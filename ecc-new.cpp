#include <iostream>
#include <cstdint>
#include <random>
#include <chrono>
#include <tuple>

using namespace std;

/* ============================================================
 * 1. 有限域参数
 *    p = 2^31 - 1 是真正的梅森素数
 *    允许用 (x & p) + (x >> 31) 做快速模约简
 * ============================================================ */
static const uint32_t P = 2147483647;

/* ============================================================
 * 2. Montgomery 曲线参数
 *    曲线形式: y^2 = x^3 + A x^2 + x
 *
 *    A24 = (A + 2) / 4
 *    是 Montgomery ladder 中的优化常量
 * ============================================================ */
static const uint32_t A = 6;
static const uint32_t A24 = (A + 2) / 4;

/* ============================================================
 * 3. 有限域模运算
 * ============================================================ */

// (a + b) mod p
inline uint32_t mod_add(uint32_t a, uint32_t b) {
    uint32_t r = a + b;
    if (r >= P) r -= P;
    return r;
}

// (a - b) mod p
inline uint32_t mod_sub(uint32_t a, uint32_t b) {
    return (a >= b) ? (a - b) : (P - (b - a));
}

// (a * b) mod p
// 使用梅森素数的快速约简
inline uint32_t mod_mul(uint64_t a, uint64_t b) {
    uint64_t r = a * b;
    r = (r & P) + (r >> 31);
    if (r >= P) r -= P;
    return (uint32_t)r;
}

/* ============================================================
 * 4. 模逆 (a^-1 mod p)
 *    扩展欧几里得算法
 *    注意：整个 ECDH 过程中只在最后用一次
 * ============================================================ */
uint32_t mod_inv(uint32_t a) {
    int64_t t = 0, newt = 1;
    int64_t r = P, newr = a;

    while (newr) {
        int64_t q = r / newr;
        tie(t, newt) = make_pair(newt, t - q * newt);
        tie(r, newr) = make_pair(newr, r - q * newr);
    }

    if (t < 0) t += P;
    return (uint32_t)t;
}

/* ============================================================
 * 5. xZ 投影坐标
 *
 *    仿射坐标: x = X / Z
 *    好处:
 *      - 避免每一步做模逆
 *      - Montgomery ladder 的标准表示
 * ============================================================ */
struct XZ {
    uint32_t X;
    uint32_t Z;
};

/* ============================================================
 * 6. 条件交换 (constant-time)
 *
 *    s = 0 -> 不交换
 *    s = 1 -> 交换
 *
 *    用于 Montgomery ladder 防止侧信道攻击
 * ============================================================ */
inline void cswap(uint32_t s, XZ &a, XZ &b) {
    uint32_t mask = -s;
    uint32_t t;

    t = mask & (a.X ^ b.X); a.X ^= t; b.X ^= t;
    t = mask & (a.Z ^ b.Z); a.Z ^= t; b.Z ^= t;
}

/* ============================================================
 * 7. Montgomery ladder
 *
 *    输入:
 *      k  : 标量 (私钥)
 *      x1 : 基点的 x 坐标
 *
 *    输出:
 *      k * (x1, y1) 的 xZ 表示
 *
 *    特点:
 *      - 每一轮: 1 次加 + 1 次倍
 *      - 与 k 的比特无关 → 抗侧信道
 * ============================================================ */
XZ ladder(uint32_t k, uint32_t x1) {
    XZ R0{1, 0};     // 无穷远点
    XZ R1{x1, 1};   // 基点
    uint32_t swap = 0;

    for (int i = 30; i >= 0; --i) {
        uint32_t bit = (k >> i) & 1;
        swap ^= bit;
        cswap(swap, R0, R1);
        swap = bit;

        // 差分加公式
        uint32_t A_ = mod_add(R0.X, R0.Z);
        uint32_t B_ = mod_sub(R0.X, R0.Z);
        uint32_t C_ = mod_add(R1.X, R1.Z);
        uint32_t D_ = mod_sub(R1.X, R1.Z);

        uint32_t DA = mod_mul(D_, A_);
        uint32_t CB = mod_mul(C_, B_);

        uint32_t X5 = mod_mul(mod_add(DA, CB), mod_add(DA, CB));
        uint32_t Z5 = mod_mul(x1, mod_mul(mod_sub(DA, CB), mod_sub(DA, CB)));

        // 倍点公式
        uint32_t AA = mod_mul(A_, A_);
        uint32_t BB = mod_mul(B_, B_);
        uint32_t E  = mod_sub(AA, BB);

        uint32_t X4 = mod_mul(AA, BB);
        uint32_t Z4 = mod_mul(E, mod_add(BB, mod_mul(A24, E)));

        R1 = {X5, Z5};
        R0 = {X4, Z4};
    }

    cswap(swap, R0, R1);
    return R0;
}

/* ============================================================
 * 8. 主函数：Montgomery ECDH
 * ============================================================ */
int main() {
    uint32_t base_x = 5;  // 选定的 Montgomery 基点 x 坐标

    // 真随机 + 时间扰动
    mt19937 gen(
        (uint32_t)chrono::high_resolution_clock::now()
            .time_since_epoch().count() ^ random_device{}()
    );

    uniform_int_distribution<uint32_t> dis(1, P - 1);

    // Alice / Bob 私钥
    uint32_t a = dis(gen);
    uint32_t b = dis(gen);

    // 公钥 = 私钥 * 基点
    XZ A_pub = ladder(a, base_x);
    XZ B_pub = ladder(b, base_x);

    // 转换为仿射 x 坐标
    uint32_t A_x = mod_mul(A_pub.X, mod_inv(A_pub.Z));
    uint32_t B_x = mod_mul(B_pub.X, mod_inv(B_pub.Z));

    // 共享密钥
    uint32_t A_shared = mod_mul(
        ladder(a, B_x).X,
        mod_inv(ladder(a, B_x).Z)
    );

    uint32_t B_shared = mod_mul(
        ladder(b, A_x).X,
        mod_inv(ladder(b, A_x).Z)
    );

    cout << "Alice shared: " << A_shared << endl;
    cout << "Bob   shared: " << B_shared << endl;

    cout << (A_shared == B_shared ? "ECDH success" : "ECDH failed") << endl;
}
