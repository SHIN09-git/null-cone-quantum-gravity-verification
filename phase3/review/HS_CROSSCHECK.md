# Hilbert–Schmidt 条件与双边界系数的交叉核验

对任意完备复 Hilbert 空间 $H,K$ 和有界准备算符 $C:H\to K$，8 条公开定理共同给出以下结论。在输入和输出的完整正交归一基上，$C$ 的全部矩阵元组成有限范数向量，当且仅当 $C^*C$ 的普通正迹有限。若还知道 $C^*C\ge cI$ 且 $c>0$，该向量存在又与 $H$ 有限维等价。结论适用于不可数基。[受检代码](../NullCone/HilbertSchmidt.lean) · [正迹的独立定义](../NullCone/Trace.lean) · [v0.2 复核第 1 节](../../phase2/RECHECK.md)

## 原文中的系数

v1 的（D.22）取有限投影 $P$，把 $C_b b_i$ 与共轭副本的 $\bar b_i$ 配对，再用 $\sqrt{\operatorname{Tr}(PC_b^*C_b)}$ 归一。以 $d_j$ 表示输出基时，分子的乘积基系数恰为 $\langle d_j,C_b b_i\rangle$，其中 $i$ 在本次截断内。没有纳入的列为零。这与（5.31）分母中 $\sum_i\|C_b b_i\|^2$ 一致。程序的 `HasMatrixVector` 在 $\ell^2(\kappa\times\iota,\mathbb C)$ 中要求每个 $(j,i)$ 坐标都等于同一 $C$ 的这个矩阵元。[v1（D.22）](https://arxiv.org/html/2611.34924v1#A4.E22) · [v1（5.31）](https://arxiv.org/html/2611.34924v1#S5.E31)

| 公开定理 | 核对结果 |
| --- | --- |
| `column_sum_basis_independent`、`positiveTrace_gram_eq_column_sum` | 前者用伴随、Parseval 等式和非负级数换序，证明任意两组完整输入基的列范数平方和相等。后者把任一有限正交族补成 Hilbert 基，又用一组完整基的全部有限子和逼近扩展和，证明此和恰为普通正迹。相等的两端都允许 $+\infty$。 |
| `finite_trace_iff_hilbertSchmidt`、`positiveTrace_gram_eq_matrix_sum` | 普通迹有限等价于实际列平方范数在实数中可和。输出基的 Parseval 等式进一步给出矩阵全部指标的非负双重和，允许换序。 |
| `finite_trace_iff_matrix_vector`、`positiveTrace_eq_vector_norm_sq` | 程序从可和性构造 $\ell^2$ 元素，并证明任何具有指定全部坐标的 $v$ 都满足 $\operatorname{Tr}_+(C^*C)=\|v\|^2$。 |
| `finiteDimensional_iff_matrix_vector_of_lower`、`normalized_matrix_iff` | 前者使用整个 $H$ 上的严格标量下界。后者只在 $C\ne0$ 且迹有限时给出单位向量 $u$ 和正数 $r$，使 $r u$ 的每个坐标恢复原矩阵元。 |

物理应用中需辨明两处识别。首先，证明使用完整乘积基的 Hilbert 空间坐标。要以无坐标的完备张量积陈述同一结果，需使用 $K\widehat\otimes\bar H$ 与上述坐标空间的等距同构。其次，把另一切面制备的有限范数态识别为这里的 $v$，须证明两者对同一 $C_b$ 的所有矩阵元相符。原文（D.22）给出有限截断的态，（5.30c）提供固定几何的算符下界；对四维未切制备的识别仍需独立的闭合论证。[v1（5.30c）](https://arxiv.org/html/2611.34924v1#S5.E30.3) · [v1（5.38）](https://arxiv.org/html/2611.34924v1#S5.E38)

## 全算符代数上的有限正泛函

另行核对了 `Functional.lean` 对 v0.2 复核第 2 节第一条充分条件的表述。$\zeta:B(H)\to\mathbb C$ 是正的复线性泛函，定义域包含单位。`cutProjection` 构造到指定有限族张成空间的正交投影 $P$。正性给出 $\zeta(I-P)\ge0$。若对每个有限正交归一族都已知 $\operatorname{Re}\zeta(P)=T(W,e)$，取上确界便得 $\operatorname{Tr}_+(W)\le\operatorname{Re}\zeta(I)<\infty$。最后加上 $W\ge cI$、$c>0$ 才得到有限维。这里无须假设 $\zeta(AB)=\zeta(BA)$。例如无限维空间中的归一化向量态在单位上取值 1，却在投到与该向量正交的一维子空间时取值 0，不能复现 $W=I$ 的权重 1。[泛函及 3 条定理](../NullCone/Functional.lean) · [v0.2 复核第 2 节](../../phase2/RECHECK.md)

## 复算

另外用公开接口在 $H=K=\ell^2(\mathbb N,\mathbb C)$ 上编译了三个特例。零算符有矩阵向量 $v=0$，却无法把它归一化。恒等算符的固定外态开边界矩阵元绝对收敛，但其全矩阵没有有限范数向量，因为对角线上有无穷多个 1。三个检查在开启警告即报错的环境中通过。[恒等算符的正迹](../NullCone/Trace.lean) · [矩阵向量与归一化条件](../NullCone/HilbertSchmidt.lean)

在 `phase3` 目录单独执行 `lake env lean -DwarningAsError=true NullCone/HilbertSchmidt.lean`。另以同一参数重编 `NullCone/Functional.lean`。两个模块的 8 条和 3 条公开定理分别通过检查，各自的 `#print axioms` 均输出 `propext`、`Classical.choice`、`Quot.sound`。对照的原文 `main.tex` 及 v1 PDF 的 SHA-256 与项目锁定值一致。[原件记录](../../reference/phase2.json) · [Lean 版本](../lean-toolchain)
