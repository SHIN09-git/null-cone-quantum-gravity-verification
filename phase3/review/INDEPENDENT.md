# v0.3.0 声明与原命题的独立核对

五条截断在同一无限维复 Hilbert 空间上强趋于恒等，给同一个有界插入的未归一化矩阵元带来五个不同极限。其中一条在每个截断上都等于同一个正有限参考值。因此，只给固定外态的开放拼接和一个选定截断的正有限值，无法推出维数有限。要判定四维引力的结论，还需几何原则将同一截断族与未切振幅联系起来。[全模型定理](../NullCone/Counterexample.lean) · [五个极限](../NullCone/Limits.lean) · [v0.2 原命题](../../phase2/RECHECK.md)

我在阅读本轮 Lean 文件之前，按 v0.2.0 的两份复核及标量幅度推导写下判据。下文核对的是实际定理中的空间、截断族、输入条件及结论。我随后补写了 `HilbertSchmidt.lean` 和 `Functional.lean`。这两个模块由其他复核者交叉核验。[预先判据](BLIND.md) · [逐式推导](../../phase2/DERIVATION.md) · [标量模式原推导](../../report/mathematics.tex)

## 双边界态和五条极限

1. 单侧标签 $B=\mathbb N\sqcup\mathbb N$。双侧使用完整的 $\ell^2(B\times B,\mathbb C)$，包括两个标签不同的坐标。有限制备的每一项满足 $v_P(i,j)=\langle e_i,CP e_j\rangle$。两条腿的交换由两个标签同时置换给出，右侧提升只改变第二标签的相位。交换插入自伴，右侧提升满射且保范数。面积算符的两个本征值为 1 和 3。对该算符使用谱演算，得到 $C=\sqrt w I$、$C^*C=wI$，其中 $w=e^{-3}$。相位去掉共同因子后分别为 1 和 $e^{i}$，归一化参考态的响应为 $\delta=1-\cos 1>0$。[空间与算符](../NullCone/Model.lean) · [正交投影、伴随与插入](../NullCone/Projections.lean) · [高斯谱演算](../NullCone/Area.lean) · [参考态](../NullCone/Amplitude.lean)
2. `signed_is_matrix_element` 给出 $Z_P=\operatorname{Re}\langle v_P,Xv_P\rangle$，其中 $X=U^*OU-O-\delta I/2$ 是一个固定算符。对 $r\ge n$，计算该矩阵元得到 $Z_P=w\delta(3n-r)/2$。实际单位向量的响应为 $2n\delta/(r+n)$，条件 $r+n>0$ 正好排除零向量。交叉交换项来自同时纳入的 $n$ 对标签。[矩阵元和质量的推导](../NullCone/Amplitude.lean) · [插入定义](../NullCone/Projections.lean)
3. 每个投影幂等、自伴且像的维数等于有限标签集的大小。五族均递增，而且最终包含任意给定的有限标签集。由 Hilbert 空间中的基展开，对每个固定 $x\in\ell^2(B)$ 均有 $\|P_kx-x\|\to0$。证明覆盖所有固定外态。此处有向集是有限标签集按包含关系排序。[投影的有限秩](../NullCone/Projections.lean) · [范数收敛](../NullCone/Hilbert.lean) · [五族的共尾性](../NullCone/Cutoffs.lean)

程序从 $k=0$ 开始计数，原文的 $n=k+1$。表中的五种结果由同一个 $Z_P$ 得出。[极限定理](../NullCone/Limits.lean)

| $a$ 标签数 $r$ | 每一步的 $Z_P/(w\delta)$ | $Z_P$ 的极限 |
| --- | ---: | --- |
| $n$ | $n$ | $+\infty$ |
| $3n-2$ | $1$ | $w\delta$ |
| $3n$ | $0$ | $0$ |
| $3n+2$ | $-1$ | $-w\delta$ |
| $7n$ | $-2n$ | $-\infty$ |

正有限那一列在每一步都等于只取第一对标签时的未归一化值，它的归一化响应却趋于 $\delta/2$。假如所有有限标签集的网有同一个实数极限，该极限也必须同时等于 $0$ 和 $w\delta>0$。`no_finite_cut_net_limit` 明确排除了这种可能。另以这些公开声明作输入，直接把五条极限改写成 $\operatorname{Re}\langle v_P,Xv_P\rangle$ 的极限，并将强收敛改写为 $\|P_kx-x\|\to0$，在 Lean 4.24.0 的警告即报错设置下均可编译。[全网结论](../NullCone/Limits.lean) · [正有限路径的归一化极限](../NullCone/Counterexample.lean) · [可重编译的独立用例](Regression.lean)

## 一般迹、开边界和三阶系数

`positiveTrace` 取全体有限正交归一族的对角和在 $[0,+\infty]$ 中的上确界。对正算符，这就是普通扩展正迹。有限维时与代数迹相符，每个有限切面的权重也等于压缩至切面后的普通有限维迹。在固定的 $W\ge cI$、$c>0$ 下，这个迹有限与 $H$ 有限维等价。证明允许不可数 Hilbert 基。固定外态的开放矩阵元则有绝对和上界 $\|x\|\|y\|$。在 $\ell^2(\mathbb N)$ 上取恒等算符即可同时验证开放公式和无限闭合迹。[一般正迹与固定外态展开](../NullCone/Trace.lean)

在我补写的模块中，对任意有界 $C:H\to K$，$\operatorname{Tr}_+(C^*C)=\sum_i\|Ce_i\|^2$ 在扩展非负实数中成立，值与完整基的选取无关。该迹有限，当且仅当全部矩阵元 $\langle d_j,Ce_i\rangle$ 组成 $\ell^2(\kappa\times\iota)$ 中的向量。平方范数等于该迹。若需要单位向量，还需 $C\ne0$。这里选择了完备 Hilbert 张量积的乘积基坐标表示。使用无坐标张量积对象及其自然等距同构是另一个表述层次。另一位复核者单独编译了八条公开定理，并检验了零算符和恒等算符。[Hilbert–Schmidt 模块](../NullCone/HilbertSchmidt.lean) · [交叉核验记录](HS_CROSSCHECK.md)

模式部分直接微分硬截断的复值函数 $C_N(x)=x^2\sum_{k=1}^N e^{-2ikx}/(2k^2)$。三次对实参数求导并除以 $3!$，所得确为 $-iH_N$。负虚部趋于正无穷，减 $\log N$ 后趋于欧拉常数。检验还覆盖同一振幅的绝对和 $\pi^2x^2/12$、$N\ge1$ 时的截断误差 $x^2/(2N)$ 和 $x=cG$ 时的三阶项。我用公开定理另行恢复了未除以 $3!$ 的导数 $-6iH_N$。这些结论的起点是给定的标量模式式。v0.2 的振子态构造、Abel 截断和三角截断各有独立的证明任务。[模式与导数](../NullCone/Series.lean) · [原文及适用范围](SERIES.md)

对先移除截断的实际函数 $C(x)$，另一个模块证明 $C(x)/x^2\to\pi^2/12$。取 $N=\lfloor1/(2x)\rfloor$，前 $N$ 项的正弦满足同号下界，尾部对虚部三阶差商的贡献有统一上界。因此在整个右邻域上 $\operatorname{Im}C(x)/x^3\to-\infty$。减去已确定的二阶项后，复差商不可能趋于有限数。这里验证了发散的方向和适用区间，v0.2 中的精确对数系数、常数和实部三阶项仍需更细的计算。以 $x_n=1/(n+1)$ 取样，独立用例还检查了减去二阶项后的复差商虚部确实趋于负无穷。[去截断后的实际振幅](../NullCone/Perturbation.lean) · [独立用例](Regression.lean)

## 有限维充分条件中的几何输入

- 在任何有界算符 $O$ 和两个单位向量上，期望差由 $2\|O\|\|u-v\|$ 控制。对于右侧面积可用本征标签表示的模型，程序将面积平方偏差与实际双侧态的右侧提升连接，得到系数 $|\eta|/\pi$。它允许任意两标签的相关性，且要求该态的二阶矩可和。`integrated_phase_square_le` 还适用于任意具有所需二阶矩的实轴测度。把某个连续谱面积算符的特定期望表达为该测度的积分，需要相应的谱定理识别。[响应与面积矩](../NullCone/Response.lean)
- 一旦给定无限维窄带子空间 $V$ 及任意有限维起始切面 $E$，程序可以在 $V\cap E^\perp$ 中加入任意 $n$ 个正交归一向量。新切面 $P$ 包含整个 $E$，秩恰为 $\dim E+n$。带外投影在 $P$ 上的压缩迹至多为 $\dim E$。进一步取 $cI\le W\le I$，以及在 $V$ 内范数至多为 $\varepsilon$、在全空间有界的对称面积偏差算符 $S$。只要 $V$ 对 $S$ 不变，$V^\perp$ 也对 $S$ 不变。程序在压缩权重 $W_P$ 的本征基中计算 $\operatorname{Re}\operatorname{Tr}[(S|_P)^*(S|_P)W_P]/\operatorname{Re}\operatorname{Tr}W_P$。它保留 $S|_P:P\to H$，因此计入了离开切面的分量。由此可把上界压到 $\varepsilon^2+A^2/(mc)$，同时达到指定的秩，其中 $A\ge\|S\|$。这里允许 $P$ 与 $W$、$S$ 均不对易。[窄带扩充与实际压缩迹](../NullCone/Dilution.lean)
- 小响应 $|D_P|\le\delta/4$ 及 $W\ge cI$ 给出 $Z_P\le -(c\delta/4)\operatorname{rank}P$。若改用任意有限极限排除无限维，高秩的小响应截断必须进入同一滤子的每个尾部。一般维数定理将高秩矩估计列作假设。更强的 `finiteDimensional_of_band_cover_and_closing` 从有限个闭不变子空间的稠密覆盖、各带内的算符界及同一个响应的矩估计出发，在假设无限维后亲自构造所需的高秩切面。它仍要求给定一个固定的起始切面 $E$，在包含 $E$ 且满足小响应条件的所有有限切面上，闭合值有统一有限下界。这项闭合输入及四维谱带的物理识别需要独立论证。[秩与滤子条件](../NullCone/Trace.lean) · [一般维数定理](../NullCone/Dimension.lean) · [从不变谱带覆盖推出有限维](../NullCone/Dilution.lean)
- 我补写的另一条条件对同一 $B(H)$ 上的有限正线性泛函 $\zeta$ 作检验。它在所有有限秩正交投影上的取值须等于 $W$ 的几何权重。利用补投影的正性，可得 $\operatorname{Tr}_+(W)\le\operatorname{Re}\zeta(I)$。再加 $W\ge cI$、$c>0$，即可推出 $H$ 有限维。这里使用的投影是所给有限正交归一族张成空间的实际正交投影。泛函无需满足迹性。[有限正泛函](../NullCone/Functional.lean) · [独立交叉核验](HS_CROSSCHECK.md#全算符代数上的有限正泛函)

v0.2 另有一条从完整 $B(H)$ 上非零有限正迹推出有限维的论证，它甚至允许非正规迹。该论证用到无限维 Hilbert 空间的两份正交等距副本，本次工程中的几何权重泛函定理未形式化这条单独的途径。四维局域剪切代数、精确路径积分与换切面的统一极限也仍属于物理输入。上面的反模型定位的是开放矩阵元与最后一次自由指标闭合之间的推理条件。[v0.2 独立复核](../../phase2/RECHECK.md) · [§5.2 与附录 E 的比较](../../phase2/DERIVATION.md)

此外，我分别用 `lake env lean -DwarningAsError=true` 重编了窄带扩充模块、去截断后的弱耦合模块和六项独立用例。三次命令均退出 0。输出的 12 条窄带定理、4 条弱耦合定理和 6 项独立用例，其公理依赖只有 `propext`、`Classical.choice` 和 `Quot.sound`。[窄带扩充](../NullCone/Dilution.lean) · [弱耦合](../NullCone/Perturbation.lean) · [独立用例](Regression.lean)

