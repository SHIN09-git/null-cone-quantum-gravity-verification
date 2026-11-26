# 复 Hilbert 空间上的开边界求和与闭合迹

设完备复 Hilbert 空间为 $H$，有界线性算符为 $W:H\to H$。若存在与截断无关的 $c>0$，使算符序满足 $cI\le W$，则通常正迹有限当且仅当 $H$ 有限维。对同一个无限维空间，固定两个外态的开边界矩阵元仍可绝对收敛。Lean 证明覆盖任意 Hilbert 基的指标集，包括不可数指标集。[Lean 实现](../NullCone/Trace.lean) · [v0.2 复核第 1 节](../../phase2/RECHECK.md)

## 正迹的定义与有限维结论

对每个自然数 $n$ 和正交归一族 $e_1,\ldots,e_n$，令

$$
T(W,e)=\sum_{i=1}^{n}\operatorname{Re}\langle e_i,We_i\rangle,
\qquad \operatorname{Tr}_+(W)=\sup_{n,e}T(W,e).
$$

`positiveTrace` 在扩展非负实数 $[0,+\infty]$ 中取上确界。实现用 `ENNReal.ofReal` 嵌入有限和，对正算符每项都非负。若 $V$ 是 $e$ 张成的子空间，$P_V$ 是正交投影，`cutWeight_eq_trace_compression` 从 Mathlib 的普通有限维迹得到 $T(W,e)=\operatorname{Re}\operatorname{Tr}_{V}(P_V W|_{V})$。特别地，同一 $V$ 的任何正交归一基给出相同的数。对 $W=C^*C$，`cutWeight_adjoint_comp_self` 另外给出 $T(W,e)=\sum_i\|Ce_i\|^2$。[算符定义与证明](../NullCone/Trace.lean)

1. 若 $cI\le W$，每个单位向量的对角元实部至少为 $c$。`cutWeight_ge_rank` 求和得到 $T(W,e)\ge cn$。
2. 若 $H$ 的一个正交归一族有无限个元素，对每个 $n$ 都可在其中取 $n$ 个不同向量。因而 $\operatorname{Tr}_+(W)\ge cn$ 对所有 $n$ 成立。若这个迹有限，选 $n>\operatorname{Tr}_+(W)/c$ 就得矛盾。`finiteDimensional_of_positiveTrace_ne_top` 将此论证应用于完整 Hilbert 基。若基只有有限个向量，它同时也是代数基，故 $H$ 有限维。
3. 反过来，在有限维 $H$ 中把任意正交归一族补成基。正性保证补入的对角元均非负，而完整基给出的和正是有限维迹。`positiveTrace_eq_trace` 证明上确界等于这个迹，`positiveTrace_ne_top_iff_finiteDimensional` 合并两个方向。[完整定理](../NullCone/Trace.lean)

## 开边界公式与恒等算符

对任意 Hilbert 基 $b_i$ 和固定向量 $x,y\in H$，`open_matrix_elements` 同时证明

$$
\sum_i\langle y,b_i\rangle\langle b_i,x\rangle=\langle y,x\rangle,\qquad
\sum_i\big|\langle y,b_i\rangle\langle b_i,x\rangle\big|\le\|y\|\,\|x\|.
$$

第一个和按所有有限指标子集的包含关系取极限，第二个和在实数中收敛。取 $H=\ell^2(\mathbb N,\mathbb C)$、$W=I$ 和坐标基，每个闭合对角元都等于 1。`l2_open_and_closed` 在同一空间上同时给出所有固定外态的开边界绝对收敛以及 $\operatorname{Tr}_+(I)=+\infty$。这正是 v0.2 用于检验（4.29）与（5.38）之间推论的算符例子。[开边界与恒等算符的定理](../NullCone/Trace.lean) · [v0.2 对最后一个切面的推导](../../phase2/DERIVATION.md)

## 有符号闭合值与截断秩

固定 $c,\delta>0$。在每个截断上，令秩为 $r$，权重为 $T$，实归一响应为 $D$，并采用同一截断的 $Z=T(D-\delta/2)$。当 $T\ge cr$ 且 $|D|\le\delta/4$ 时，先由 $T\ge0$ 得 $Z\le-\delta T/4$，再由 $-\delta/4<0$ 得

$$
 Z\le -\frac{c\delta}{4}r.
$$

`signedClosure_le_neg_rank` 从上述两个估计导出此界。`signedCut_le_neg_rank` 用有界算符 $W\ge cI$ 的实际对角和作 $T$，由此在证明中导出 $T\ge cr$。对截断标签及其极限，程序分别处理以下三种条件。[有符号闭合证明](../NullCone/Trace.lean)

| 已知的截断条件 | 结论 | Lean 定理 |
| --- | --- | --- |
| 权重和响应估计对所有截断成立，同一个实数 $L$ 满足所有 $Z\ge L$ | 每个秩都满足 $r\le -4L/(c\delta)$。只要所有秩的集合无界，统一下界就不存在。 | `rank_bound_of_signed_lower`、`signedClosure_no_uniform_lower` |
| 两个估计最终成立，任何尾部中都能找到任意大的秩 | 对每个实数 $a$，$Z$ 都不能趋于 $a$。若趋于 $a$，某个尾部将满足 $Z>a-1$，与该尾部中任意大的秩矛盾。 | `signedClosure_no_finite_limit` |
| 两个估计最终成立，且秩趋于正无穷 | $Z\to-\infty$。 | `signedClosure_tendsto_atBot` |

原文（D.24）、（D.25）讨论如何在给定几何和响应参数下选取满足 $|D|\le\delta/4$ 的截断族。Lean 的有符号定理以该估计为输入。将结果用于（5.38），还要独立证明同一个未归一化插入沿这族截断有统一有限下界或趋于有限标量。另一个截断族的有限值、固定外态的绝对收敛、归一化响应本身的有限性都不能提供这项前提。[v0.2 对切面等价的判定](../../phase2/RECHECK.md) · [逐式依赖](../../phase2/CLAIMS.md)

## 从同一族有符号闭合推出有限维

`finiteDimensional_of_cofinal_small_cuts` 的结论直接是 `FiniteDimensional ℂ H`。它要求对 $H$ 内每个含 $n$ 个向量的有限正交归一族，能在给定的截断族中选到同一空间上的一个截断，其秩至少为 $n$，且 $|D|\le\delta/4$。若这些小响应截断的 $Z$ 有统一有限下界 $L$，那么上一节的负界使每个选中截断的秩至多为 $-4L/(c\delta)$。假设 $H$ 无限维，从完整 Hilbert 基中选出的正交归一族可有任意多向量，必然超过此上界。条件只比较维数。原文的完整循环覆盖有限个基标签，足以给出所需的秩。[有限维定理](../NullCone/Dimension.lean) · [v1 附录 D.2](https://arxiv.org/pdf/2611.34924v1#page=72)

窄带版本明确列出几何输入。记 $K=|\eta|\|O\|/\pi$、$A=s_*$、$q_P=\operatorname{Tr}[\rho_P(\hat s-s_0)^2]$。给定 $c,\delta>0$ 和 $K\ge0$，`exists_narrow_band_parameters` 先选 $\varepsilon=\delta/[8(K+1)]$，再取整数 $m>\max\{1,A^2/(c\varepsilon^2)\}$。于是 $q_P\le\varepsilon^2+A^2/(mc)$ 保证 $K\sqrt{q_P}\le\delta/4$。在这组参数确定后，`finiteDimensional_of_narrow_band_cuts` 使用（5.32）形式的响应界 $|D_P|\le K\sqrt{q_P}$。它把（D.25）的几何估计列为独立条件，要求在无限维假设下，这个固定截断族能在任意大的秩上实现上述面积二阶矩界。由该族的小响应闭合值的统一下界得到有限维。[窄带参数与充分条件](../NullCone/Dimension.lean) · [v1（5.32）](https://arxiv.org/html/2611.34924v1#S5.E32) · [v1（D.25）](https://arxiv.org/html/2611.34924v1#A4.E25)

若输入是沿给定截断网的有限极限 $a$，则 $Z_P>a-1$ 最终成立。`finiteDimensional_of_cofinal_small_cuts_limit` 与 `finiteDimensional_of_narrow_band_limit` 要求每个尾部都能找到同时满足秩要求和响应估计或二阶矩估计的截断。这样有限极限提供的下界与负的秩界落在同一个截断上。将这两个定理用于四维菱形，需为同一几何、同一插入、同一去截断过程验证其输入。[有限极限版本](../NullCone/Dimension.lean)

## 在无限维窄带中构造截断

给定旧截断的有限维值域 $E$ 和无限维窄带子空间 $V$，把 $E$ 的正交投影限制在 $V$ 上。像的维数至多为 $\dim E$，故其核必为无限维，否则核与商空间都有限维，$V$ 也会有限维。这个核里的向量同时属于 $V$ 和 $E^\perp$。`exists_band_extension` 从核的代数基中选 $n$ 个向量，施行 Gram–Schmidt 正交归一化。把它们接在 $E$ 的正交归一基之后，得到真实的截断子空间 $P\supset E$，秩为 $\dim E+n$。若有限个带共同张成的子空间稠密，`exists_infinite_band` 证明无限维 $H$ 中至少一带必须是无限维。[构造与秩等式](../NullCone/Dilution.lean)

令 $Q_{\rm out}$ 为投到 $V^\perp$ 的正交投影。每个新增向量对 $\sum_i\|Q_{\rm out}e_i\|^2$ 的贡献为零，每个旧单位向量的贡献至多为 1。此和是 $Q_{\rm out}$ 在 $P$ 上的普通压缩迹，故换基后仍至多为 $\dim E$。对非零截断，带外比例至多为 $\dim E/\dim P$。[带外迹与换基证明](../NullCone/Dilution.lean)

写 $W_P=P W|_P$。给定 $cI\le W\le I$，`compressed_weight_eigenbasis` 构造 $W_P$ 的正交归一本征基 $u_i$，并证明每个本征值满足 $c\le\lambda_i\le1$。设 $S=\hat s-s_0$ 自伴，闭子空间 $V$ 在 $S$ 下不变，$\|S|_V\|\le\varepsilon$ 且 $\|S\|\le A$。此时 $V^\perp$ 也不变。将单位向量分成两个正交分量后，得到 $\|Sx\|^2\le\varepsilon^2+A^2\|Q_{\rm out}x\|^2$。记 $R=S|_P:P\to H$，在上述本征基上直接计算有限迹得到

$$
\frac{\operatorname{Re}\operatorname{Tr}_{P}(R^*R W_P)}
     {\operatorname{Re}\operatorname{Tr}_{P}(W_P)}
=\frac{\sum_i\lambda_i\|S u_i\|^2}{\sum_i\lambda_i}
\le\varepsilon^2+\frac{A^2\dim E}{c\,\dim P}.
$$

这里允许 $P$ 与 $W$ 或 $S$ 不对易。给定目标秩 $N$ 和正整数 $m$，`exists_high_rank_operator_cut` 选择足够多的新向量，使同一个 $P$ 既含 $E$、秩至少为 $N$，又使右端至多为 $\varepsilon^2+A^2/(mc)$。这一步从窄带和算符的性质导出高秩小矩截断。[算符二阶矩与定量截断](../NullCone/Dilution.lean) · [v1（D.24、D.25）](https://arxiv.org/pdf/2611.34924v1#page=72)

`finiteDimensional_of_band_cover_and_closing` 进一步去掉了选择高秩小响应截断的前提。它使用上述有限带覆盖、响应与二阶矩的关系。闭合条件另行要求存在某个旧有限截断 $E$ 和实数 $L$，使所有包含 $E$ 且满足小响应界的非零有限截断都有 $Z_P\ge L$。在无限维假设下，上述构造给出任意高秩的这种截断，与负秩界矛盾。这个闭合条件适用于任意符合条件的扩充。若物理闭合只对预先选好的整循环网给出有限数，上一节的逐网定理还要求在该网自身的尾部找到所需截断。[有限维定理的完整签名](../NullCone/Dilution.lean) · [v0.2 对截断族的判定](../../phase2/RECHECK.md)

## 复核方式

在 `phase3` 目录运行 `lake build NullCone.Dilution` 可连同依赖检查这三个模块。此次复核使用 Lean 4.24.0 和 Mathlib 提交 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。构建成功。`Trace.lean`、`Dimension.lean`、`Dilution.lean` 分别对 16、6、12 条公开定理执行 `#print axioms`，每条定理均只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。[版本锁定文件](../lake-manifest.json)
