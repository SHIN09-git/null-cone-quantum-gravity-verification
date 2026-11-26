# 径向模式级数与三阶系数

式 (4.33) 的标量模式和在每个实数 $x$ 上绝对收敛。保留前 $N\ge1$ 个模式时，振幅误差至多为 $x^2/(2N)$。式 (4.34) 对同一截断振幅先求导，在 $x=0$ 得到三阶 Taylor 系数 $-iH_N$。这个系数随 $N$ 增大没有有限复极限。[原文式 (4.33)](https://arxiv.org/html/2611.34924v1#S4.E33) · [原文式 (4.34)](https://arxiv.org/html/2611.34924v1#S4.E34) · [Lean 源文件](../NullCone/Series.lean)

## 变量和物理输入

原文固定角面积、一个极化和一个实角谐波，选取式 (4.32) 的高斯制备、二次插入和相对旋转。在这些选择下，第 $k$ 个模式的方差为 $v_k=1/(2sk)$，两次收缩给出权重 $2v_k^2$，一对激发取得相位 $e^{-2ik/s}$。取 $x=1/s=4\hbar G_N/\mathscr A$，便得到本文件的出发式

$$
C_N(x)=\frac{x^2}{2}\sum_{k=1}^N\frac{e^{-2ikx}}{k^2}.
$$

Lean 的索引从 $n=0$ 开始，物理模式为 $k=n+1$。`cutoff N` 因而恰好保留 $k=1,\ldots,N$。它是从实数到复数的函数。`iteratedDeriv 3 (cutoff N) 0` 在实变量上求导，保留完整的复值结果。原文物理范围为 $s>0$。标量表达式自然延伸至所有实 $x$，包括求导点 $0$。[原文式 (4.32)](https://arxiv.org/html/2611.34924v1#S4.E32) · [既有报告的坐标空间推导](../../report/mathematics.tex)

## 声明与计算

下列声明均在命名空间 `NullCone.Series` 中。

| Lean 声明 | 已证明的数学结论 |
| --- | --- |
| `mode_norm`、`amplitude_absolute_sum` | 每项指数的模为 1。乘入公共因子后，逐项范数之和恰等于 $\pi^2 x^2/12$。 |
| `cutoff_tendsto` | 实际的有限振幅 $C_N(x)$ 收敛到级数定义的 $C(x)$。 |
| `dilogSeries_absolute`、`amplitude_eq_dilog` | 二重对数的定义幂级数在 $\lvert z\rvert\le1$ 绝对收敛，$C(x)=x^2\operatorname{Li}_2(e^{-2ix})/2$。 |
| `amplitude_tail_le` | 对所有实 $x$ 和自然数 $N\ge1$，有 $\lvert C(x)-C_N(x)\rvert\le x^2/(2N)$，含相位为 1 的点。 |
| `cutoff_cubic` | $C_N^{(3)}(0)/3!=-iH_N$，其中 $H_N=\sum_{k=1}^N1/k$。 |
| `cutoff_cubic_scaled` | 对固定实常数 $c$ 和实参数 $G$，$\frac{G^3}{3!}\left.\frac{d^3}{dg^3}C_N(cg)\right|_{g=0}=-i(cG)^3H_N$。取 $c=4\hbar/\mathscr A$、$G=G_N$ 即得原文的三阶项。 |
| `cubic_log_limit`、`cubic_diverges`、`cubic_no_finite_limit` | 三阶系数的负虚部减去 $\log N$ 后趋于欧拉常数 $\gamma$。该负虚部趋向 $+\infty$，复系数没有有限极限。 |

尾界使用 $1/(k+1)^2\le 1/k-1/(k+1)$，在 $k\ge N$ 上相加后相邻两项消去。计算三阶系数时，先对有限指数和逐项求导，再对 $x^2/2$ 使用乘积法则。$x=0$ 时只有对前因子求两次导、对指数求一次导的项保留。

## 先移除截断，再取弱耦合极限

对无穷振幅本身，`NullCone.Perturbation.amplitude_quadratic_limit` 给出双侧极限 $C(x)/x^2\to\pi^2/12$。`amplitude_im_cubic_atBot` 给出完整的右极限 $\operatorname{Im} C(x)/x^3\to-\infty$，其中包括序列 $x_N=1/(2N)$。因此减去真实二阶项后，$(C(x)-\pi^2 x^2/12)/x^3$ 没有有限的复数右极限，见 `amplitude_no_cubic_coefficient`。[无穷振幅的 Lean 证明](../NullCone/Perturbation.lean)

二阶结论使用可和的统一上界 $1/k^2$。对三阶商，取 $N=\lfloor1/(2x)\rfloor$。充分小的正 $x$ 满足 $1/4\le Nx\le1/2$，因而前 $N$ 个模式可用 $\sin(2kx)\ge kx$ 估计，虚部三阶商至多为 $-H_N/2$。剩余模式对该商的贡献至多为 2。由于 $x\downarrow0$ 时 $N\to\infty$，这就给出了右极限。精确的 $x^3\log x$ 系数和随后的有限项还需要更细的估计。

## 适用范围

本文件从给定的标量模式振幅出发。式 (4.33) 的第一步把算符关联函数化为这个标量和，其中的高斯矩、Wick 收缩和 Fock 空间中的旋转由既有报告另行推导。这里的二重对数采用闭单位圆盘上的级数定义。报告中的振荡尾界、Abel 与三角截断，以及移除截断后 $C(x)$ 在 $x\downarrow0$ 的对数展开，均需独立论证。[既有报告](../../report/mathematics.tex)
