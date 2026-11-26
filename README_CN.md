# 光锥量子引力独立核验

[English README](README.md) · [v0.2.0 发布页](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/releases/tag/v0.2.0) · [研究对象 arXiv:2611.34924v1](https://arxiv.org/abs/2611.34924v1)

## 第二阶段 · 最后一条边界闭合时，振幅之和是否收敛

式（4.29）固定了初态和末态。第 43 页在（5.38）后用它闭合最后一条边界，此时还要让每个允许态与自己配对，再把所有配对的振幅相加，即求迹。（5.30c）给每个正交态的正权重一个共同下界。重新审读正文六章和附录 A–E，我们核实了有限截断的估计，也找到几种足以证明有限维的明确条件。v1 是否独立证明作者选定的截断能回到同一个有限未切振幅，仍然存疑。四维物理态空间的维数尚未确定。[面向大学物理读者的报告](phase2/REPORT_CN.md) · [英文技术说明](phase2/report/report.pdf)

| 结论 | 证据与范围 |
|---|---|
| **条件性成立** | 只要独立证明同一个有符号插入沿原文那一族截断有有限极限，有限维就能推出。该极限的符号无需预设。[逐式推导](phase2/DERIVATION.md) |
| **发现反例** | 同一两面积模型的一种截断始终给出同一正有限值，另一种趋于负无穷，两组都纳入每个基态。反例针对从开放拼接推到闭合的数学命题；完整四维引力动力学仍待实现。[模型前提](phase2/COUNTERMODEL.md) · [五种截断的精确结果](phase2/RECHECK.md) |
| **存疑** | 附录 D.3 得到正的一圈鞍点比值；它与（D.47）精确全态比值的等同仍待证明。附录 E.3 的引力实例回引（5.39c），倒用这一步会形成循环。[命题依赖](phase2/CLAIMS.md) · [显式前提](phase2/ASSUMPTIONS.md) |
| **严格验证** | （5.44）联合求和的绝对总权重等于 $2p(1-p)Z_\beta$。总热迹有限非零时，（5.66）的窗代价按热权取平均恰好为 $1/2$；个别窄窗仍可能代价无界。[全篇复核推导](phase2/RECHECK.md) |

OpenAI Codex 完成推导、程序和报告，独立 AI 上下文进行了反审。项目记录中尚无外部专家评审或人工逐式核验的签署。第二阶段公开 14 项测试、96 行高精度记录，以及每步的命令、标准输出、错误输出与哈希。[逐式判定](phase2/FINDINGS.md) · [复现说明与基准数据](phase2/REPRODUCIBILITY.md)

在仓库根目录，使用已安装锁定依赖的 Python 执行下列命令。输出目录须为新目录。

~~~sh
python -B reproduce.py --phase 2 --out ../null-cone-phase2-run --compare
~~~

## 第一阶段 · 第 4.4 节的跃迁振幅与收敛性

[英文技术报告](report/report.pdf) · [报告的 LaTeX 源文件](report/report.tex) · [v0.1.0 发布页](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/releases/tag/v0.1.0)

第一阶段核验 Venkatesa Chandrasekaran 的论文 *An algebraic quantization of gravity from the null cone*，arXiv:2611.34924v1 第 4.4 节式（4.29）至（4.33）。在论文选定的高斯态、单个实角谐函数、单个极化和相位下，引力子对的连通振幅在每个固定正耦合处都绝对收敛。这里的“连通”指从两次插入的期望中减去两个单次期望的乘积。若先截断径向模式再按耦合展开，三阶系数随截断对数发散。[论文第 4.4 节](https://arxiv.org/html/2611.34924v1#S4.SS4)

**研究贡献与评审状态。** OpenAI Codex 完成了数学推导，编写并运行了复现程序，也起草了报告。这一版尚未经过外部专业人士审查。

| 证据等级 | 结论 |
| --- | --- |
| 严格验证 | 给定有限范数的边界态和幺正演化，（4.29）、（4.30）给出一张切面上的基展开和绝对值上界。（4.31）控制固定有限张切面上分别截断各个投影的误差。 |
| 条件性成立 | 把算符的乘积解释为拼接时空的演化，须匹配边界数据并使用演化合成律。（4.32）的高斯宽度和旋转相位由论文选定。 |
| 严格验证，限上述准备 | 写 $x=4G_N\hbar/\mathcal A=1/s$，中心化的对态给出 $C=x^2\operatorname{Li}_2(e^{-2ix})/2$。仅保留前 $N$ 个径向模式时，绝对误差至多为 $x^2/(2N)$。报告第 4、5 页给出远离共振时的更紧上界、三种截断的比较及弱耦合展开的余项界。 |
| 数值支持 | 127 条数值记录包括 85 位、125 位十进制精度下的比较。$s=10$ 时，振幅约为 $0.006703874007446236-0.002609993579151187i$。证明见报告第 2–6 页。 |
| 存疑 | 把选定的模式旋转解释成有限光锥上的几何平移，还需要给出保持端点边界条件的映射。 |
| 尚未核验 | 一般引力演化的自伴性、任意连续源的共同定义域，以及四维量子引力的紫外完备性。紫外完备性要求适用范围内的理论在任意短距离仍有一致的定义。 |

### 两个反例各自推翻什么

1. **发现反例。** 在论文选定的同一个高斯乘积态中，若直接把未减去均值的正二次源取无截断极限，则它在每个非零态上的二次型值都发散。减去均值后，对态具有有限范数，式（4.33）仍成立。
2. **发现反例。** 即使每段演化都幺正，两张中间切面的所有路径项也可能无法联合绝对求和。报告构造的例子中，每个矩阵块的路径绝对值总和都是 1，而最终振幅为 $1/3$。逐张切面加入投影的极限仍满足式（4.31）。

报告第 6 页分别写出待反驳命题、构造及证明。这两个反例限定了上述数学命题的适用范围，对原量子引力理论能否紫外完备没有给出判定。

### 复现计算

解压 v0.1.0 发布包，或检出同名 Git 标签，然后进入这份 README 所在目录。把虚拟环境和新结果放在快照外。基准环境使用 CPython 3.12.10、SymPy 1.14.0 和 mpmath 1.3.0。依赖文件固定了两个安装包的 SHA-256。在 Windows PowerShell 中执行：

~~~powershell
py -3.12 -m venv ../null-cone-env
../null-cone-env/Scripts/python.exe -m pip install --only-binary=:all: --require-hashes -r requirements.txt
../null-cone-env/Scripts/python.exe -B tools/snapshot.py
../null-cone-env/Scripts/python.exe -B reproduce.py --out ../null-cone-run --compare
~~~

在 macOS 或 Linux 中执行：

~~~sh
python3.12 -m venv ../null-cone-env
../null-cone-env/bin/python -m pip install --only-binary=:all: --require-hashes -r requirements.txt
../null-cone-env/bin/python -B tools/snapshot.py
../null-cone-env/bin/python -B reproduce.py --out ../null-cone-run --compare
~~~

每次复跑选择一个新的输出目录。依赖就绪后，科学计算可以离线执行。程序依次运行符号推导、高精度计算、11 项单元测试和独立审查脚本，保存各步完整的标准输出、错误输出、命令、版本、退出码和输出哈希。`--compare` 会将九个结果文件与包内基准逐字节比较，比较内容包括 Python 版本。换用其他解释器或系统数学库，末位数字可能不同。省略该参数仍会执行全部数学和数值断言。[基准运行清单](baseline/run.json) · [原始数值记录](baseline/numerical.jsonl) · [独立检验脚本](tests/independent_checks.py)

用上面选定的解释器替换下列命令中的 `python`。第一条联网核对 arXiv v1 的 PDF 和源码字节，不向磁盘保存论文。第二条从包内 LaTeX 源码编译英文报告，需要 pdfLaTeX、AMS 数学包和字体、geometry、xcolor 和 hyperref。不同 TeX 发行版可能生成不同的 PDF 字节。第三条核验文件清单并从冻结文件重建 ZIP。

~~~sh
python -B tools/check_paper.py
python -B tools/build_report.py --out ../rebuilt-report.pdf
python -B tools/snapshot.py --zip ../rebuilt-snapshot.zip
~~~

### AI 贡献、人工核验和同行评审

项目负责人确定研究问题和范围，并授权公开本版。OpenAI Codex 完成主推导、编写并运行符号计算与数值程序、整理报告和发布材料。第一阶段另开了独立 AI 上下文，先只读原论文并写下推导，再对照主审结果，检验两个推广命题并编写仅依赖 Python 标准库的脚本。每个数学结论的依据都是列出的证明。

截至 2026 年 11 月 26 日，项目记录中没有人工逐式核验的签署或记录，也没有针对这份核验成果的外部同行评审报告。原论文的作者与本核验项目分别署名。建议引用方式、论文指纹和使用许可见[版本记录](VERSION.md)、[原文指纹](reference/paper.json)和[许可说明](LICENSE.md)。
