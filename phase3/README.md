# 光锥量子引力独立核验 · Lean 4 候选版 v0.3.0-rc.1

本工程把 v0.2.0 的主要数学推理写成 Lean 定理。双边算符模型的五组投影都强趋于恒等，同一个有符号闭合振幅却有五种极限。对普通正迹，整个空间上统一严格正的权重与有限迹合在一起确实推出有限维。式（4.33）的标量级数绝对收敛，硬截断的实际三阶系数随截断发散。[中文报告](REPORT_CN.md) · [English report](REPORT_EN.md) · [公式与定理索引](FORMALIZATION_MAP.md) · [假设清单](ASSUMPTIONS.md)

本候选从公开提交 `44df2c1e4915c0e654dd5907d91b775e83f31326` 分出。研究对象是 arXiv:2611.34924v1。原始 PDF、TeX 的字节指纹及页码来自既有版本记录。物理闭合与局域四维引力约束属于单独的问题。[公开 v0.2.0](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/releases/tag/v0.2.0) · [原文 v1](https://arxiv.org/abs/2611.34924v1) · [原文摘要记录](../reference/phase2.json)

## 从干净目录编译

安装 Git、Python 3 和能够按 `lean-toolchain` 选择版本的 elan。解开候选归档，进入 `phase3`。在已安装固定版本 Lean 的系统上，也可以直接把该工具链的 `bin` 放入 PATH。以下命令适用于 PowerShell 和常见的 Unix shell。

```sh
lake exe cache get
python verify.py
```

本次运行覆盖 16 个证明模块、145 条公开定理和 6 项独立语义复核。第一步通过 Lake 读取已提交的依赖清单，取得数学库及其缓存。第二步核对实际编译器、九个依赖的提交及其受版本控制的文件，编译工程，运行独立复核用例，再为每条公开定理输出完整类型和 `#print axioms`。默认日志写在 `.lake/verification/`。Python 脚本只使用标准库。首次下载依赖需要网络。源码按固定提交取得时，mathlib 同版本的压缩缓存也可用于离线解包。[Lean 工具链](lean-toolchain) · [Lake 工程](lakefile.toml) · [依赖锁](lake-manifest.json) · [检查脚本](verify.py)

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true review/Regression.lean
```

这三条命令可分别检查证明、逐条公理及审查者写下的等价表述。要重放编译产物的内核声明，另用同一 Lean 编译 lean4checker 的固定提交，然后把可执行文件传给检查脚本。每个证明模块单独重放，以控制内存使用。

```sh
git clone https://github.com/leanprover/lean4checker.git ../phase3-checker
git -C ../phase3-checker checkout --detach da26eb05e9959402afcb9bd6dfe5dc4f700f70d6
(cd ../phase3-checker && lake build)
python verify.py --replay ../phase3-checker/.lake/build/bin/lean4checker
```

上面括号内的命令使用 Unix shell。在 PowerShell 中进入 `../phase3-checker` 运行 `lake build`，然后回到 `phase3`，可执行文件带 `.exe`。lean4checker 使用 Lean 内核，将各证明模块自己的声明重新加入由其导入项构成的环境。检查使用锁定版 Lean 和 mathlib。公理清单允许 `propext`（命题外延性）、`Classical.choice`（选择公理）和 `Quot.sound`（商类型规则）。[重放工具](https://github.com/leanprover/lean4checker/tree/da26eb05e9959402afcb9bd6dfe5dc4f700f70d6) · [实际构建记录](evidence/run.json) · [完整定理与公理输出](evidence/axioms.log) · [独立语义复核](review/INDEPENDENT.md)

## 源码入口

| 问题 | 从这里读 |
| --- | --- |
| 同一双边算符与五种极限 | [总反例](NullCone/Counterexample.lean) · [有限振幅](NullCone/Amplitude.lean) · [五条极限](NullCone/Limits.lean) |
| 开放求和、普通正迹与有限维 | [迹与开边界](NullCone/Trace.lean) · [Hilbert–Schmidt 判别](NullCone/HilbertSchmidt.lean) · [有限秩负界与充分条件](NullCone/Dimension.lean) |
| 响应界与面积窗 | [右腿提升](NullCone/Response.lean) · [非对易的高秩低矩截断](NullCone/Dilution.lean) · [实际面积的谱演算](NullCone/Area.lean) |
| 标量振幅与微扰展开 | [模式级数与导数](NullCone/Series.lean) · [无截断振幅的三阶差商](NullCone/Perturbation.lean) · [物理变量换算](review/SERIES.md) |
| 证明强度及复现环境 | [定理目录](FORMALIZATION_MAP.md) · [预先判据](review/BLIND.md) · [复编说明](evidence/ENVIRONMENT.md) |

候选根目录的 `python tools/snapshot.py` 校验整个分发包的成员及 SHA-256。前两阶段仍使用根目录的 `reproduce.py`。在原公开标签上可以复现原版的确定性归档。
