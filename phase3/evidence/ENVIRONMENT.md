# 编译和复算记录

候选版以 v0.2.0 的提交 `44df2c1e4915c0e654dd5907d91b775e83f31326` 为基线。编译器为 Lean 4.24.0，提交 `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`。mathlib 固定在 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`，另八个传递依赖的提交均由 Lake 清单固定。编译和重放在 Windows x86-64 上执行。Python 3.12.10 用于记录日志和复算前两阶段。[受检输入的 SHA-256](inputs.json) · [逐项链接与原文指纹核查](source-check.log) · [版本清单](../lake-manifest.json) · [上游 mathlib](https://github.com/leanprover-community/mathlib4/tree/f897ebcf72cd16f89ab4577d0c826cd14afaafc7)

第二个构建目录使用独立的依赖工作树。九个仓库各自从本机镜像按清单的提交浅取出，核对 HEAD 及受版本控制的文件。该目录起初没有本工程的 Lean 源码和编译结果。只复制候选源码、清单和验证程序，候选模块的 .olean 文件由新的编译产生。独立语义复核用例也重新从源码编译。

依赖准备阶段，下载 leantar 的 GitHub 连接被重置。随后使用本机已有的 leantar 0.1.15、7335 个 mathlib 内容缓存包和 ProofWidgets v0.0.74 发布归档。仅缓存归档而未展开前端文件时，Lake 报告缺少 ProofWidgets 构建结果。核对 ProofWidgets 的 Git 标签，按发布归档解出其 js 目录后，标准命令 `lake exe cache get` 成功，随后按同一个清单构建。ProofWidgets 归档的 SHA-256 为 `c55e692bcf8de76c5be780666e07d0c0cd523100c86fc6eb7197c65808edff74`。这次复现使用了预编译依赖，未从零重建 Lean 自身和整个 mathlib。[缓存准备日志](dependency-ready.log)

最初的验收脚本指定了这个 Lean 版本不支持的打印宽度选项。删去该显示选项后，最终验收在另一个没有工程编译产物的目录从头运行；两次使用相同的独立依赖检出。依赖下载诊断与早期打印诊断的完整输出保存在[准备过程](setup/)。

[build.log](build.log) 记录 Lake 的完整构建输出。[axioms.log](axioms.log) 记录每条公开定理的完整类型以及传递依赖的基础公理。[semantic-tests.log](semantic-tests.log) 记录隔离审查上下文写出的等价表述。逐模块的 `replay-NullCone.*.log` 由 lean4checker 产生；每个命令与退出状态均列在 [run.json](run.json)。重放从相应模块锁定的导入环境开始，以 Lean 内核再次检查该模块自己的声明。该工具与 Lean 使用同一个内核。机器检查的对象是写出的数学命题，命题和论文之间的对应另由[独立审查](../review/INDEPENDENT.md)核对。

开发工作区另行完整执行了构建、145 条定理公理检查及 6 项语义用例。两个目录的定理签名/公理日志和语义测试日志分别逐字节相同。[两处运行对比](compare.log) · [另一次运行](workspace/run.json)

在候选工作区重新执行了 `reproduce.py --phase 1` 和 `--phase 2`，两次均带 `--compare`，所有结果文件均与 v0.2.0 的已提交基线逐字节相同。前两阶段的完整原始数值、标准输出及错误流仍可在[第一阶段基线](../../baseline/)与[第二阶段基线](../../phase2/baseline/)查阅。本次对应命令和输出摘要见 [legacy-checks.log](legacy-checks.log)。

