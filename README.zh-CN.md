# 六阶 SPR：六次分子的必要性

[English](README.md)

本仓库是一个独立的 Lean 4 / mathlib 证明工程，通过一个显式六阶区间实例，说明公共 SPR 分子确实可能必须达到六次。

## 本仓库证明的结论

具体系数箱的六个独立区间均具有严格正宽度，整个箱内每个分母均严格 Hurwitz 稳定。一个显式的实系数恰六次分子满足

$$
\operatorname{Re}\left(\frac{b(i\omega)}{a(i\omega)}\right)>0
\quad\text{对箱内每个分母 }a\text{ 以及每个 }\omega\in\mathbb R.
$$

与此同时，**不存在次数至多为五的非零实多项式**，能对整个箱满足哪怕是弱频域非负性。这证明该实例的次数必要性，并不声称每个六阶箱都必须使用六次分子。

完整定理 [`SPR.DegreeNecessity.counterexample`](DegreeNecessity/Result.lean) 同时包含正宽度、稳定性、六次见证及低次排除，不需要额外的稳定性或证书前提。

## 环境安装与构建

安装 Git 和 [elan](https://github.com/leanprover/elan)，并确认 `elan` 已加入 PATH。在 macOS、Linux 或 Windows 的 WSL 环境中执行：

```sh
git clone https://github.com/dgjszy/sextic-spr-degree-necessity.git
cd sextic-spr-degree-necessity
elan toolchain install leanprover/lean4:v4.30.0
elan run leanprover/lean4:v4.30.0 lake exe cache get
elan run leanprover/lean4:v4.30.0 lake build
```

当前仓库未包含 `lean-toolchain` 或 `lake-manifest.json`，因此应始终通过上面显式指定的工具链调用 Lake。[`lakefile.lean`](lakefile.lean) 要求 Lean **4.30.0**，并将 mathlib 固定到提交 `c5ea00351c28e24afc9f0f84379aa41082b1188f`。Lake 在首次使用时解析依赖并生成本地清单；下载工具链、依赖及缓存需要联网。

本仓库是本地证明库，无需部署服务器或配置数据库。正式构建不需要 Python 或外部求解器。

## 验证与使用

```sh
elan run leanprover/lean4:v4.30.0 lake env lean Audit.lean
```

默认构建包含传递公理审计，仅允许 `propext`、`Classical.choice` 和 `Quot.sound`；发现其他公理时会报错。

在本工程的 Lean 环境中使用：

```lean
import DegreeNecessity.Result

#check SPR.DegreeNecessity.counterexample
#print axioms SPR.DegreeNecessity.counterexample
```

## 仓库结构

- [`DegreeNecessity/Basic.lean`](DegreeNecessity/Basic.lean)：显式区间箱及见证定义。
- [`DegreeNecessity/Stability.lean`](DegreeNecessity/Stability.lean)：鲁棒稳定性。
- [`DegreeNecessity/Witness.lean`](DegreeNecessity/Witness.lean)：六次 SPR 见证。
- [`DegreeNecessity/Exclusion.lean`](DegreeNecessity/Exclusion.lean)：排除全部非零低次分子。
- [`DegreeNecessity/Result.lean`](DegreeNecessity/Result.lean)：完整定理。
- [`Audit.lean`](Audit.lean)：定理检查和公理审计。
