# Sextic SPR: Necessity of Numerator Degree Six

[简体中文](README.zh-CN.md)

A standalone Lean 4 / mathlib proof of an explicit sextic interval example showing that a common SPR numerator can genuinely require degree six.

## What this repository proves

The concrete coefficient box has six independent intervals of strictly positive width. Every denominator in the entire box is strictly Hurwitz stable. One explicit real numerator of exact degree six satisfies

$$
\operatorname{Re}\left(\frac{b(i\omega)}{a(i\omega)}\right)>0
\quad\text{for every box member }a\text{ and every }\omega\in\mathbb R.
$$

At the same time, **no nonzero real polynomial of degree at most five** satisfies even weak frequency positivity for the whole box. This establishes degree necessity for this example, not the claim that every sextic box requires degree six.

The complete theorem [`SPR.DegreeNecessity.counterexample`](DegreeNecessity/Result.lean) combines positive widths, stability, the degree-six witness, and lower-degree exclusion without additional stability or certificate premises.

## Setup and build

Install Git and [elan](https://github.com/leanprover/elan), and make sure `elan` is on your PATH. Run these commands in a macOS, Linux, or Windows WSL shell:

```sh
git clone https://github.com/dgjszy/sextic-spr-degree-necessity.git
cd sextic-spr-degree-necessity
elan toolchain install leanprover/lean4:v4.30.0
elan run leanprover/lean4:v4.30.0 lake exe cache get
elan run leanprover/lean4:v4.30.0 lake build
```

This repository does not currently include `lean-toolchain` or `lake-manifest.json`. Always invoke Lake through the explicit toolchain above. [`lakefile.lean`](lakefile.lean) requires Lean **4.30.0** and pins mathlib to commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Lake resolves dependencies and creates its local manifest on first use; internet access is required for the toolchain, dependencies, and cache.

This is a local proof library; no server or database deployment is needed. The formal build requires neither Python nor an external solver.

## Verify and use

```sh
elan run leanprover/lean4:v4.30.0 lake env lean Audit.lean
```

The default build includes a transitive axiom audit that permits only `propext`, `Classical.choice`, and `Quot.sound`; any other axiom causes an error.

Within this project's Lean environment:

```lean
import DegreeNecessity.Result

#check SPR.DegreeNecessity.counterexample
#print axioms SPR.DegreeNecessity.counterexample
```

## Repository layout

- [`DegreeNecessity/Basic.lean`](DegreeNecessity/Basic.lean): explicit box and witness definitions.
- [`DegreeNecessity/Stability.lean`](DegreeNecessity/Stability.lean): robust stability.
- [`DegreeNecessity/Witness.lean`](DegreeNecessity/Witness.lean): degree-six SPR witness.
- [`DegreeNecessity/Exclusion.lean`](DegreeNecessity/Exclusion.lean): exclusion of all nonzero lower-degree numerators.
- [`DegreeNecessity/Result.lean`](DegreeNecessity/Result.lean): complete theorem.
- [`Audit.lean`](Audit.lean): theorem checks and axiom audit.
