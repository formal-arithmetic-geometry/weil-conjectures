## What changed

Proved `AlgebraicGeometry.Scheme.Modules.cechH1_injective` in
`Sheaf.AlgebraicGeometry.CechH1Injective`, keeping its signature, universe,
visibility and canonical-comparison predicate unchanged. The canonical family
comes from `cechH1Map_natural`. The existing
`moduleCech_resolution_column_zero` supplies the kernel property of every
column augmentation. Four completely proved private helpers construct the
bidegree projections, identify the sole total-degree-zero summand, calculate
its total differential, and chase a degree-one boundary. This makes
`H¹(moduleCechBeta)` monomorphic. Its factorization through the canonical
comparison then proves the required underlying-function injectivity.

Added proof-only imports `Sheaf.AlgebraicGeometry.ModuleCechResolutionColumnZero`
and `Mathlib.Algebra.Homology.Refinements`. Retained the original public import
`Sheaf.AlgebraicGeometry.CechH1MapNatural`; public interfaces are unchanged.
Updated only `proof`, `proof_deps` and `proof_origin` in
`dag/nodes/sec-curve-estimates/lem-sc-cech-h1-injective.json`.
No other module is adapted, and no statement or definition is changed.

The proof is an elementary low-degree chase in the double complex and beta map
constructed in Stacks Tag 01EQ, proving the injectivity of Tag 0B8R. Both official
source pages were checked:
https://stacks.math.columbia.edu/tag/01EQ and
https://stacks.math.columbia.edu/tag/0B8R.
The alternative chase is marked as worker-written in the proof-origin record.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.cechH1_injective`
(node `lem-sc-cech-h1-injective`). Added zero holes; zero holes remain in the
item or elsewhere in this delivery. This is a proof, not a decomposition.
All private helpers have complete proofs. There are no new public declarations.

The single-file local compile succeeded without warnings in approximately six
seconds. `#print axioms AlgebraicGeometry.Scheme.Modules.cechH1_injective`
reported exactly `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.
The diagnostic print was removed from the delivered file.

The generic boundary-lifting argument does not assume a nonempty cover index
or nonzero coefficient module, and uses kernels, not positive cohomology
vanishing. Empty families, empty opens and zero modules are supported by the
existing column-kernel theorem. The open-cover hypothesis is used only to
obtain the canonical comparison family. In total degree zero, only (0,0)
occurs; both total differential signs there are +1, checked in Lean.

## No longer needed

Removed these direct proof imports and their proof-dependency edges:

- `Sheaf.CategoryTheory.SiteCechComplex`, node
  `def-weil-pbc-site-cech-complex`: the argument uses the existing concrete
  module-valued Cech complex, not the separate general-site construction.
- `Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree`, node
  `lem-sc-zariski-module-abelian-cohomology-agree`: all maps and kernels stay
  in the global-section module category.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`, node
  `lem-sc-cech-spectral`: the degree-one boundary chase proves injectivity
  directly and needs no Cech-to-derived spectral sequence or edge-map bridge.

These are removed from this item's proof route. Other items can still need
them; no claim of removing them from every target's import closure is made.
The existing definitions publicly needed by the statement remain available.
No realized unit statement or unit proof step is bypassed:
`dag/units/sk-thm-curveestimate.json` realizes only
`thm-sc-proper-cohomology`, and its steps list is empty; this item is below
that level. No additional modules or nodes are needed solely by this proof.

## Where the brief, the DAG or earlier work was wrong

The original statement is correct. The original spectral-sequence proof plan
is mathematically valid, but its Lean spectral-sequence existence theorem
provides nonempty page identifications and an abutment, rather than the
canonical edge-map identification needed for `IsModuleCechComparison`.
The existing module-valued comparison and column-kernel theorem support a
shorter direct proof, so no new edge-map or module/abelian comparison lemma
was introduced. The old docstring was updated to describe the actual proof.

The local `literature/stacks-project/cohomology.tex` file is absent on this
machine; the two cited official source pages were read instead. This caused
no tool or mathematical blocker. No target or intermediate interface changed.

## Second reading by G1

1. Compared the delivered module and node with the repository versions. The target theorem signature, universe, visibility, and canonical-comparison predicate are unchanged; only proof, imports, and proof metadata differ.
2. Compiled the module locally and checked `#print axioms`; compilation is clean and the target depends only on `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions in the delivered file.
3. Read the proof and its private helpers. The boundary-lifting argument is fully proved, and no new public or split-off statement was added. The injectivity conclusion is obtained from the unchanged comparison equation and `ModuleCat.mono_iff_injective`.
4. Checked pruning and imports. The proof uses the natural comparison, module Cech double-complex definitions, the column-zero kernel theorem, and Mathlib refinements; the prior spectral-sequence, site-Cech, and module/abelian comparison imports are removed from the route.
5. Checked the unit route and edge cases. The unit realization is untouched; the direct low-degree chase applies to empty covers, empty opens, and zero modules because it uses kernel universal properties rather than nonvanishing assumptions. The node proof, dependencies, and origin agree with the Lean proof.

I changed only proof-only imports, the proof body/docstring, node proof metadata, and this review section. No statement or definition was changed.
