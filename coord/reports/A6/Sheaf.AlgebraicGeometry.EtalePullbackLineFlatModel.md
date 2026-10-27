## What changed

Completed `AlgebraicGeometry.Etale.etale_pullback_line_flat_model` in
`Sheaf.AlgebraicGeometry.EtalePullbackLineFlatModel`. All existing signatures,
definitions and public imports are unchanged. Added one proved private generic
helper, `line_comparison_isIso`, identifying the actual localization tensor map
with the K-flat tensor counit. Updated the item's proof, proof dependencies,
proof origin and obsolete top-level tool approvals to describe the direct proof.

The proof uses the already proved fixed-coefficient source-library APIs. It proves
flatness of the locally trivial line by geometric stalks, descends its finite
local constancy, and proves each term's flatness and constructibility directly.
It proves support and K-flatness, invertibility of the prescribed comparison,
constructible homology, and the Tor interval. Finally it constructs the required
isomorphisms on each prescribed stratum and on the actual fibre-product common
refinement, preserving each specified finite module value.

Proof imports added: `WeilConjectures.ConstructibleSheaf.InternalHom`,
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`,
and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`.
Verification: the complete hole-free proof compiled with `lcompile.py` in 53.5
seconds with profiling enabled. Profiling options were then removed. The proof
imports were minimized: `Monoidal` and `KernelCokernel` are public dependencies of
`InternalHom` and need no redundant explicit imports.

No other module is adapted. No definition repair or change record is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.etale_pullback_line_flat_model`
(node `lem-sp-etale-pullback-line-flat-model`). The private comparison helper is
also completely proved. Holes closed: 1 of 1. Holes added: 0. Split off: 0.
There are no remaining `sorry`s in the delivered module or added elsewhere.

## No longer needed

The following proof imports are removed; their modules are not withdrawn because
other arguments may still need them:

- `WeilConjectures.ConstructibleSheaf.KernelCokernel`: already publicly imported
  through `InternalHom` and its `Monoidal` dependency; its theorems remain in use.
- `Sheaf.AlgebraicGeometry.FiniteFlatConstructibleTotalTensor`: direct termwise
  flatness, support and bounded-flat criteria avoid the two-complex total tensor.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`: the proved
  fixed-coefficient `upperStarPreservesFlat_moduleCat` supplies flat pullback.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`: the source
  `upperStarComp` supplies composition for the actual ModuleCat-valued sheaves.
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`: the proved source
  `upperStarConstantSheafIso` transports the specified constant values directly.
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeEtaleFlat`: geometric stalks identify
  the line with the tensor unit and prove its flatness directly.
- `Sheaf.Algebra.Homology.TotalTensorSignedCoherence`: the model already is the
  shifted termwise tensor; the homology shift isomorphism handles its integer shift.
- `Sheaf.Paper.EtaleKFlatCriteria`: the proved generic bounded-above flat criterion
  applies directly to these cochain complexes.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`: exact pullback's existing
  `mapDerivedCategoryFactors` and the prescribed representative suffice.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`: the source monoidal pullback
  comparison applies to the actual ModuleCat sheaves.

Consequently the following nodes are removed from this item's proof dependencies
and its top-level `tool_uses` (remaining approvals keep their order):
`lem-weil-pbc-ringed-topos-flat-module-pullback`,
`lem-pur-scheme-constructible-preimage`,
`lem-weil-pbc-inverse-image-composition-module-linear`,
`lem-kun-pullback-constant`, `lem-pur-finite-locally-free-etale-flat`,
`lem-sfb-finite-flat-constructible-total-tensor`,
`lem-pur-total-tensor-signed-coherence`, `lem-kun-kflat-criteria`,
`lem-weil-pbc-ringed-topoi-derived-pullback`, and
`lem-weil-pbc-ringed-topoi-module-pullback-tensor`.
The separate constructible-preimage lemma is unnecessary because the source
constructible-pullback theorem already performs that argument. The existing
stratification pullback and cover base-change constructions remain in use.
No source-library declaration or module is removed. No unit's own statement or
proof route is bypassed; this is a shorter proof of its line-model dependency.

## Where the brief, the DAG or earlier work was wrong

The planned total-tensor and general ringed-topos detour was unnecessary: the
adopted library already proves the fixed-coefficient flat-pullback, bounded-flat
K-flatness and Tor-bound results needed here. Its existing constructibility and
monoidal inverse-image APIs also provide the explicit witnesses. The statement
itself needs no correction. The proof allows empty strata and cover members,
the zero coefficient ring, a one-degree support interval, and every integer shift.
The line trivialization is used rather than replaced by an arbitrarily chosen
existence witness. No target or source-library interface changes.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
