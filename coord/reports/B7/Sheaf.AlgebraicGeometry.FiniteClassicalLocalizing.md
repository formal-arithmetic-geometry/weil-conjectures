## What changed

Filled the proof of `AlgebraicGeometry.ProEtale.finite_classical_localizing` in
`Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing`, preserving its complete statement
and public imports. Added proved private helpers for classical coproducts, truncation
coproduct preservation, finite constant models, exact constant-scalar restriction, and
the underlying sheaf of the canonical internal-to-intrinsic realization.

The proof follows the six-step argument: weak Serre closure gives triangulated closure;
comparison inverse image gives heart coproduct closure; exact coproducts and conservative
homology give the derived coproduct/truncation assertions; the coefficient pullback
comparison gives classical pullback and canonical truncation equations; finite discrete
constructibility encoding gives classical generators; and the intersection definition of
localizing closure gives the final inclusion. The canonical realization is unchanged.
The copied DAG records the actual declarations used. The change record
`coord/changes/B7-finite-classical-localizing-proof-commands.md` documents the
proof elaboration options and zero-object notation flagged by static preflight.
The downstream check reports no external module requiring adaptation.

## Proved and sorry left

Closed the single hole in `AlgebraicGeometry.ProEtale.finite_classical_localizing`
(node `lem-sfb-finite-classical-localizing`). Added zero holes. No `sorry` remains in the
item or any delivery file. No new public declarations, definitions, or modules.

The theorem signature and public imports were compared verbatim with the shared source;
both are unchanged. Every Lean line is at most 100 characters. The complete file passed
`lcompile.py` in 34.8 seconds with exit code zero and no warnings. The delivery tool
records its own final compilation, axiom probe, and preflight results.

## No longer needed

Removed proof imports (and two unused exploratory Mathlib imports,
`Mathlib.CategoryTheory.Sites.PreservesSheafification` and
`Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits`):

- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`.
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`.
- `Sheaf.Paper.FiniteDiscreteSchemeRing` (available through the coefficient encoding).
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`.

The direct node dependencies `lem-kun-grothendieck-derived-coproducts` and
`sk-thm-pe-direct-image-comparison` are replaced by the existing source homology-coproduct
instance and the specific coefficient-pullback encoding respectively. The large general
constructible comparison is replaced by the finite-discrete heart encoding and the
fixed-module constructible-origin theorem. The direct node `sk-thm-pe-constructible-comparison` is replaced by
`lem-weil-pbc-fixed-module-constructible-origin`. The direct node
`lem-weil-pbc-module-sheaves-colimits-forgetful` is unnecessary
as a direct dependency because the requisite preservation instances already exist.
No declaration or module is withdrawn: these statements remain available to other users.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The final clause requires an explicit
comparison with the *specified* `integralModelIntrinsicRealization`, rather than an arbitrary
coefficient equivalence. The proof supplies its underlying-sheaf isomorphism and proves
exactness and coproduct preservation by conservative forgetful functors. The finite Tor
bound and the nilpotence hypothesis are not used by this classicality argument.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
