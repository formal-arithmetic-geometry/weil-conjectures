## What changed

Filled `WeilConjectures.integral_point_dual_models` in
`Sheaf.Paper.IntegralPointDualModels`, retaining its complete signature and all existing
public definitions and public imports. Added only proved private helpers for the signed
Hom degree equivalence, its differential and bounds, its derived model, the sequence
Roos difference map, and the implication from classical adic completeness to derived
completeness. Updated the existing node's proof, proof dependencies and proof origin to
match the actual argument.

The coefficient DVR supplies Noetherianity. The existing finite-module adic-completeness
result supplies completeness of the coefficient ring. Adic limits of finite geometric
partial sums invert the sequence difference map; the countable-product cohomology
comparison then proves derived completeness. Existing upstream perfect-complex theorems
give perfectness and finite bounded cohomology of the dual. The ordinary signed model is
computed using Mathlib's cochains to a single complex and the stated projective Hom model.
Finally, perfect objects are dualizable, so the existing formal strong-monoidal comparison
theorem proves invertibility of the exact canonical `ihomUnitComparison`. Dualizing each
finite free reduction gives the common reversed interval.

Searches used the required LeanFinder, Loogle and Mathlib grep services. Loogle found
`Module.dual_projective`; Mathlib also supplies `Module.dual_finite` and
`HomComplex.Cochain.toSingleEquiv`. The upstream search found
`DerivedCategory.IsPerfect.ihom_unit`, `.finite_homology`,
`.exists_homologyConcentratedIn`, and `.isDualizable`. These avoid rebuilding abstract
perfect duality or translating between ordinary modules and one-object-site modules.

Initial resumed validation found and repaired the signed-scalar rewrite, the explicit
argument to the homology isomorphism criterion, and the contravariant orientation of
the model-transport isomorphisms, and an unconstrained unused universe in the adic
completeness theorem application. The final item compiled cleanly through `lcompile.py`
in 12.4 seconds, with no warnings. Provider interruptions lost no sandbox changes.

## Proved and sorry left

Closed the one original hole, `WeilConjectures.integral_point_dual_models`
(`lem-sf-integral-point-dual-models`). Zero holes remain in the item, and zero new holes
are added. This is a proof from existing declarations, including the project's stated
`CochainComplex.projective_hom_evaluation_model`; no assertion is made that all its
transitive dependencies are already free of holes. No statement was split off.

The signed degree calculation gives the requested sign `(-1)^(i+1)`, and the bounds use
only integer inequalities, so negative and empty intervals are included. The sequence
argument includes `f = 0`. The proof uses no condition on ramification and treats every
positive coefficient exponent through the existing `n + 1` indexing.

## No longer needed

Removed the private imports `Sheaf.ZetaWeil.FiniteProjectiveModuleDualPairing` and
`Sheaf.Algebra.Homology.BaseChangeRHomPerfect`, and their node dependencies
`lem-zl-finite-projective-module-dual-pairing` and `lem-pc-base-change-rhom-perfect`.
Mathlib's proved dual module instances give the former's needed clauses directly;
the proved formal comparison for strong monoidal functors and dualizable objects gives
the latter's needed conclusion directly in ordinary modules. No new site-comparison
lemma is needed. Removed their obsolete top-level tool-use approvals from this node.

Removed redundant original private imports
`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, `Mathlib.RingTheory.Noetherian.Basic`,
and `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`; retained public imports expose
the required API. Also omitted redundant candidate imports of HomComplexSingle,
DerivedCategory.FullyFaithful, Preserves.Shapes.Products, AdicCompletion.Basic and
Data.Int.Interval after checking public import exposure. The direct proof dependency
`lem-weil-l-adic-extension-complete` is replaced by the existing
`lem-pod-adic-limit-finite-modules`, which already proves the relevant classical adic
completeness; field completeness remains needed inside that existing theorem.
No module is withdrawn, and no claim is made that a removed direct dependency is unused
elsewhere in the library. The unit statement and its steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-site base-change application does not directly have the ordinary
module category of this theorem. That translation is avoidable: the theorem's existing
reduction is already strong monoidal, and the source library proves that perfect objects
are dualizable. Its formal internal-Hom comparison therefore proves the precise canonical
map with no change of statement, coefficients, or category. Similarly, the classical
adic completeness needed for the sequence argument is already available in the library.
No mathematical statement correction or definition repair is necessary. No target or
consumer changes meaning.

The resumed dispatch metadata reference clock was reset automatically from `1792670510.0919163` to `1792730542.4936678` across provider interruptions. The original sandbox and proof were preserved; no budget metadata was edited by this worker.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
