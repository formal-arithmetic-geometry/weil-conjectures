## What changed

Completed all three original proof bodies without changing their signatures:
`stratumDualTensor_preservesFiniteLimits`, `stratumDualTensor_derived`, and
`closedSupport_stratum_globalHom`. The finite-limit proof identifies dual tensor with internal Hom using
the chosen dual pairing, then transports limit preservation across that isomorphism.
The first two RHom comparisons use additive coyoneda
adjunction and right-derived composition. The third uses ordinary closed monoidal duality,
exact dual tensor, and right-derived composition. The shifted clause uses the already proved
`CategoryTheory.derived_coyoneda_evaluation` for every integer.

The tensor comparison descends the existing single-complex tensor comparison to the homotopy
category and applies uniqueness of left derived functors. Explicit colimit and K-flat instances
avoid expensive instance search. The earlier main-module validation through lcompile.py succeeded; the final
main-module compile after expanding the finite-limit adjunction argument took 33.9 seconds.
On this resumption, the complete repaired sandbox compiled against the current
library, with the main module taking 45.7 seconds. The retained supporting modules
compile as well. Development profiler and trace options remain only in scratchpad.
The first preflight exited without a diagnostic. A later queued run was interrupted
by provider HTTP 429 errors before a result was retained; the final retry saves its
complete output in the sandbox scratchpad. No successful push was reported by those runs.
Both new node records now include actual LeanSearch queries in addition to their
retained Loogle/LeanFinder and grep searches.
The earlier downstream scan found 265 transitive consumers; the only two direct importers are
`Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum` and
`Sheaf.Paper.FormalClosedSupport`. Both direct consumers were compiled unchanged through lcompile.py against the sandbox
overlay: ConstructibleExtContinuityStratum in 4.0 seconds and FormalClosedSupport in
8.4 seconds, both checked again after the definition exposure repair. The former already imports the cochain tensor interface independently.
The definition `stratumDualTensor` now uses `@[no_expose]`, with its defining equation
proved as `stratumDualTensor_eq`; its construction and mathematical meaning are identical.
No target, coefficient convention, or universe changed. Updated both DAG nodes attached
to this module to the actual proof. The change record is
`coord/changes/D3-stratum-dual-tensor-exposure.md`.

## Proved and sorry left

Closed the three original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.stratumDualTensor_preservesFiniteLimits`.
- `AlgebraicGeometry.ProEtale.CondensedRing.stratumDualTensor_derived`.
- `AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_stratum_globalHom`.

Also proved `AlgebraicGeometry.ProEtale.CondensedRing.finiteLocallyProjective_isDualizable`
(node `lem-proetale-finite-projective-dualizable`) from local finite-power and retract duality,
canonical pullback comparison, and descent of isomorphisms. The earlier report incorrectly
listed this declaration as still open.

Also proved `AlgebraicGeometry.ProEtale.CondensedRing.supportPullback_ihomComparison_isIso`
(node `lem-proetale-pullback-internal-hom`) by the equalizer presentation of module internal Hom.
The comparison with the abstract closed structure is proved using uniqueness of right adjoints,
its embedding formula, the tensor quotient formula for coefficient pullback, and evaluation.
All helpers are proved. Closed three original holes, added zero holes: the item and both new
modules have zero `sorry`. This is a proof from the existing library, rather than a decomposition
leaving new obligations.

## No longer needed

Removed these fourteen original imports:

- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `Sheaf.Algebra.Homology.HomComplex`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`.
- `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Paper.CartesianCoefficients`.
- `Sheaf.Paper.FormalClosedSupportDerived`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.

Also removed the exploratory import `Sheaf.Paper.CondensedInternalHomSections`.

Proof-only imports now supply the generic derived/coyoneda and rigid APIs actually used.
The actual proof no longer directly uses these original proof nodes:
`sk-prop-sfb-cartesian-coefficients`, `prop-pur-kinjective-resolutions-exist`,
`def-pur-sheaf-hom`, `def-pur-sheaf-tensor-product`,
`def-weil-sheaf-of-modules-category`, `def-pc-kflat-complex`,
`def-pur-derived-internal-hom`, `lem-pur-hom-kflat-into-kinjective`,
`def-pur-ringed-site-zeroth-hypercohomology`, `lem-weil-pbc-kinjective-hom-derived`,
`def-pur-hom-complex`; the basics alias also no longer directly uses
`det-lem-formal-closed-support-derived` and `def-weil-size-convention` in its proof.
Statement dependencies remain unchanged, and the new local duality node retains its
internal-Hom/tensor definition dependencies. No claim is made that these modules are globally
unreachable: other items and retained transitive imports may still need them.
Removed obsolete top-level tool approvals from each node, retaining the right-adjoint
K-injective criterion. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous session left the weakly etale comparison as a split-off. On resumption,
its incomplete exploratory proof initially confused scalar transport with the identity;
that was replaced by the correct equalizer comparison with the coefficient isomorphism.
The comparison is now proved with the canonical strong monoidal structure.

The DAG's planned ringed-site Hom-complex transport is unnecessary for this degree-zero
source: ordinary module-object adjunction and derived coyoneda provide the comparisons
in the existing categories directly. The finite-projective local duality step and its weakly etale module internal-Hom comparison
are both proved. The generic theorem
`lem-weil-pbc-derived-coyoneda-evaluation` is used as a tool; it is already proved and merely
supplies the final passage from global RHom to shifted Hom, preserving the unit route.
No statement is disputed. The resumed attempt expanded the finite-limit proof into an
explicit natural isomorphism with internal Hom after the delivery checker rejected the
one-line application of the dualizability lemma as a restatement. This now records the
actual adjunction argument in Lean. The compile server once timed out waiting for an answer; retry
succeeded. There was no compile-limit increase.

## New nodes

`lem-proetale-finite-projective-dualizable` isolates finite locally projective local duality
from proof step 3. It is proved in Lean, including the finite-power induction, retract
argument, and descent of the canonical evaluation isomorphism. Its proof metadata now
records these steps and its dependency on the next node.

`lem-proetale-pullback-internal-hom` supplies compatibility of weakly etale coefficient
pullback with the canonical module internal-Hom comparison. It is proved by constructing
the natural equalizer isomorphism and comparing the two morphisms after the equalizer
embedding. The retained earlier scratch calculation was completed in the new module:
uncurrying reduces the comparison to tensorator naturality and the evaluation identity.
The argument uses no local projectivity or derived categories.
The three searches were run on resumption. Blueprint search for internal Hom found only
related finite-coefficient derived and etale statements, with different coefficient
categories or hypotheses. In particular `lem-weil-pbc-etale-pullback-internal-hom` concerns
fixed-ring module sheaves on small etale sites, and cannot supply this pro-etale coefficient
module-object statement. Its full proof in words appears in the docstring and node, and its Lean proof is complete.

The public-import pruning is recorded in
`coord/changes/D3-closed-support-stratum-hom-imports.md`; existing statements are unchanged.
The separate definition exposure repair retains exactly the original concrete construction.

The definition exposure change is recorded in `coord/changes/D3-stratum-dual-tensor-exposure.md`.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
