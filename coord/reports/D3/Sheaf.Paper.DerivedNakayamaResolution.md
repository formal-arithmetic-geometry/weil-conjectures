## What changed

Completed `AlgebraicGeometry.ProEtale.DerivedNakayama.derived_nakayama_resolution` in
`lean/Sheaf/Paper/DerivedNakayamaResolution.lean`. The theorem statement and every existing
definition and instance are unchanged. Added only proved private constructions and lemmas.
No consumer or source-library module is modified. All original public imports are retained.
The change record `coord/changes/d3-derived-nakayama-proof-scopes.md` documents the local
instance scope and the consumer identified by preflight; no forced adaptation is required.

The proof constructs multiplication and reduction as internal-module maps, proves sectionwise
short exactness using continuous division and discrete quotient lifts, and transports it by
exact `mapMod` inverse image. The adopted `DerivedCategory.reductionIso` and its naturality
compute the same two-term rank-one resolution. A private commutative copy of `End(unit)`
supplies its linear scalar action. Transporting the entire short complex through
`regularPullbackIso` avoids expensive unfolding of internal-module record equalities.
Mathlib's cokernel-of-composition snake sequence constructs the normalized quotient-power
maps. Applying the degree-zero short-exact-sequence triangle and triangulated `tensorLeft`
proves the specified triangles for every unbounded complex.

Updated the resolution node's proof, proof dependencies, proof origin, and obsolete tool
approvals to record this implementation. The blueprint unit and all its statements and
steps are preserved. Exactness is also proved at exponent zero and for the empty profinite
space; the public theorem keeps its original positive-exponent hypotheses.

Validation: the complete module compiled through `lcompile.py` in 36.8 seconds and the
final clean axiom probe compiled in 36.0 seconds. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`. Import-cycle checks passed for
the four new nontrivial proof dependencies. The delivery runs the required compile and
preflight again.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.ProEtale.DerivedNakayama.derived_nakayama_resolution`
(node `det-pe-derived-nakayama-resolution`). This is a proof, not a decomposition.

Remaining holes in the item: zero. Added holes: zero. Split-off statements: zero.
All new helpers are private and completely proved. No new module, axiom, hollow definition,
or arbitrary witness from an unproved existence theorem is introduced.

## No longer needed

Removed these direct imports from this item:

- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.Topology.ProfiniteCondensedRing`

The original public `CoefficientExtensionFinite` import is retained for the unit route and
consumer compatibility. The proof itself obtains discreteness from the proved coset basis;
a section of the discrete quotient gives continuous lifts without a separate finiteness
theorem. The original public right-derived-functor import is likewise retained.
The proof operates directly on internal module objects and the existing monoidal derived
category, so the section-module equivalence and independent-coefficient K-flat/descent
route are unnecessary. It uses the adopted flat left-Kan-extension theorem directly for
point inverse-image exactness. The right-derived-functor API is unrelated to the proof but remains publicly available.

Removed these planned proof dependencies:

- `lem-weil-pbc-standard-quotients-perfect`
- `lem-weil-pbc-sheafification-exact`
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-sheaf-tensor-closed`
- `def-pc-flat-sheaf-modules`
- `lem-weil-pbc-independent-bounded-flat-kflat`
- `lem-pc-kflat-resolution`
- `lem-weil-pbc-site-derived-tensor-descent`
- `def-pc-tensor-complex-sheaves`

Removed these obsolete top-level tool approvals, preserving all remaining approvals in order:

- `lem-weil-pbc-standard-quotients-perfect`
- `lem-weil-pbc-sheafification-exact`
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `lem-weil-pbc-independent-bounded-flat-kflat`
- `lem-pc-kflat-resolution`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-sheaf-tensor-closed`

These are dependencies no longer needed by this item; no module is withdrawn or deleted.
In particular the blueprint UNIT's independent citation of
`lem-weil-pbc-standard-quotients-perfect` remains intact, and this delivery does not request
its global removal. Adopted source-library declarations and imports are untouched.

## Where the brief, the DAG or earlier work was wrong

The statements need no repair. The expanded DAG prescribed an unnecessary change to
section-module sheaves and a separate independent-coefficient tensor model: the adopted
internal-module monoidal derived category already proves the required natural tensor-cone
comparison and triangulated tensor functor. The cokernel-of-composition sequence gives the
same normalized quotient maps and exact sequence without a second sectionwise construction.
This preserves the unit's point sequence, exact pullback, two-term free resolution, and
quotient-power-triangle route.

The restored live item was used as the base; no quarantined attachment or dependency was
withdrawn. There was no compiler/tool malfunction and no statement dispute.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
