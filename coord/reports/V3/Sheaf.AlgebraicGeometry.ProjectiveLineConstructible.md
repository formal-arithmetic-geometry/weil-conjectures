## What changed

Repaired the returned import cycle by replacing the application of the downstream source
projective-line theorem with an actual proof from finite-curve finiteness and the existing
proved finite-order embedding criterion. The item no longer imports
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective` (or its cyclic
`ProjectiveCurve` counterpart).

The theorem, its signature and visibility, all public imports, and all public definitions
are unchanged. Five private helpers implement forgetting abelian sheaves to sets,
reconstructing finite-coefficient module constructibility, constant-module curve finiteness,
and the affine-base embedding argument. Every helper is proved. The private pullback
comparison is a genuine isomorphism construction from proved Kan-extension and
sheafification comparisons, with no arbitrary witness from a postponed theorem.

Over an affine base, embed each constructible sheaf into a finite sum of finite
pushforwards of finite constant module sheaves, using the existing source theorem
`exists_mono_biproduct_lowerStar_of_locallyOfFiniteType`. For each finite morphism h, the
composite with the projective-line projection is projective. Integral incomparability bounds
each geometric fibre dimension by that of the projective line. The finite module's additive
group has cardinal dividing a power of an invertible annihilator; apply the existing
`ProjectiveCurveFiniteGroup` declaration. The derived coefficient-forgetting comparison,
`finite_local_abelian_forget_iff`, and finite-coefficient reconstruction give module
constructibility. Exact finite direct image and derived composition identify the required
higher images, and finite biproducts preserve constructibility. The proved source embedding
criterion supplies the remaining resolution argument. Etale localization over affine opens
and the existing constructibility comparisons finish the exact stated theorem.

Updated only the existing node's proof, proof_deps, proof_origin, and obsolete tool_uses.
Its Lean attachment is restored to this item's original declaration, rather than the
returned delivery's downstream source theorem. The unit's realized statement/steps are empty;
no unit route is bypassed. No new nodes, modules, public definitions, signatures, change records,
withdrawals, or consumer adaptations are needed.

Validation: the complete proof compiled without warnings through lcompile.py in 42.9 seconds;
the required delivery dry run checks the exact submission. The original public theorem
signature was compared verbatim with the current repository. Empty bases, zero modules, trivial rings, negative integer degrees,
nonreduced or disconnected fibres, and nonseparated finite-type bases introduce no extra
hypothesis: dimensions use topological incomparability and the formal embedding criterion
handles all integer degrees.

## Proved and sorry left

Closed 1 of 1 original local holes:
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine`
(node `thm-fin-projective-line-constructible`). No sorry remains in the delivered module.
Holes added: 0. Split-offs: 0. This is a proof from existing declarations, not a decomposition
into new postponed lemmas.

Existing imported postponed theorems, including projective-curve finite-group finiteness and
coefficient/constructibility comparisons, remain the next obligations. This delivery does
not claim that the theorem's entire transitive axiom closure is already axiom-free.

## No longer needed

Removed these proof imports from the repository's planned version:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
- `Sheaf.AlgebraicGeometry.FiniteTypeFieldPushforwardEmbedding`
- `Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `Sheaf.RingTheory.IntegralExtensionDimension`
- `Sheaf.AlgebraicGeometry.DimensionAffineOpenCover`
- `Sheaf.AlgebraicGeometry.Dimension`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence`
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.CategoryTheory.CartanEilenbergExists`
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`
- `WeilConjectures.SixFunctors.BaseChange.EtaleDerived`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence`

The returned delivery's new downstream `Finiteness.Projective` import is also removed.
`ConstructibleSheaf.DenseOpenUnit` is retained for its constant-sheaf local-constancy instance.
The following planned nodes are absent from the new direct proof dependencies:

- `lemma-nagata-projective-space-base-change-proper`
- `def-weil-proper-morphism`
- `lem-weil-pbc-projective-space-standard-charts`
- `lem-weil-pbc-integral-extension-dimension`
- `lem-pc-dimension-affine-open-cover`
- `lem-pc-scheme-dimension-local-rings`
- `lem-weil-pbc-module-direct-image-left-exact`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-grothendieck-spectral-sequence`
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-sp-cartan-eilenberg-exists`
- `thm-sp-if-e1`
- `thm-sp-double-complex-spectral-sequences`

The projective-space standard charts and affine/local-ring dimension conversions are
replaced by the existing projective-line field dimension theorem and integral
incomparability. The separate left-exactness/enough-injectives, Grothendieck spectral
sequence, Cartan--Eilenberg, and hypercohomology modules are replaced by the existing proved
finite-order embedding criterion, exact finite-image comparison, and additivity.
Kernel/cokernel Serre closure is still used through that formal criterion. The source
embedding and finite direct-image implementations replace the narrower statement wrappers;
these mathematical lemmas themselves remain needed. Properness follows from the projective
instances and does not require a separate properness theorem as a direct dependency.
No claim is made that these removed imports are globally unreachable: other items or public
imports may still need them.

Removed obsolete maintainer tool-use entries, preserving the order of those retained:

- `lemma-nagata-projective-space-base-change-proper`
- `lem-weil-pbc-projective-space-standard-charts`
- `lem-weil-pbc-integral-extension-dimension`
- `lem-pc-dimension-affine-open-cover`
- `lem-pc-scheme-dimension-local-rings`
- `lem-weil-pbc-module-direct-image-left-exact`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-grothendieck-spectral-sequence`
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-sp-cartan-eilenberg-exists`
- `thm-sp-if-e1`
- `thm-sp-double-complex-spectral-sequences`

## Where the brief, the DAG or earlier work was wrong

The returned proof was circular: the current source
`hasConstructibleDirectImages_projectiveLine` is proved from this assigned Sheaf theorem.
Its import therefore cannot discharge this item. This repair imports neither that module nor
the source projective-curve module that reaches it. Import-direction checks on the new source
finiteness helpers are acyclic. The node remains attached to the assigned theorem.

The DAG's long spectral-sequence plan is unnecessary because the source library already
proves `hasConstructibleDirectImages_of_exists_mono`; its node is
`lem-finrepair-constructible-direct-images-from-embeddings`. The source finite-pushforward
embedding theorem works directly over every finite coefficient ring, so reducing through
Z/N is also unnecessary. Mathlib searches (LeanFinder, Loogle, grep, retained in the search
log) did not provide a direct etale-constructibility theorem. Source searches supplied the
formal resolution, finite-image comparison, integral incomparability and localization APIs.
No statement is disputed, weakened, or replaced by a same-statement postponed theorem.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
