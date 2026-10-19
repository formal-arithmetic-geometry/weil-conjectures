## What changed

Proved `AlgebraicGeometry.etaleModule_affine_cohomology_isZero` with its original signature.
The proof annihilates the underlying abelian sheaf by the positive integer ℓ^a, applies
`ProEtale.classicalUniformBounds` to the constant affine presentation of W, and transfers
vanishing to étale cohomology using `comparisonUpperStarCompUpperStarIso` and
`comparisonCohomologyMap_bijective`. Constant-module inverse image commutes with the
abelian forgetful functor via `upperStarForget₂Comparison`.

For the module-resolution conclusion, the constant-ring module equivalence transfers
injectivity to sheaves valued in `ModuleCat A`. The existing, proved
`Sheaf.subsingleton_H_forget₂_of_injective` gives abelian acyclicity for these finite
coefficients. `moduleSheaves_colimits_forgetful` and
`Functor.exists_rightDerived_exact_comp_iso` then compute derived abelian sections on
the chosen module resolution. Exact scalar forgetting commutes with homology and its
faithfulness reflects zero objects. All these steps are in the item's proof; there are
no helper modules, changed definitions, or changed target statements.

Validation: the retained proof compiled cleanly against the current published build in
the required delivery dry run on this resumed attempt. The theorem signature is unchanged; its proof docstring
now names the comparison and acyclicity declarations actually used. There are no Lean
lines over 100 characters.

The item DAG records this route. One node attaches the existing finite-ring acyclicity
theorem from the source library; it introduces no Lean declaration or hole.

## Proved and sorry left

Closed `AlgebraicGeometry.etaleModule_affine_cohomology_isZero`
(`lem-sfb-etale-module-affine-bound`): one of one original holes closed.
Zero holes added or split off. No sorry remains in the delivered module.
The finite-ring acyclicity node attaches an existing proved declaration.
The uniform pro-étale bound and abelian comparison remain the existing stated inputs.

## No longer needed

Removed the original direct imports of `Sheaf.AlgebraicGeometry.EtaleComparison`,
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`: the used geometry is
available through the bound and comparison imports.
Removed `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: the existing
`comparisonUpperStarCompUpperStarIso` supplies the coefficient identification directly.
Removed `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
(`lem-pe-constant-left-module-inverse-image`): `upperStarForget₂Comparison` handles the
actual constant-coefficient module sheaf encoding.
Removed `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
(`lem-weil-pbc-module-sheaves-enough-injectives`): the constant-module equivalence
transfers enough injectives from the Grothendieck module-valued sheaf category at the
required universes.
Removed `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`
(`lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`): finite-ring abelian
acyclicity and the exact-composite theorem give the needed terminal evaluation comparison.
The corresponding three obsolete top-level tool approvals were removed from the node.
Also removed redundant proof imports of `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`, and
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`; their required
instances are already publicly available through the retained imports.

The proof does not call `etale_indEtale_weaklyEtale_comparison`
(`det-pe-morphisms-etale-comparison`): Mathlib supplies the weakly-étale instance.
It also does not call `supportSiteComparison_pullback_coherent`
(`lem-weil-pbc-comparison-pullback`): the source library supplies the needed
`comparisonUpperStarCompUpperStarIso` directly. Both unused proof dependencies and
their top-level tool approvals were removed from the node; the constant-presentation
argument and the coefficient identification remain unchanged.

Temporary unlanded helper modules `AffineEtaleTorsionBound`, `ModuleEvaluationZero`, and
`ModuleCatIsZeroOfUnderlying`, as well as the earlier underlying-homology split, are absent
from this delivery. Their arguments are inlined and no helper sorry is introduced.
The temporary helper node was never landed and is not delivered. These are sandbox
artifacts, so no repository module is withdrawn and there is no `deleted.txt`.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's report claimed compilation before the current retained file compiled.
The generic evaluation comparison requires `SmallCategory W.left.Etale`; the étale site
has object universe u+1 and hom universe u, so that interface does not fit. The declared
enough-injectives theorem is also formulated only for a lifted smaller coefficient ring.
The constant-ring equivalence and the proved finite-ring acyclicity theorem give the
required instances and comparison without changing any existing interface.
The edge cases of empty schemes, zero coefficients, and arbitrary nonconstructible
coefficient sheaves are preserved: the proof imposes no nonemptiness or sectionwise
finiteness assumption. The unit's constant-presentation geometric route is retained.
`hℓk` and `ha` are retained unchanged even though the stronger uniform torsion bound
already covers the coefficient cases they restrict.

## New nodes

`lem-sfb-finite-ring-injective-abelian-acyclic` records the existing source theorem
`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective` in
`WeilConjectures.CategoryTheory.Sites.SheafCohomologyModules`. Its complete proof uses
coinduction into an injective abelian sheaf and the finite cyclic decomposition of the
coefficient ring. It is the acyclicity input for the module/abelian evaluation comparison;
no duplicate Lean statement and no new hole are added. The additional tools
`lem-sc-ext-derived-composite` and `lem-weil-pbc-module-sheaves-colimits-forgetful` are
used for the standard exact-composite comparison; they replace the unusable generic
comparison interface rather than bypassing the geometric unit route.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
