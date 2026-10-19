## What changed

Completed the original set-valued topological-invariance theorem without changing its
signature or public imports. Retained and repaired the earlier attempt's full affine-basis
proof chain: `UniversallyHomeomorphIntegral`, `ProEtaleAffineBaseChangeEquivalence`,
`ProEtaleAffineBaseChangeDense`, `ProEtaleSheafAffineTopologicalInvariance`,
`ProEtaleSheafEquivalenceZariskiLocal`, and
`ProEtaleSheafDirectImageTopologicalInvariance` (all under
`Sheaf.AlgebraicGeometry`). Each new module has its own DAG node and a complete proof.

The affine-category proof descends maps into the etale terms using the existing etale
universal-homeomorphism equivalence, then combines them by limits. Essential surjectivity
comes from descending the whole presentation and taking its affine-scheme limit. The
covering proof descends finite jointly-surjective basis families. Dense-subsite comparison
identifies the affine direct image; weakly-etale base change, mates and cover-local detection
of isomorphisms glue the actual adjunction over an affine cover of the target. The final
adjunction API supplies the inverse-image equivalence and the specified unit and counit.

Checked the empty scheme/empty cover, identities, non-finite universal homeomorphisms and
non-quasi-separated schemes: no extra hypothesis is used. Single-file compilation through
`lcompile.py --all` succeeded for all seven modules. The required delivery preflight checks
the axiom census as well. No existing interface or definition changes, hence no forced adaptations.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.proEtaleSheaf_topological_invariance`
(node `lem-trf-proetale-topological-invariance`). Added 0 holes. No `sorry` remains in
any delivered module. This is a proof, not a decomposition into new admitted statements.

The six helper theorems are also proved: `isUniversalHomeomorphism_of_universally_isHomeomorph`,
`proEtaleAffineBaseChange_isEquivalence`, `proEtaleAffineBaseChange_isDenseSubsite`,
`proEtaleSheafDirectImage_affine_topological_invariance`,
`proEtaleSheafDirectImage_isEquivalence_of_openCover`, and
`proEtaleSheafDirectImage_topological_invariance` (first in `AlgebraicGeometry`,
the others in `AlgebraicGeometry.Scheme`).

## No longer needed

Removed the following proof imports from the item module:

- `Sheaf.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.RingTheory.Etale.Basic`
- `Mathlib.Algebra.Category.Ring.FinitePresentation`
- `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`
- `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`
- `Mathlib.Algebra.Category.Ring.FilteredColimits`
- `Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Sheaf.RingTheory.IndPrincipalZariski`
- `Mathlib.Algebra.Category.CommAlgCat.Basic`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
- `Sheaf.RingTheory.IndEtaleStability`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv`
- `WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.Paper.SliceSiteLocalization`
- `Mathlib.CategoryTheory.Sites.LocalProperties`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.RingTheory.IndEtaleUniverseTransport`

The etale-equivalence, affine-basis and affineness-descent inputs are still used by the
proved helper chain, so those are not globally pruned. The inverse-image definitions and
the general adjunction and cover-local APIs are also still used.

The explicit finite-presentation/filtered-colimit Hom argument is unnecessary: etale
uniqueness/existence after a universal homeomorphism and the actual limit presentations
prove full faithfulness directly. The route therefore does not need
`lem-weil-pbc-etale-algebra-finite-presentation-localization`,
`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`,
`lem-weil-pbc-filtered-colimit-algebras-elementwise`,
`lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise`,
`lem-weil-pbc-commutative-algebras-colimits-exist`, or the explicit tensor-colimit step.
It also does not invoke the broad admitted `IndEtaleStability`, `SliceSiteLocalization`
or `weaklyEtale_localization` theorem: the pinned source's proved affine-basis and
weakly-etale base-change/localization APIs provide precisely the needed assertions.
`lem-weil-pbc-site-equivalence-is-morphism-of-sites` and
`lem-cbc-local-dense-ordinary-sheaves` are replaced by Mathlib's dense-subsite API.
No unit-level step is bypassed: affine etale descent, affine ind-etale basis comparison,
cover compatibility and Zariski localization are all realized.

Removed the obsolete top-level tool approvals from the item node for
`lem-weil-pbc-surjective-universally-closed-affine-target`,
`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`,
`lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise`,
`lem-weil-pbc-commutative-algebras-colimits-exist`,
`lem-weil-pbc-ind-etale-stability`, `lem-weil-pbc-slice-site-localization`, and
`lem-weil-proetale-weakly-etale-localization`; the affineness-descent dependency is now
recorded on the helpers that actually use it.

## Where the brief, the DAG or earlier work was wrong

The existing sandbox report and node records described an admitted direct-image theorem,
but the retained Lean had already proved it and its intermediate statements. This delivery
updates those records and supplies the missing nodes. The affine essential-surjectivity
code needed explicit object identifications, affine instances and functor identity/composition
proofs to compile against current sources. No mathematical statement was weakened.

Updated the item docstring to describe this actual proof route, removing the obsolete
finite-presentation and filtered-colimit argument.

The source's abelian-valued invariance theorem cannot be applied to `Type (u + 1)`;
the proof instead uses its coefficient-independent site and localization infrastructure.
No definition repair or target-statement change was necessary.

## New nodes

`lem-trf-proetale-affine-base-change-dense`: The base-changed affine ind-etale basis is dense. This helper is proved with no admitted substatement; its node records the source, precise dependencies and realized argument.

`lem-trf-proetale-affine-base-change-equivalence`: Affine ind-etale base change along a universal homeomorphism. This helper is proved with no admitted substatement; its node records the source, precise dependencies and realized argument.

`lem-trf-proetale-affine-topological-invariance`: Topological invariance over an affine target. This helper is proved with no admitted substatement; its node records the source, precise dependencies and realized argument.

`lem-trf-proetale-sheaf-equivalence-zariski-local`: Direct-image equivalence is local on the target. This helper is proved with no admitted substatement; its node records the source, precise dependencies and realized argument.

`lem-trf-proetale-topological-invariance-direct-image`: Direct image invariance for small pro-etale sheaves. This helper is proved with no admitted substatement; its node records the source, precise dependencies and realized argument.

`lem-trf-universally-homeomorph-integral`: Universal homeomorphisms are integral. This helper is proved with no admitted substatement; its node records the source, precise dependencies and realized argument.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
