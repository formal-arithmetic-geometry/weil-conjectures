## What changed

Only `lean/Sheaf/Paper/SmoothPurityTowerInjectiveComponents.lean` and its existing node's proof record change. Existing public signatures and definitions are unchanged.

Proved coefficient-ring-map naturality by sheafification-adjunction naturality, then assembled the successive-level naturality squares with `NatTrans.ofOpSequence` and uncurrying. A private, completely proved helper handles arbitrary coefficient-ring maps. Proved preservation of the vertical sheaf condition using ordinary continuous sheaf direct image. Proved finite-limit preservation of tower pushforward using pointwise module-presheaf limits, closure of the vertical sheaf condition under limits, and reflection by the full-subcategory inclusion; additivity follows from finite-product preservation. Added the proof-only Mathlib full-subcategory-limit import.

Proved the normalized underived evaluation isomorphism: the section normalization gives equality of the two section modules, restriction and morphism normalizations prove naturality, and the identity-on-sections equation proves uniqueness. All transport helpers are private and completely proved.

Proved the injective-complex computation from the existing component acyclicity statement and `isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`. Proved the supplied-resolution computation by `asIso` of exactly the three specified morphisms. Added the proof-only import `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact` and used its existing exact-functor unit theorem for evaluation. Proved the natural derived comparison by constructing both composite right derived functors, transporting the underived comparison with `rightDerivedNatIso`, checking both units, and applying `rightDerived_ext` for uniqueness.

The main component theorem remains an existing dependency with its original hole. No claim is made that the derived consequences are independent of it. On resuming, a fresh compile exposed variable runtime near the 60-second limit. Profiling isolated 32.5 seconds of kernel checking in the concrete derived comparison. The same proof now lives in a fully proved private lemma over abstract abelian categories, instantiated by the unchanged public theorem. This avoids repeatedly unfolding the concrete tower categories. The final module passed the remote single-file compiler in 21.7 seconds (exit code 0, no diagnostics). The delivery gates also check the remaining hole and declaration signatures.

## Proved and sorry left

Closed 8 of the original 9 holes (namespace `AlgebraicGeometry.ProEtale`):

- `spTowerRingMap_naturality`
- `spTowerPush_sheaf`
- `spTowerPush_properties`
- `spTowerEvaluationIso_existsUnique`
- `sp_tower_injective_complex_computes`
- `sp_tower_injective_resolution_computes`
- `sp_tower_evaluation_derived_unit`
- `sp_tower_derived_direct_image_evaluation`

Added 0 holes and split off 0 statements.

The 1 original hole left, attached to `det-sp-tower-injective-components`, is:

- `AlgebraicGeometry.ProEtale.sp_tower_injective_components`: evaluate the split embedding supplied by the right-adjoint theorem to get the finite-product retract; transport restricted-injective section acyclicity, then obtain direct-image acyclicity.

## No longer needed

Removed direct proof imports `Mathlib.CategoryTheory.Abelian.RightDerived` (already available through the acyclicity API) and `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`. The explicit K-injectivity dependency `lem-weil-pbc-bounded-below-injectives-kinjective` is not used: the formal statements here are on D+, and the published acyclic-unit theorem and exact-unit theorem directly prove the required computations. Removed that node from this item's proof dependencies and obsolete tool-use approval. This does not assert that its module becomes globally unreachable; Mathlib's derivability construction can still import it transitively.

Removed redundant direct imports `Sheaf.CategoryTheory.RingedSiteModules` and `Sheaf.Paper.SmoothPurityCoefficientTowers`: their declarations are already publicly imported by the coefficient-tower abelian module. The right-adjoint module remains imported for the unfinished component theorem. No other mathematical dependency or module is pruned. The original ringed-site and abelian-cohomology imports are retained for the unfinished component theorem and its unchanged proof plan. The generic exact-unit input is the existing, already proved node `src-sbc-exact-functor-plus-unit`; no new statement is introduced.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was found. The original node's separate K-injectivity comparison is unnecessary for its actual D+ Lean signatures. The unit route (right-adjoint embedding, finite-product retract, section acyclicity, and derived evaluation) is preserved. The item has nine original holes, not ten as initially counted in the progress commentary. The independent coefficient universe requires explicit annotations on the local quotient-ring morphism; no equality of scheme and coefficient universes is imposed.

The resumed dry run flagged the earlier sandbox's added global universe names as an interface-command change. The transport helpers now bind those universes on their own declarations, restoring the original global universe command and avoiding any interface change. The continuation also replaced the expensive concrete derived-comparison proof by its generic private argument; no definition, statement, file split or timeout limit changed.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
