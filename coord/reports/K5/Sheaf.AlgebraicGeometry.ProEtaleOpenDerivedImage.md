## What changed

Proved AlgebraicGeometry.ProEtale.finiteCoefficientOpenDerivedImage with its complete signature unchanged. Two new proved helper modules supply the ordinary coefficient-linear restriction comparison and K-injective preservation. The first uses Mathlib cocontinuous sheafification compatibility, the ringed-site pushforward adjunction and uniqueness against the existing normalized finiteModuleAdjunction. Its two unit normalizations are proved explicitly. The second transports slice K-injectivity across the concrete coefficient-preserving site equivalence. A proved private categorical helper constructs the right-derived comparison on complexes, its Kan universal property, invertibility on K-injectives, and the derived-unit equation from the upstream homotopy-derived adjunction. No definitions or existing public signatures change. The two new helper nodes are proved auxiliary results, not split-off obligations.

Validation: all three modules compile through lcompile.py --all, individually in import order and within the file time limit. The resumed dry run passed compilation and preflight (CODEX review class). Its axiom probes for the two helper modules received no answer from the busy compile service within 201 seconds; the merge reruns these probes. The delivery has no new sorry and uses only existing published dependencies.

## Proved and sorry left

Closed 1 of 1 original holes: AlgebraicGeometry.ProEtale.finiteCoefficientOpenDerivedImage (lem-exc-proetale-open-derived-image). Added 0 holes. Both new theorems AlgebraicGeometry.ProEtale.finiteCoefficientOpenRestriction (lem-exc-finite-coefficient-open-restriction) and AlgebraicGeometry.ProEtale.finiteCoefficientOpenPullback_isKInjective (lem-exc-finite-coefficient-open-kinjective) are proved. There are no remaining sorry declarations in any delivered module. Existing imported project theorems may still depend on sorry; this delivery proves the assigned theorem from those published declarations, as stage 3 requires.

## No longer needed

Removed direct proof imports Sheaf.Algebra.Homology.KInjectiveRestrictLocalized, Sheaf.CategoryTheory.KInjectiveTotalDerived, WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp, Mathlib.CategoryTheory.Sites.CoverLifting, Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap, Sheaf.AlgebraicGeometry.ProEtaleFiniteModules, Sheaf.AlgebraicGeometry.ProEtaleInverseImage, Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction and Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization. Localized K-injectivity, covering infrastructure, coefficient maps, coefficient modules and weakly-etale localization remain needed transitively in the helper proofs or statement interfaces.

The proof does not use lem-sfb-proetale-object-inverse-image-restriction or lem-cbc-sieve-slice-sheafification: Mathlib's sheafification comparison and uniqueness of the normalized module left adjoint replace that argument. It does not use lem-weil-pbc-kinjective-total-derived, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-hom-derived or lem-sf-exact-functor-derived-triangulated: upstream rightDerivedFunctor and mapDerivedCategoryRightDerivedAdjunction supply the categorical construction, and the private helper proves the comparison and unit transport. The abstract derived-category definitions remain in statement imports; no separate proof application of def-weil-abstract-derived-category is needed. Parent proof_deps and tool_uses now describe this route. No unit route is bypassed and no whole module is claimed unreachable from all other users.

## Where the brief, the DAG or earlier work was wrong

The existing proEtaleOpenUnitEvaluation theorem handles commutative coefficients of Type u and cannot directly supply the arbitrary Ring coefficients of Type (u + 1) required here. Its two coefficient-independent site definitions remain used. The existing ProEtaleFiniteModuleAdjunction module already gives the needed normalized adjunction for arbitrary finite rings; uniqueness of left adjoints avoids a fresh noncommutative Kan-colimit construction. The earlier retained attempt left the ordinary restriction helper open; this session completed it. The upstream library already supplies the generic exact-left-adjoint derived-adjunction construction, making a separate total-derived-existence argument unnecessary.

The initial dry run waited for worktree capacity and then refused the retained split-off sorry before 60 percent of the budget. That split-off has now been proved; the delivery adds no sorry. After the provider interruption, the resumed dry run compiled all three modules and then required a change record for section-level universe and variable commands around the private categorical helper. Its parameters and universes are now declared directly on the private theorem, keeping all commands and public interfaces of the existing module unchanged; leanindex reports no interface changes.

## New nodes

lem-exc-finite-coefficient-open-restriction records the proved ordinary coefficient-linear open restriction and its two unit normalizations, from original steps 1--3 and Stacks Tags 03CE, 04IX, 03D3. The argument is uniform for empty schemes and the zero ring and does not require commutativity.

lem-exc-finite-coefficient-open-kinjective records the proved K-injectivity preservation from original step 4 and Stacks Tag 08FI. It applies to unbounded complexes, including zero complexes, with no termwise-injectivity hypothesis. Neither new node leaves an obligation for another worker. No change record is needed: no existing signature, definition or public import changes.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
