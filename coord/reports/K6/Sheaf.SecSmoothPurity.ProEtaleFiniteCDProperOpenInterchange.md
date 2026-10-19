## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleFiniteCDProperOpenInterchange` in the assigned module, with its signature and all definitions unchanged. Added private proof imports of the proved source-library finite-CD theorem and open-extension full-faithfulness instances, and of Mathlib's adjunction composition API.

For a degreewise-injective K-injective representative J, Cartesian injective acyclicity and the all-sheaf bound compute Rp_*k_!M by p_*k_!J. The specified sheaf comparison identifies this with an object in the image of i_!. Exact descent of the invertible sheaf open unit makes derived i_! fully faithful. Its counit at Rp_*k_!M is therefore invertible. The actual canonical comparison is i_! of the specified inverse lambda followed by this counit, so it is invertible. Its two normalization equations are the inverse adjunction formula and its inverse identity. This uses an essential-image witness only to prove invertibility of the actual counit; it does not replace the canonical comparison by an arbitrary isomorphism.

Updated the existing node's proof, proof dependencies, proof origin and obsolete tool-use entry to describe this route. No new module, statement, definition, or axiom was added. The public-import pruning is documented in `coord/changes/K6-finite-cd-proper-open-proof-imports.md`; `tools/downstream.py` reports zero consumers, and the removed module's sole theorem has no external textual users.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.proEtaleFiniteCDProperOpenInterchange` (node `lem-exc-proetale-finite-cd-proper-open-interchange`). Proved 1 of 1 original sorries. Zero sorries remain in the item; zero holes were added or split off. Existing imported statements may still have their own sorries, as allowed by the stage-3 brief.

## No longer needed

Removed the direct import of `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`: its mathematical input is supplied by the already proved source-library specialization `Functor.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic`, imported from `WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension`. The node `lem-kun-finite-cd-acyclic-complex` remains a mathematical dependency.

Removed redundant direct proof imports `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`, `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, and `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison`; their declarations are already publicly available through `ProperExceptionalOpenBaseChange`.

The route no longer needs a separate use of `lem-weil-pbc-kinjective-hom-derived`, or a separate replacement I of k_!J and use of `lem-weil-pbc-derived-functor-injective-vanishing`. Existing derived functors and their comparison units handle localization. Removed the former node's obsolete `tool_uses` entry. The generic finite-CD theorem internally handles resolutions and injective acyclicity. No claim is made that these modules disappear from the entire targets' import closure, since other users may retain them. The blueprint unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The six-step DAG plan is valid but longer than necessary for the existing Lean definition: the canonical comparison is already defined as the open transpose of the specified inverse lambda. Thus an essential-image computation and the fully faithful adjunction's counit criterion prove invertibility, and both normalization identities follow formally. There is no need to construct and compare a new derived natural transformation or separately prove representative independence.

The cited current blueprint proof file differs from the retained repaired proof described by the existing node; this delivery uses the retained repaired finite-CD argument recorded in the node and the cited generic derived-category result, without changing the blueprint unit or target statements.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
