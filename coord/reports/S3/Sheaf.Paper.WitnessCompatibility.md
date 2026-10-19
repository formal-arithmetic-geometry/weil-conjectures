## What changed

Proved five supporting theorems in Sheaf.Paper.WitnessCompatibility. Scalar restriction now obtains its derived left adjoint from ordinary sheaf scalar extension: its restricted composite is tensor with the coefficient sheaf, K-flat acyclicity gives derivability, and the existing source-library derived adjunction applies. The three tower identity/composition/category proofs use functoriality and component extensionality. The reduction-domain proof explicitly transports the constructible realization witness along theta inverse.

Added proof-only imports of WeilConjectures.CategoryTheory.DerivedCategory.Adjunction, WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic, WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange and WeilConjectures.CategoryTheory.Sites.ReductionFlat. Updated the definition node's proof record to describe the supporting proofs and the remaining obligation. No signature, definition, visibility or target statement changed. No forced adaptations or new statements.

## Proved and sorry left

Closed 5 of the 6 original holes, all in namespace AlgebraicGeometry.ProEtale:

- pbcRestriction_isRightAdjoint
- pbcWitnessedTower_id_laws
- pbcWitnessedTower_comp_laws
- pbcWitnessedTower_category_laws
- pbcWitnessedInput_memReductionDomain

One original sorry remains: AlgebraicGeometry.ProEtale.pbcComparisonReductionMap_isIso, attached to def-weil-pbc-witness-compatibility. Its statement and complete proof-in-words docstring are unchanged. It still needs the identification of ordinary K-flat scalar-extension balancing with the particular derived comparison mate used by pbcComparisonReductionMap. No holes were added; no statements were split off. After checking the retained sandbox against current sources, the final module, including import pruning, compiled cleanly through lcompile.py in 8.7 seconds.

## No longer needed

Removed the unused proof-only import Sheaf.Paper.RingedTopoiCanonicalTensorPullback. None of the five completed proofs uses its declarations. In particular, scalar restriction is constructed directly for fixed coefficient rings, without passing through the general variable-ring sheaf equivalence or the general ringed tensor-pullback theorem. The latter remains a conceptual statement dependency of the witness predicate and its unfinished comparison obligation; its node is not deleted or claimed globally obsolete. No public imports were removed. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The definition node originally had no proof steps, although its module had six supporting theorem holes. The existing source-library K-flat and derived-adjunction API supplies the arbitrary-ring scalar-restriction assertion directly. The ordinary scalar-extension/comparison isomorphism by itself does not identify the derived mate in the remaining assertion, so that assertion is honestly retained as an original hole.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
