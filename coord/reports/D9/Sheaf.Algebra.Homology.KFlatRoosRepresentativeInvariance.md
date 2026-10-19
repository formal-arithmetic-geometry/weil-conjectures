## What changed

Proved representativeInvariance using a generic comparison for arbitrary complexes in Roos coordinates. The item now proves strict augmentation naturality, K-flat tensor invariance with independent site universes, exact-product invariance, the common K-flat roof construction for every derived isomorphism, its augmentation comparison equation, and both implications of the augmentation criterion. The generic coordinate comparison has its own module and node, and is proved from degreewise split short exact sequences and the existing homology-sequence comparison theorem.

## Proved and sorry left

Closed: SheafOfModules.KFlatRoos.representativeInvariance (the single original hole).
Also proved: CochainComplex.quasiIso_of_roos_coordinates
(lem-pe-roos-coordinates-quasi-iso), including the coordinate chain maps, the
degreewise split short exact sequences, their morphism and the shifted outer
quasi-isomorphism. Every helper is proved. Holes added: zero. Sorries left in the
item and the new module: zero. Net holes closed minus added: one. The proof uses
existing library declarations as intended by stage 3; no assumptions were added
and no target changed.

## No longer needed

Removed proof imports Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso and Sheaf.CategoryTheory.StrictRoosComparison. Their nodes lem-pur-change-of-rings-kflat-quasi-iso and lem-weil-strict-roos-comparison are unused: a tensor-square argument works directly over R and the generic coordinate lemma handles the Roos comparison. Removed direct imports Mathlib.CategoryTheory.Localization.CalculusOfFractions and Mathlib.CategoryTheory.Abelian.FunctorCategory; DerivedCategory.right_fac packages the calculus. The levelwise-abelian tower node lem-weil-tower-category-levelwise-abelian is unused because the proof works with products of complexes directly. Removed their tool_uses entries. Statement imports remain as before.

## Where the brief, the DAG or earlier work was wrong

The change-of-rings declaration has one common site/coefficient universe, whereas this item allows independent universes. The strict Roos comparison also has a larger interface requiring tower derived categories. Rather than alter those declarations or the item, the proof resolves the coefficient module in degree zero, uses categorical K-flatness and the tensor square, and compares the explicit Roos coordinates. Identity and zero complexes, arbitrary endomorphisms, and nonflat coefficient algebras satisfy these arguments. The current unit has no realized proof steps, so this change does not bypass a unit step.

## New nodes

lem-pe-roos-coordinates-quasi-iso, in Sheaf.Algebra.Homology.RoosCoordinatesQuasiIso, is the proved generic diagonal mapping-fiber comparison. It has no site, product, K-flat, flat-term, or derived-isomorphism hypothesis. It is strictly part of the original argument, and the item supplies all its coordinate identities definitionally. No existing signatures or definitions were changed. The scoped commands around private
proofs trigger the static interface check; their scope and the complete consumer list
are recorded in coord/changes/D9-kflat-roos-private-proof-context.md.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
