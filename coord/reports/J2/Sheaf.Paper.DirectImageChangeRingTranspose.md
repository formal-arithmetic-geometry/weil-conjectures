## What changed

Proved `AlgebraicGeometry.ProEtale.directImageChangeRingTranspose` with its original
signature unchanged. Its three conjuncts follow from the ordinary pure-tensor
normalization, the coefficient-adjunction mate identity, and counit naturality.

Added two proved modules. `DirectImageTensorPullbackNormalization` constructs the
ordinary comparison termwise, proves its pure-tensor formula, and identifies its
localization with the specified derived comparison. `DirectImageTensorPullbackLocalization`
proves a generic mate-transport identity from the two normalized adjunction units and
four functor comparison isomorphisms. No existing definition or signature changed.
The new imports used only by proofs are private imports.

The normalization proof uses the published K-flat resolution theorem to extend the
normalized scalar-unit identity to every complex by naturality and cancellation of
a localized quasi-isomorphism. The exact-functor factorization lemmas identify the
ordinary restriction/pullback square with the derived one. Applying the generic
mate identity then proves the full localization square, with no new hypothesis.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.directImageChangeRingTranspose`
(node `lem-sp-direct-image-change-ring-transpose`), one of one original holes.

New theorems proved in this delivery:
`AlgebraicGeometry.ProEtale.directImageChangeRing_tensorNormalization`
(node `lem-sp-direct-image-tensor-pullback-normalization`) and
`directImageChangeRing_tensorNormalization_localization`
(node `lem-sp-direct-image-tensor-pullback-localization`).
All private helpers are proved. No sorry remains in any delivery module, and no
holes are added or split off. Existing imported declarations are used as published.

Validation: the full three-module sandbox compiled cleanly after the resume repairs:
localization 0.0 s (cached), normalization 43.1 s, and the item 16.0 s.
All three files contain zero `sorry` occurrences.

## No longer needed

Removed direct proof imports of
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`, and
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`. The coefficient-map and
operation interfaces remain available through the existing public imports; the new
normalization proof supplies the representative calculation instead of directly
invoking tensor descent. No entire original dependency node or module is pruned
from the transitive closure. The new helper modules keep the existing unit route.
The generic localization lemma needs only Mathlib adjunction mates and category
rewriting. The normalization proof does not require proving pullback preservation
of K-flatness or assuming that B is flat over A: scalar-unit normalization extends
to arbitrary complexes via a K-flat resolution and counit naturality.

The interrupted standalone `DirectImageTensorPullbackModel` was never landed;
its ordinary construction is proved privately in the normalization module. It is
not delivered, and no library module is withdrawn. Scratchpad files are not delivered.

## Where the brief, the DAG or earlier work was wrong

The retained report described localization as an open hole. The retained later
proof already reduced it to a generic normalized-mate calculation. Expanding the
functor map of a composite before applying the inverse-mate unit identity completes
that calculation. The final derived square follows from its actual normalization
hypotheses and the ordinary unit square; no pure-tensor extensionality assumption
or new existence theorem is needed.

The resumed compile found stale alias-sensitive rewriting and an over-eager `ext`
in the retained proof. Explicit associativity before the normalized-unit rewrite,
`erw` for the scalar-extension alias, and `HomologicalComplex.hom_ext` repair these.
The expensive unit calculation is replaced by `Iso.comp_inv_eq`, avoiding the
large sheaf construction unfolded by cancellation rewriting. The current library also requires the proved
`Functor.mapDerivedCategoryNatIso_symm` API from the private import
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`; inversion
of the induced natural isomorphism is not definitionally transparent. Normalizing
the identity complex comparisons in the generic exact-functor lemma before its
sheaf specialization avoids expensive reduction of the sheaf construction. The
termwise chain maps use `NatTrans.mapHomologicalComplex` directly. The complete
normalization file now compiles within the unchanged 60-second limit.
The retained profiling-only module is moved to the scratchpad and is not delivered.

The statements admit zero rings, identity coefficient maps, zero complexes, empty
schemes and non-flat coefficient quotients. The proofs use no properness, finiteness
or boundedness beyond the unchanged original statement. No target statement changes.

## New nodes

`lem-sp-direct-image-tensor-pullback-normalization` records the proved normalization
witness, its pure-tensor formula and localization square.
`lem-sp-direct-image-tensor-pullback-localization` records the proved generic
mate-transport identity. Both have their sources, search records, Lean statements
and proof steps. No change record is needed: all existing signatures, definitions
and public imports are unchanged.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
