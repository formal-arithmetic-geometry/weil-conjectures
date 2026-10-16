# IntegralLatticePair.equivalent_iff_image_eq

## Reason

Add completed image-classification and uniqueness lemmas for proof step 1, and
constant-matrix image/coset lemmas for the matrix part of proof step 4, of
`Sheaf.Paper.LatticeSheafLocallyConstant`. The static preflight classifies the new
section commands (`variable` and scoped elaborator settings) as an interface change.
The new section closes before the existing main theorem; its variables and settings
are scoped to the new proofs. All existing public declarations retain their exact
signatures, visibility, definitions, and meaning. This record documents the additions.
No downstream module needs adaptation, and no target changes meaning.

## Old

The public declarations below did not exist. At their insertion point the existing
module went directly from `matrixLatticeImage` to the main theorem. Its namespace
and universe commands were, verbatim:

```lean
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale
```

## New

Those existing commands are unchanged. Added a closed `section LatticePairImages`
containing private proved helpers and a closed `section Classes`, with these variables:

```lean
variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
  (a : R ⟶ S)
  (L : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
  (U : X.ProEt)
```

The primary new public statement is, verbatim:

```lean
theorem IntegralLatticePair.equivalent_iff_image_eq
    (ha : ∀ T, Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (P Q : IntegralLatticePair a L U) :
    P.Equivalent Q ↔ ∀ T, P.image T = Q.image T
```

Also added `IntegralLatticePair.intertwiningIso_unique` and the specialization
`integralLatticePair_equivalent_iff_image_eq` for the integral coefficient inclusion.
All three are proved and recorded by
`lem-weil-pbc-lattice-pair-image-classification`; none adds an assumption to an
existing declaration. The three added imports are private proof imports.

Also added a closed `section LatticeMatrixImages`, containing private proved
helpers, `open scoped Matrix`, the same scoped elaborator settings, and a closed
`section MatrixImages` with these variables:

```lean
variable (X : Scheme.{u}) (K : Type u) [Field K]
  [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K) (U : X.ProEt) (n : ℕ)
```

Its public additions are `matrixLatticeImage_eq_of_coset_eq`,
`matrixLatticeImage_coset_eq_of_eq`, and `matrixLatticeImage_coset_eq_iff`,
recorded by `lem-weil-pbc-matrix-lattice-coset-invariance`. All are proved.
The forward invariance requires no nonempty hypothesis; the converse explicitly
requires `Nonempty U.left` to evaluate coefficients at a point. These section
commands also close before the unchanged main theorem.

Added a closed `section FreeExtension` with the generic ring sheaves, map and
slice object from `LatticePairImages`, and a finite index type `I`. Its private
helpers explicitly construct the scalar-extension isomorphism. Its proved public
addition `exists_latticeFreeScalarExtensionIso` requires only `[Finite I]` and
normalizes the isomorphism on every basis section. This is recorded by
`lem-weil-pbc-lattice-free-scalar-extension`. Its statement uses only the already
public standard free-sheaf and tensor/sheafification constructions. No arbitrary
object is taken from an unproved existence assertion.

Added closed `ConstantMatrix` and `ConstantPairs` sections. Their private
helpers construct the sectionwise constant matrix action, prove its restriction
compatibility, and prove finite local freeness of the standard integral sheaf.
The only public addition is `exists_matrixIntegralLatticePair`: its statement
uses precisely the existing pair, image and trivialization definitions, with
an explicit proof of the prescribed image formula on every test object.
It is recorded by `lem-weil-pbc-constant-matrix-lattice-pair`. The proof makes
no arbitrary choice from an unproved existence theorem. These sections also
close before the unchanged main theorem.

## Users

The downstream list was checked with `tools/downstream.py`; the new names had no
existing users. Every existing downstream module is listed here for completeness.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LatticeSheafLocallyConstant | F2 | Adds proved coefficient, image, scalar-extension and constant-matrix lemmas; no existing signature changes. |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | E3 | Unchanged; existing declarations and their meanings are identical. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Unchanged; existing declarations and their meanings are identical. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Unchanged; existing declarations and their meanings are identical. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | C4 | Unchanged; existing declarations and their meanings are identical. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Unchanged; existing declarations and their meanings are identical. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged; existing declarations and their meanings are identical. |
| TargetsCheck | unclaimed | Unchanged; existing declarations and their meanings are identical. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged; existing declarations and their meanings are identical. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged; existing declarations and their meanings are identical. |

## Status

landed 20261016T062623-L-449261 2026-10-16 (merge of deliver/F2/Sheaf.Paper.LatticeSheafLocallyConstant)
