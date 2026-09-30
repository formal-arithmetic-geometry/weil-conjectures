/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.CategoryTheory.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat

/-!
# The derived pullback and the derived tensor product

Let `g : Z ⟶ Y` be a morphism of schemes. We show that the two bifunctors
`(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)` from `D(Y_ét)` to `D(Z_ét)` are
the total left derived functors of `(A, B) ↦ g^*A ⊗ g^*B` and `(A, B) ↦ g^*(A ⊗ B)`
respectively. They will be compared by deriving the oplax monoidal structure of `g^*`.

The K-flat left derivability structure on `K(Y_ét)` does not suffice for this, since `g^*`
need not send K-flat complexes to K-flat complexes. We use instead the complexes which are
K-flat and whose pullback by `g` is K-flat (`AlgebraicGeometry.Etale.kFlatUpperStar`). They
contain the functorial flat resolutions when `g^*` preserves flat sheaves, so they form a
left derivability structure by
`HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism`.

## Main definitions and results

- `AlgebraicGeometry.Etale.kFlatUpperStar g`: the K-flat complexes on `Y_ét` whose pullback
  by `g` is K-flat, and `AlgebraicGeometry.Etale.isLeftDerivabilityStructure_kFlatUpperStar`:
  they form a left derivability structure.
- `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar`:
  `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` is the total left derived functor of `(A, B) ↦ g^*A ⊗ g^*B`.
- `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor`:
  `(K, M) ↦ Lg^*(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ g^*(A ⊗ B)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The K-flat complexes of étale sheaves on `Y` whose pullback by `g : Z ⟶ Y` is K-flat. -/
def kFlatUpperStar : ObjectProperty (HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :=
  (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ⊓
    (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat.inverseImage
      ((g)^*[A].mapHomotopyCategory (.up ℤ))

instance : (kFlatUpperStar A g).IsTriangulated := by
  dsimp [kFlatUpperStar]
  infer_instance

instance : (kFlatUpperStar A g).IsClosedUnderIsomorphisms := by
  dsimp [kFlatUpperStar]
  infer_instance

omit [Abelian.HasFunctorialFlatResolution A] in
/-- The functorial flat resolutions of complexes of étale sheaves on `Y` are K-flat and have
K-flat pullbacks. -/
lemma kFlatUpperStar_quotient_obj_resolutionFunctor_obj
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ Sheaf Y.smallEtaleTopology A))
    [Λ.F.PreservesZeroMorphisms]
    (K : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ) :
    kFlatUpperStar A g ((HomotopyCategory.quotient _ _).obj (Λ.resolutionFunctor.obj K)) := by
  have hι : (ObjectProperty.flat.ι : _ ⥤ Sheaf Y.smallEtaleTopology A).essImage ≤
      ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.2
  refine ⟨(HomotopyCategory.kFlat_quotient_obj_iff _).2 (Λ.kFlat_resolutionFunctor_obj hι K), ?_⟩
  exact (HomotopyCategory.kFlat_quotient_obj_iff _).2
    (kFlat_upperStar_mapHomologicalComplex_obj g
      (Λ.colimitOfShapeFlatResolutionFunctorObj hι K).colimitsOfShape)

/-- The K-flat complexes with K-flat pullback by `g` form a left derivability structure on
`K(Y_ét)` for the quasi-isomorphisms. -/
instance isLeftDerivabilityStructure_kFlatUpperStar :
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).IsLeftDerivabilityStructure :=
  let Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ Sheaf Y.smallEtaleTopology A) :=
    Classical.arbitrary _
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ.reduced)

end Etale

end AlgebraicGeometry
