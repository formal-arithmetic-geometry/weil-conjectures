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
- `AlgebraicGeometry.Etale.derivedTensorLeftDerivedUpperStarCounit` and
  `AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedTensorCounit`: the counits of the two
  derived bifunctors below.
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
  refine ⟨(HomotopyCategory.kFlat_quotient_obj_iff _).2
    (Λ.kFlat_resolutionFunctor_obj hι K), ?_⟩
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

section

open DerivedCategory Functor.LaxMonoidal

/-- The counit exhibiting `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` as the total left derived functor of
`(A, B) ↦ g^*A ⊗ g^*B`: the counits of `Lg^*` on both factors, followed by the lax monoidal
structure of `Qh : K(Z_ét) ⥤ D(Z_ét)`. -/
noncomputable def derivedTensorLeftDerivedUpperStarCounit :
    (((Functor.whiskeringLeft₂ _).obj (Qh (C := Sheaf Y.smallEtaleTopology A))).obj Qh).obj
        ((((Functor.whiskeringLeft₂ _).obj L((g)^*[A])).obj L((g)^*[A])).obj (-⊗ᴸ-(Z)[A])) ⟶
      (((Functor.whiskeringLeft₂ _).obj ((g)^*[A].mapHomotopyCategory (.up ℤ))).obj
        ((g)^*[A].mapHomotopyCategory (.up ℤ))).obj
          ((Functor.postcompose₂.obj Qh).obj (curriedTensor _)) :=
  (((Functor.whiskeringLeft₂ _).map (g)^*[A].leftDerivedFunctorCounit).app
      (Qh ⋙ L((g)^*[A]))).app (-⊗ᴸ-(Z)[A]) ≫
    (((Functor.whiskeringLeft₂ _).obj ((g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ Qh)).map
      (g)^*[A].leftDerivedFunctorCounit).app (-⊗ᴸ-(Z)[A]) ≫
    (((Functor.whiskeringLeft₂ _).obj ((g)^*[A].mapHomotopyCategory (.up ℤ))).obj
        ((g)^*[A].mapHomotopyCategory (.up ℤ))).map (μNatTrans Qh)

/-- The counit exhibiting `(K, M) ↦ Lg^*(K ⊗ᴸ M)` as the total left derived functor of
`(A, B) ↦ g^*(A ⊗ B)`: `Lg^*` applied to the lax monoidal structure of
`Qh : K(Y_ét) ⥤ D(Y_ét)`, followed by the counit of `Lg^*`. -/
noncomputable def leftDerivedUpperStarDerivedTensorCounit :
    (((Functor.whiskeringLeft₂ _).obj (Qh (C := Sheaf Y.smallEtaleTopology A))).obj Qh).obj
        ((Functor.postcompose₂.obj L((g)^*[A])).obj (-⊗ᴸ-(Y)[A])) ⟶
      (Functor.postcompose₂.obj ((g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj
        (curriedTensor _) :=
  (Functor.postcompose₂.obj L((g)^*[A])).map (μNatTrans Qh) ≫
    (Functor.postcompose₂.map (g)^*[A].leftDerivedFunctorCounit).app (curriedTensor _)

/-- `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` is the total left derived functor of `(A, B) ↦ g^*A ⊗ g^*B`
from `K(Y_ét) × K(Y_ét)` to `D(Z_ét)`. -/
theorem isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar :
    ((((Functor.whiskeringLeft₂ _).obj L((g)^*[A])).obj L((g)^*[A])).obj
      (-⊗ᴸ-(Z)[A])).IsLeftDerivedFunctor₂ (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g))
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)) _ (fun X₁ X₂ ↦ ?_)
  have := isLeftDerivedFunctor₂_derivedTensor A Z
  have := (MorphismProperty.id_prod_kFlat_derives_curriedTensor
    (HomotopyCategory.quasiIso (Sheaf Z.smallEtaleTopology A) (.up ℤ))
      Qh).isIso_of_isLeftDerivabilityStructure (LF := -⊗ᴸ-(Z)[A]) (μNatTrans Qh)
    (((g)^*[A].mapHomotopyCategory _).obj X₁.obj) ⟨_, X₂.property.2⟩
  simp only [derivedTensorLeftDerivedUpperStarCounit, NatTrans.comp_app]
  refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance ?_)
  exact this

/-- `(K, M) ↦ Lg^*(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ g^*(A ⊗ B)`
from `K(Y_ét) × K(Y_ét)` to `D(Z_ét)`. -/
theorem isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor :
    ((Functor.postcompose₂.obj L((g)^*[A])).obj (-⊗ᴸ-(Y)[A])).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarDerivedTensorCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g))
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)) _ (fun X₁ X₂ ↦ ?_)
  have := isLeftDerivedFunctor₂_derivedTensor A Y
  have := (MorphismProperty.id_prod_kFlat_derives_curriedTensor
    (HomotopyCategory.quasiIso (Sheaf Y.smallEtaleTopology A) (.up ℤ))
      Qh).isIso_of_isLeftDerivabilityStructure (LF := -⊗ᴸ-(Y)[A]) (μNatTrans Qh) X₁.obj
        ⟨_, X₂.property.1⟩
  have : IsIso (((μNatTrans Qh).app X₁.obj).app X₂.obj) := this
  simp only [leftDerivedUpperStarDerivedTensorCounit, NatTrans.comp_app]
  refine IsIso.comp_isIso' ?_ inferInstance
  exact Functor.map_isIso L((g)^*[A]) (((μNatTrans Qh).app X₁.obj).app X₂.obj)

end

end Etale

end AlgebraicGeometry
