/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat

/-!
# The derived pullback and the derived tensor product

Let `g : Z ⟶ Y` be a morphism of schemes. We show that the two bifunctors
`(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)` from `D(Y_ét)` to `D(Z_ét)` are
the total left derived functors of `(A, B) ↦ g^*A ⊗ g^*B` and `(A, B) ↦ g^*(A ⊗ B)`
respectively. They will be compared by deriving the oplax monoidal structure of `g^*`.

Since `g^*` is exact, the counit of `Lg^*` is an isomorphism everywhere, so
`Lg^*(K ⊗ᴸ M)` is computed with the K-flat left derivability structure on `K(Y_ét)`.
This does not suffice for `Lg^*K ⊗ᴸ Lg^*M`, since `g^*` need not send K-flat complexes to
K-flat complexes. We use instead, for the second factor, the complexes whose pullback by `g`
is K-flat (`AlgebraicGeometry.Etale.kFlatUpperStar`). They contain the functorial flat
resolutions when `g^*` preserves flat sheaves, so they form a left derivability structure by
`HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism`.

## Main definitions and results

- `AlgebraicGeometry.Etale.kFlatUpperStar g`: the complexes on `Y_ét` whose pullback by `g`
  is K-flat, and `AlgebraicGeometry.Etale.isLeftDerivabilityStructure_kFlatUpperStar`:
  they form a left derivability structure.
- `AlgebraicGeometry.Etale.derivedTensorLeftDerivedUpperStar g` and
  `AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedTensor g`: the bifunctors
  `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, with the counits
  `AlgebraicGeometry.Etale.derivedTensorLeftDerivedUpperStarCounit` and
  `AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedTensorCounit`.
- `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar`:
  `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` is the total left derived functor of `(A, B) ↦ g^*A ⊗ g^*B`.
- `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor`:
  `(K, M) ↦ Lg^*(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ g^*(A ⊗ B)`.

## TODO

Nothing here is specific to étale sheaves: the same statements hold for an exact functor
`F` between abelian monoidal categories with functorial flat resolutions, `F` preserving flat
objects. They should be proved in that generality and specialised here.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The complexes of étale sheaves on `Y` whose pullback by `g : Z ⟶ Y` is K-flat: the
inverse image of the K-flat complexes of `K(Z_ét)` under `g^* : K(Y_ét) ⥤ K(Z_ét)`. -/
abbrev kFlatUpperStar :
    ObjectProperty (HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :=
  (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat.inverseImage
    ((g)^*[A].mapHomotopyCategory (.up ℤ))

omit [Abelian.HasFunctorialFlatResolution A] in
/-- The pullbacks of the functorial flat resolutions of complexes of étale sheaves on `Y` are
K-flat. -/
lemma kFlatUpperStar_quotient_obj_resolutionFunctor_obj [Etale.UpperStarPreservesFlat A]
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ Sheaf Y.smallEtaleTopology A))
    [Λ.F.PreservesZeroMorphisms]
    (K : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ) :
    kFlatUpperStar A g ((HomotopyCategory.quotient _ _).obj (Λ.resolutionFunctor.obj K)) :=
  (HomotopyCategory.kFlat_quotient_obj_iff _).2
    (kFlat_upperStar_mapHomologicalComplex_obj g
      (Λ.colimitOfShapeFlatResolutionFunctorObj
        ObjectProperty.flat.essImage_ι_le K).colimitsOfShape)

omit [Abelian.HasFunctorialFlatResolution A] in
/-- Given a functorial flat resolution `Λ` of étale sheaves on `Y`, the complexes whose
pullback by `g` is K-flat form a left derivability structure on `K(Y_ét)` for the
quasi-isomorphisms. -/
lemma isLeftDerivabilityStructure_kFlatUpperStar_of_leftResolution
    [Etale.UpperStarPreservesFlat A]
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ Sheaf Y.smallEtaleTopology A)) :
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).IsLeftDerivabilityStructure :=
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ.reduced)

/-- The complexes whose pullback by `g` is K-flat form a left derivability structure on
`K(Y_ét)` for the quasi-isomorphisms. The functorial flat resolution of étale sheaves on `Y`
is given by the instance `Etale.hasFunctorialFlatResolution_sheaf`. -/
instance isLeftDerivabilityStructure_kFlatUpperStar [Etale.UpperStarPreservesFlat A] :
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).IsLeftDerivabilityStructure :=
  isLeftDerivabilityStructure_kFlatUpperStar_of_leftResolution A g
    (‹HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A)›.some)

section

open DerivedCategory Functor.LaxMonoidal

/-- The bifunctor `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` from `D(Y_ét)` to `D(Z_ét)`. -/
noncomputable abbrev derivedTensorLeftDerivedUpperStar :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  (((Functor.whiskeringLeft₂ _).obj L((g)^*[A])).obj L((g)^*[A])).obj (-⊗ᴸ-(Z)[A])

/-- The bifunctor `(K, M) ↦ Lg^*(K ⊗ᴸ M)` from `D(Y_ét)` to `D(Z_ét)`. -/
noncomputable abbrev leftDerivedUpperStarDerivedTensor :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  (Functor.postcompose₂.obj L((g)^*[A])).obj (-⊗ᴸ-(Y)[A])

/-- The counit exhibiting `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` as the total left derived functor of
`(A, B) ↦ g^*A ⊗ g^*B`. On `K, M` in `K(Y_ét)` it is the composite
```
 Lg^*(Qh K) ⊗ᴸ Lg^*(Qh M) --(counit ⊗ᴸ 1)--> Qh(g^*K) ⊗ᴸ Lg^*(Qh M)
   --(1 ⊗ᴸ counit)--> Qh(g^*K) ⊗ᴸ Qh(g^*M) --(μ Qh)--> Qh(g^*K ⊗ g^*M)
```
of the counits of `Lg^*` on both factors and the lax monoidal structure of
`Qh : K(Z_ét) ⥤ D(Z_ét)`. -/
noncomputable def derivedTensorLeftDerivedUpperStarCounit :
    (((Functor.whiskeringLeft₂ _).obj (Qh (C := Sheaf Y.smallEtaleTopology A))).obj Qh).obj
        (derivedTensorLeftDerivedUpperStar A g) ⟶
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
`(A, B) ↦ g^*(A ⊗ B)`. On `K, M` in `K(Y_ét)` it is the composite
```
 Lg^*(Qh K ⊗ᴸ Qh M) --(Lg^*(μ Qh))--> Lg^*(Qh (K ⊗ M)) --(counit)--> Qh(g^*(K ⊗ M))
```
of `Lg^*` applied to the lax monoidal structure of `Qh : K(Y_ét) ⥤ D(Y_ét)` and the counit
of `Lg^*`. -/
noncomputable def leftDerivedUpperStarDerivedTensorCounit :
    (((Functor.whiskeringLeft₂ _).obj (Qh (C := Sheaf Y.smallEtaleTopology A))).obj Qh).obj
        (leftDerivedUpperStarDerivedTensor A g) ⟶
      (Functor.postcompose₂.obj ((g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj
        (curriedTensor _) :=
  (Functor.postcompose₂.obj L((g)^*[A])).map (μNatTrans Qh) ≫
    (Functor.postcompose₂.map (g)^*[A].leftDerivedFunctorCounit).app (curriedTensor _)

variable {A} in
/-- The lax monoidal structure `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)` of `Qh : K(X_ét) ⥤ D(X_ét)` is an
isomorphism when `M` is K-flat. -/
lemma isIso_μNatTrans_Qh_app_app_of_kFlat {X : Scheme.{u}}
    (K M : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ))
    (hM : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat M) :
    IsIso (((μNatTrans (Qh (C := Sheaf X.smallEtaleTopology A))).app K).app M) := by
  -- Instance search does not find this instance through `-⊗ᴸ-(X)[A]`.
  have : (-⊗ᴸ-(X)[A]).IsLeftDerivedFunctor₂ (μNatTrans Qh)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    isLeftDerivedFunctor₂_derivedTensor A X
  exact (MorphismProperty.id_prod_kFlat_derives_curriedTensor
    (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (.up ℤ))
      Qh).isIso_of_isLeftDerivabilityStructure (LF := -⊗ᴸ-(X)[A]) (μNatTrans Qh) K ⟨_, hM⟩

/-- `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` is the total left derived functor of `(A, B) ↦ g^*A ⊗ g^*B`
from `K(Y_ét) × K(Y_ét)` to `D(Z_ét)`. It is computed on pairs `(K, M)` with `K` K-flat and
`g^*M` K-flat. -/
theorem isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
    [Etale.UpperStarPreservesFlat A] :
    (derivedTensorLeftDerivedUpperStar A g).IsLeftDerivedFunctor₂
      (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)) _ (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat
    (((g)^*[A].mapHomotopyCategory _).obj X₁.obj) _ X₂.property
  simp only [derivedTensorLeftDerivedUpperStarCounit, NatTrans.comp_app]
  infer_instance

/-- `(K, M) ↦ Lg^*(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ g^*(A ⊗ B)`
from `K(Y_ét) × K(Y_ét)` to `D(Z_ét)`. It is computed on pairs of K-flat complexes. -/
theorem isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor :
    (leftDerivedUpperStarDerivedTensor A g).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarDerivedTensorCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat X₁.obj _ X₂.property
  simp only [leftDerivedUpperStarDerivedTensorCounit, NatTrans.comp_app]
  infer_instance

end

end Etale

end AlgebraicGeometry
