/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# The derived pullback and the derived tensor product

Let `g : Z ⟶ Y` be a morphism of schemes. We show that the two bifunctors
`(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, of type
`D(Y_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`, are
the total left derived functors of `(A, B) ↦ g^*A ⊗ g^*B` and `(A, B) ↦ g^*(A ⊗ B)`
respectively. Deriving the oplax monoidal structure of `g^*`, we obtain the comparison
`Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, which is an isomorphism since `g^*` is strong monoidal.

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
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison g`: the comparison
  `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, obtained by deriving the oplax monoidal structure of `g^*`
  with `CategoryTheory.Functor.leftDerived₂NatTrans`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso g`: it is a natural isomorphism,
  with components `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso g K M`, and
  `AlgebraicGeometry.Etale.derivedTensorRightCompLeftDerivedUpperStarIso g M`, the same for
  fixed `M` as an isomorphism of functors of `K`.
- `AlgebraicGeometry.Etale.derivedTensorRightPullback g`: tensoring with a complex pulled
  back along `g`, `N ↦ (K ↦ K ⊗ᴸ g^* N)`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso g`: the canonical `Lg^* Λ_Y ≅ Λ_Z`.
- `AlgebraicGeometry.Etale.nonempty_monoidal_leftDerivedUpperStar`: `Lg^*` is a monoidal
  functor (currently `sorry`, see the TODO below).
- `AlgebraicGeometry.Etale.isZero_derivedTensor_obj_obj_of_isZero_left` and
  `AlgebraicGeometry.Etale.isZero_derivedTensor_obj_obj_of_isZero_right`: `K ⊗ᴸ M` vanishes
  when `K` or `M` does.

The results depend on `sorryAx` through `AlgebraicGeometry.Etale.derivedTensor` and
`AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor`.

## TODO

- Nothing here is specific to étale sheaves: the same statements hold for an exact functor
  `F` between abelian monoidal categories with functorial flat resolutions, `F` preserving flat
  objects. They should be proved in that generality and specialised here. This includes the
  comparison `leftDerivedUpperStarTensorComparison`, which only uses the oplax monoidal
  structure of `F`, and `leftDerivedUpperStarTensorNatIso`, which uses that `F` is strong
  monoidal.
- The comparison should be the `δ` of an oplax (in fact strong) monoidal structure
  `Functor.OplaxMonoidal L(g^*)`, together with the unit comparison `Lg^*(𝟙_) ⟶ 𝟙_` and the
  coherence axioms, with respect to the monoidal structure on derived categories. This needs
  `-⊗ᴸ-(X)[A]` to agree with the tensor product of that monoidal structure.
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
lemma kFlatUpperStar_quotient_obj_resolutionFunctor_obj [(g)^*[A].PreservesFlat]
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
    [(g)^*[A].PreservesFlat]
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ Sheaf Y.smallEtaleTopology A)) :
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).IsLeftDerivabilityStructure :=
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ.reduced)

/-- The complexes whose pullback by `g` is K-flat form a left derivability structure on
`K(Y_ét)` for the quasi-isomorphisms. The functorial flat resolution of étale sheaves on `Y`
is given by the instance `Etale.hasFunctorialFlatResolution_sheaf`. -/
instance isLeftDerivabilityStructure_kFlatUpperStar [(g)^*[A].PreservesFlat] :
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).IsLeftDerivabilityStructure :=
  isLeftDerivabilityStructure_kFlatUpperStar_of_leftResolution A g
    (inferInstance : HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A)).some

section

open DerivedCategory Functor.LaxMonoidal

/-- The bifunctor `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M`, of type `D(Y_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`. -/
noncomputable abbrev derivedTensorLeftDerivedUpperStar :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  (((Functor.whiskeringLeft₂ _).obj L((g)^*[A])).obj L((g)^*[A])).obj (-⊗ᴸ-(Z)[A])

/-- The bifunctor `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, of type `D(Y_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`. -/
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

section

open DerivedCategory ZeroObject

variable {A} in
/-- The derived tensor product `K ⊗ᴸ M` vanishes when `K` does. -/
lemma isZero_derivedTensor_obj_obj_of_isZero_left {X : Scheme.{u}}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsZero K)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsZero (((-⊗ᴸ-(X)[A]).obj K).obj M) := by
  -- Write `M ≅ Qh M₀` with `M₀` K-flat and `K ≅ Qh 0`; then `K ⊗ᴸ M ≅ Qh (0 ⊗ M₀) = 0`.
  let R : (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A)
      (.up ℤ)).localizerMorphismKFlat.LeftResolution (Qh.objPreimage M) :=
    Classical.arbitrary _
  let eM : Qh.obj R.X₁.obj ≅ M :=
    Localization.isoOfHom Qh (HomotopyCategory.quasiIso _ (.up ℤ)) R.w R.hw ≪≫
      Qh.objObjPreimageIso M
  let Z : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ) :=
    (HomotopyCategory.quotient _ _).obj 0
  have hZ : IsZero Z := Functor.map_isZero _ (isZero_zero _)
  have hZM : IsZero (Z ⊗ R.X₁.obj) := by
    refine IsZero.of_iso ?_
      (Functor.Monoidal.μIso (HomotopyCategory.quotient _ _) 0 R.X₁.obj.as).symm
    have h :
        IsZero ((0 : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) ⊗ R.X₁.obj.as) := by
      rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, (isZero_zero _).eq_of_src (𝟙 _) 0,
        MonoidalPreadditive.zero_whiskerRight]
    exact Functor.map_isZero (HomotopyCategory.quotient _ _) h
  have := isIso_μNatTrans_Qh_app_app_of_kFlat Z R.X₁.obj R.X₁.property
  refine (Functor.map_isZero Qh hZM).of_iso ?_
  exact ((-⊗ᴸ-(X)[A]).mapIso (hK.iso (Functor.map_isZero Qh hZ))).app M ≪≫
    ((-⊗ᴸ-(X)[A]).obj _).mapIso eM.symm ≪≫
    asIso (((Functor.LaxMonoidal.μNatTrans Qh).app Z).app R.X₁.obj)

variable {A} in
/-- The derived tensor product `K ⊗ᴸ M` vanishes when `M` does. -/
lemma isZero_derivedTensor_obj_obj_of_isZero_right {X : Scheme.{u}}
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M : DerivedCategory (Sheaf X.smallEtaleTopology A)} (hM : IsZero M) :
    IsZero (((-⊗ᴸ-(X)[A]).obj K).obj M) :=
  MonoidalCategory.isZero_tensorObj_of_isZero_right K hM

end

/-- `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` is the total left derived functor of `(A, B) ↦ g^*A ⊗ g^*B`
from `K(Y_ét) × K(Y_ét)` to `D(Z_ét)`. It is computed on pairs `(K, M)` with `K` K-flat and
`g^*M` K-flat. -/
theorem isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
    [(g)^*[A].PreservesFlat] :
    (derivedTensorLeftDerivedUpperStar A g).IsLeftDerivedFunctor₂
      (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)) _ (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat
    (((g)^*[A].mapHomotopyCategory _).obj X₁.obj) _ X₂.property
  simp only [derivedTensorLeftDerivedUpperStarCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance this)

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
  -- Instance search times out on `IsIso (L(g^*).map _)`, since the objects in the goal are
  -- only defeq to `X₁.obj` and `X₂.obj`; so the morphism is given explicitly.
  exact IsIso.comp_isIso'
    (Functor.map_isIso L((g)^*[A]) (((μNatTrans Qh).app X₁.obj).app X₂.obj)) inferInstance

end

section

open DerivedCategory Functor.OplaxMonoidal

variable [(g)^*[A].PreservesFlat]

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

/-- The comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` of bifunctors,
of type `D(Y_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`, obtained by deriving the oplax monoidal structure `δ`
of `g^*`. It is the unique natural transformation such that, for `K, M` in `K(Y_ét)`, the square
```
  Lg^*(Qh K ⊗ᴸ Qh M) ──comparison──▶ Lg^*(Qh K) ⊗ᴸ Lg^*(Qh M)
          │                                    │
          │ Lg^*(μ Qh) ≫ counit                │ derivedTensorLeftDerivedUpperStarCounit
          ▼                                    ▼
   Qh(g^*(K ⊗ M)) ─────────Qh(δ g^*)──────▶ Qh(g^*K ⊗ g^*M)
```
commutes, the left vertical arrow being `leftDerivedUpperStarDerivedTensorCounit`. -/
noncomputable def leftDerivedUpperStarTensorComparison :
    leftDerivedUpperStarDerivedTensor A g ⟶ derivedTensorLeftDerivedUpperStar A g :=
  Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh)

/-- The natural isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` of bifunctors,
of type `D(Y_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`, whose underlying morphism is
`leftDerivedUpperStarTensorComparison`. -/
noncomputable def leftDerivedUpperStarTensorNatIso :
    leftDerivedUpperStarDerivedTensor A g ≅ derivedTensorLeftDerivedUpperStar A g :=
  -- `δ` is an isomorphism since `g^*` is strong monoidal.
  Functor.leftDerived₂NatIso _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (asIso (Functor.postcompose₂MapWhiskeringLeft₂
      (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh))

@[simp]
lemma leftDerivedUpperStarTensorNatIso_hom :
    (leftDerivedUpperStarTensorNatIso A g).hom = leftDerivedUpperStarTensorComparison A g :=
  rfl

/-- The comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` is an isomorphism. -/
instance isIso_leftDerivedUpperStarTensorComparison :
    IsIso (leftDerivedUpperStarTensorComparison A g) :=
  (leftDerivedUpperStarTensorNatIso A g).isIso_hom

/-- The isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` in `D(Z_ét)`, for `K, M` in `D(Y_ét)`. -/
noncomputable def leftDerivedUpperStarTensorIso
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).obj (((-⊗ᴸ-(Y)[A]).obj K).obj M) ≅
      ((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K)).obj (L((g)^*[A]).obj M) :=
  ((leftDerivedUpperStarTensorNatIso A g).app K).app M

@[simp]
lemma leftDerivedUpperStarTensorIso_hom
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarTensorIso A g K M).hom =
      ((leftDerivedUpperStarTensorComparison A g).app K).app M :=
  rfl

/-- For a fixed complex `M` on `Y`, the derived pullback commutes with tensoring by `M`:
`Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M`, naturally in `K`. That is, it compares the two functors
`K ↦ Lg^*(K ⊗ᴸ M)` and `K ↦ Lg^*K ⊗ᴸ Lg^*M` from `D(Y_ét)` to `D(Z_ét)`. This is
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso` with its second variable fixed. -/
noncomputable def derivedTensorRightCompLeftDerivedUpperStarIso
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    derivedTensorRight A Y M ⋙ L((g)^*[A]) ≅
      L((g)^*[A]) ⋙ derivedTensorRight A Z (L((g)^*[A]).obj M) :=
  NatIso.ofComponents (fun K ↦ leftDerivedUpperStarTensorIso A g K M) fun φ ↦
    NatTrans.congr_app ((leftDerivedUpperStarTensorNatIso A g).hom.naturality φ) M

end

/-- Tensoring with a complex pulled back along `g : Z ⟶ Y`, as a functor of the complex
downstairs: `N ↦ (K ↦ K ⊗ᴸ g^* N)`. -/
noncomputable def derivedTensorRightPullback :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  D((g)^*[A]) ⋙ derivedTensorRightFunctor A Z

/-- The canonical identification `Lg^* Λ_Y ≅ Λ_Z` of the units, the unit comparison asked for
in the TODO above.

The unit `Λ_Y` is the image in `D(Y_ét)` of the unit sheaf placed in degree `0`. Since `g^*` is
exact, `Lg^*` is computed by applying `g^*` degreewise, and `g^*` sends the unit sheaf of `Y`
to that of `Z` because it is strong monoidal. -/
noncomputable def leftDerivedUpperStarUnitIso : (L((g)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (leftDerivedUpperStarIsoMapDerivedCategory A g).app _ ≪≫
    ((g)^*[A].mapDerivedCategoryFactors).app _ ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).app _) ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso (Functor.Monoidal.εIso (g)^*[A]).symm)

/-- The derived pullback preserves the unit, `Lg^* Λ_Y ≅ Λ_Z`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`). -/
theorem nonempty_iso_leftDerivedUpperStar_unit :
    Nonempty ((L((g)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) :=
  ⟨leftDerivedUpperStarUnitIso A g⟩

/-- The derived pullback `Lg^* : D(Y_ét) ⥤ D(Z_ét)` is a monoidal functor for the derived tensor
products. This is the monoidality of derived pullback in blueprint
`def-weil-derived-pullback-tensor-hom` (within `sk-def-sf-operations`).

The structure isomorphisms are `leftDerivedUpperStarTensorIso` and the unit comparison of
`nonempty_iso_leftDerivedUpperStar_unit`; what is missing is their compatibility with the
associators and unitors of the derived tensor products, see the TODO in the module docstring. -/
theorem nonempty_monoidal_leftDerivedUpperStar [Etale.UpperStarPreservesFlat A] :
    Nonempty (L((g)^*[A])).Monoidal :=
  sorry

end Etale

end AlgebraicGeometry
