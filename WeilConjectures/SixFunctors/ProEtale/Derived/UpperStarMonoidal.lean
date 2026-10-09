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
public import WeilConjectures.SixFunctors.ProEtale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal

/-!
# The derived pullback and the derived tensor product

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal`,
restricted to the tensor comparison of the derived pullback.

Let `g : Z ⟶ Y` be a morphism of schemes. We show that the two bifunctors
`(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, of type
`D(Y_proét) ⥤ D(Y_proét) ⥤ D(Z_proét)`, are
the total left derived functors of `(A, B) ↦ g^*A ⊗ g^*B` and `(A, B) ↦ g^*(A ⊗ B)`
respectively. Deriving the oplax monoidal structure of `g^*`, we obtain the comparison
`Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, which is an isomorphism since `g^*` is strong monoidal.

Since `g^*` is exact, the counit of `Lg^*` is an isomorphism everywhere, so
`Lg^*(K ⊗ᴸ M)` is computed with the K-flat left derivability structure on `K(Y_proét)`.
This does not suffice for `Lg^*K ⊗ᴸ Lg^*M`, since `g^*` need not send K-flat complexes to
K-flat complexes. We use instead, for the second factor, the complexes whose pullback by `g`
is K-flat (`AlgebraicGeometry.ProEtale.kFlatUpperStar`). They contain the functorial flat
resolutions when `g^*` preserves flat sheaves, so they form a left derivability structure by
`HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism`.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.kFlatUpperStar g`: the complexes on `Y_proét` whose pullback by `g`
  is K-flat, and `AlgebraicGeometry.ProEtale.isLeftDerivabilityStructure_kFlatUpperStar`:
  they form a left derivability structure.
- `AlgebraicGeometry.ProEtale.derivedTensorLeftDerivedUpperStar g` and
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarDerivedTensor g`: the bifunctors
  `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` and `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, with the counits
  `AlgebraicGeometry.ProEtale.derivedTensorLeftDerivedUpperStarCounit` and
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarDerivedTensorCounit`.
- `AlgebraicGeometry.ProEtale.isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar`:
  `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` is the total left derived functor of `(A, B) ↦ g^*A ⊗ g^*B`.
- `AlgebraicGeometry.ProEtale.isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor`:
  `(K, M) ↦ Lg^*(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ g^*(A ⊗ B)`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison g`: the comparison
  `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, obtained by deriving the oplax monoidal structure of `g^*`
  with `CategoryTheory.Functor.leftDerived₂NatTrans`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso g`: it is a natural isomorphism,
  with components `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso g K M`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarUnitIso g`: the canonical `Lg^* Λ_Y ≅ Λ_Z`.
- `AlgebraicGeometry.ProEtale.isZero_derivedTensor_obj_obj_of_isZero_left` and
  `AlgebraicGeometry.ProEtale.isZero_derivedTensor_obj_obj_of_isZero_right`: `K ⊗ᴸ M` vanishes
  when `K` or `M` does.

The results depend on `sorryAx` through `AlgebraicGeometry.ProEtale.derivedTensor` and
`AlgebraicGeometry.ProEtale.isLeftDerivedFunctor₂_derivedTensor`.

## TODO

- The statements here are those of the étale file for a different site; both should be
  deduced from a single statement for an exact functor between abelian monoidal categories with
  functorial flat resolutions preserving flat objects.
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

namespace ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The complexes of pro-étale sheaves on `Y` whose pullback by `g : Z ⟶ Y` is K-flat: the
inverse image of the K-flat complexes of `K(Z_proét)` under `g^* : K(Y_proét) ⥤ K(Z_proét)`. -/
abbrev kFlatUpperStar :
    ObjectProperty (HomotopyCategory (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ)) :=
  (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat.inverseImage
    ((g)^*[A].mapHomotopyCategory (.up ℤ))

omit [Abelian.HasFunctorialFlatResolution A] in
/-- The pullbacks of the functorial flat resolutions of complexes of pro-étale sheaves on `Y` are
K-flat. -/
lemma kFlatUpperStar_quotient_obj_resolutionFunctor_obj [ProEtale.UpperStarPreservesFlat A]
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ Sheaf (Scheme.ProEt.topology Y) A))
    [Λ.F.PreservesZeroMorphisms]
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ) :
    kFlatUpperStar A g ((HomotopyCategory.quotient _ _).obj (Λ.resolutionFunctor.obj K)) :=
  (HomotopyCategory.kFlat_quotient_obj_iff _).2
    (kFlat_upperStar_mapHomologicalComplex_obj g
      (Λ.colimitOfShapeFlatResolutionFunctorObj
        ObjectProperty.flat.essImage_ι_le K).colimitsOfShape)

omit [Abelian.HasFunctorialFlatResolution A] in
/-- Given a functorial flat resolution `Λ` of pro-étale sheaves on `Y`, the complexes whose
pullback by `g` is K-flat form a left derivability structure on `K(Y_proét)` for the
quasi-isomorphisms. -/
lemma isLeftDerivabilityStructure_kFlatUpperStar_of_leftResolution
    [ProEtale.UpperStarPreservesFlat A]
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ Sheaf (Scheme.ProEt.topology Y) A)) :
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).IsLeftDerivabilityStructure :=
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ.reduced)

/-- The complexes whose pullback by `g` is K-flat form a left derivability structure on
`K(Y_proét)` for the quasi-isomorphisms. The functorial flat resolution of pro-étale sheaves on `Y`
is given by the instance `Etale.hasFunctorialFlatResolution_sheaf`. -/
instance isLeftDerivabilityStructure_kFlatUpperStar [ProEtale.UpperStarPreservesFlat A] :
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).IsLeftDerivabilityStructure :=
  isLeftDerivabilityStructure_kFlatUpperStar_of_leftResolution A g
    (inferInstance : HasFunctorialFlatResolution (Sheaf (Scheme.ProEt.topology Y) A)).some

section

open DerivedCategory Functor.LaxMonoidal

/-- The bifunctor `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M`, of type `D(Y_proét) ⥤ D(Y_proét) ⥤ D(Z_proét)`. -/
noncomputable abbrev derivedTensorLeftDerivedUpperStar :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) :=
  (((Functor.whiskeringLeft₂ _).obj L((g)^*[A])).obj L((g)^*[A])).obj (-⊗ᴸ-(Z)[A])

/-- The bifunctor `(K, M) ↦ Lg^*(K ⊗ᴸ M)`, of type `D(Y_proét) ⥤ D(Y_proét) ⥤ D(Z_proét)`. -/
noncomputable abbrev leftDerivedUpperStarDerivedTensor :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) :=
  (Functor.postcompose₂.obj L((g)^*[A])).obj (-⊗ᴸ-(Y)[A])

/-- The counit exhibiting `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` as the total left derived functor of
`(A, B) ↦ g^*A ⊗ g^*B`. On `K, M` in `K(Y_proét)` it is the composite
```
 Lg^*(Qh K) ⊗ᴸ Lg^*(Qh M) --(counit ⊗ᴸ 1)--> Qh(g^*K) ⊗ᴸ Lg^*(Qh M)
   --(1 ⊗ᴸ counit)--> Qh(g^*K) ⊗ᴸ Qh(g^*M) --(μ Qh)--> Qh(g^*K ⊗ g^*M)
```
of the counits of `Lg^*` on both factors and the lax monoidal structure of
`Qh : K(Z_proét) ⥤ D(Z_proét)`. -/
noncomputable def derivedTensorLeftDerivedUpperStarCounit :
    (((Functor.whiskeringLeft₂ _).obj (Qh (C := Sheaf (Scheme.ProEt.topology Y) A))).obj Qh).obj
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
`(A, B) ↦ g^*(A ⊗ B)`. On `K, M` in `K(Y_proét)` it is the composite
```
 Lg^*(Qh K ⊗ᴸ Qh M) --(Lg^*(μ Qh))--> Lg^*(Qh (K ⊗ M)) --(counit)--> Qh(g^*(K ⊗ M))
```
of `Lg^*` applied to the lax monoidal structure of `Qh : K(Y_proét) ⥤ D(Y_proét)` and the counit
of `Lg^*`. -/
noncomputable def leftDerivedUpperStarDerivedTensorCounit :
    (((Functor.whiskeringLeft₂ _).obj (Qh (C := Sheaf (Scheme.ProEt.topology Y) A))).obj Qh).obj
        (leftDerivedUpperStarDerivedTensor A g) ⟶
      (Functor.postcompose₂.obj ((g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj
        (curriedTensor _) :=
  (Functor.postcompose₂.obj L((g)^*[A])).map (μNatTrans Qh) ≫
    (Functor.postcompose₂.map (g)^*[A].leftDerivedFunctorCounit).app (curriedTensor _)

variable {A} in
/-- The lax monoidal structure `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)` of `Qh : K(X_proét) ⥤ D(X_proét)` is an
isomorphism when `M` is K-flat. -/
lemma isIso_μNatTrans_Qh_app_app_of_kFlat {X : Scheme.{u}}
    (K M : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ))
    (hM : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat M) :
    IsIso (((μNatTrans (Qh (C := Sheaf (Scheme.ProEt.topology X) A))).app K).app M) := by
  -- Instance search does not find this instance through `-⊗ᴸ-(X)[A]`.
  have : (-⊗ᴸ-(X)[A]).IsLeftDerivedFunctor₂ (μNatTrans Qh)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    isLeftDerivedFunctor₂_derivedTensor A X
  exact (MorphismProperty.id_prod_kFlat_derives_curriedTensor
    (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ))
      Qh).isIso_of_isLeftDerivabilityStructure (LF := -⊗ᴸ-(X)[A]) (μNatTrans Qh) K ⟨_, hM⟩

section

open DerivedCategory ZeroObject

variable {A} in
/-- The derived tensor product `K ⊗ᴸ M` vanishes when `K` does. -/
lemma isZero_derivedTensor_obj_obj_of_isZero_left {X : Scheme.{u}}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : IsZero K)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    IsZero (((-⊗ᴸ-(X)[A]).obj K).obj M) := by
  -- Write `M ≅ Qh M₀` with `M₀` K-flat and `K ≅ Qh 0`; then `K ⊗ᴸ M ≅ Qh (0 ⊗ M₀) = 0`.
  let R : (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A)
      (.up ℤ)).localizerMorphismKFlat.LeftResolution (Qh.objPreimage M) :=
    Classical.arbitrary _
  let eM : Qh.obj R.X₁.obj ≅ M :=
    Localization.isoOfHom Qh (HomotopyCategory.quasiIso _ (.up ℤ)) R.w R.hw ≪≫
      Qh.objObjPreimageIso M
  let Z : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ) :=
    (HomotopyCategory.quotient _ _).obj 0
  have hZ : IsZero Z := Functor.map_isZero _ (isZero_zero _)
  have hZM : IsZero (Z ⊗ R.X₁.obj) := by
    refine IsZero.of_iso ?_
      (Functor.Monoidal.μIso (HomotopyCategory.quotient _ _) 0 R.X₁.obj.as).symm
    have h :
        IsZero ((0 : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ) ⊗ R.X₁.obj.as) := by
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
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hM : IsZero M) :
    IsZero (((-⊗ᴸ-(X)[A]).obj K).obj M) :=
  MonoidalCategory.isZero_tensorObj_of_isZero_right K hM

end

/-- `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` is the total left derived functor of `(A, B) ↦ g^*A ⊗ g^*B`
from `K(Y_proét) × K(Y_proét)` to `D(Z_proét)`. It is computed on pairs `(K, M)` with `K` K-flat and
`g^*M` K-flat. -/
theorem isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
    [ProEtale.UpperStarPreservesFlat A] :
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
from `K(Y_proét) × K(Y_proét)` to `D(Z_proét)`. It is computed on pairs of K-flat complexes. -/
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

variable [ProEtale.UpperStarPreservesFlat A]

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

/-- The comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` of bifunctors,
of type `D(Y_proét) ⥤ D(Y_proét) ⥤ D(Z_proét)`, obtained by deriving the oplax monoidal
structure `δ` of `g^*`. It is the unique natural transformation such that, for `K, M` in
`K(Y_proét)`, the square
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
of type `D(Y_proét) ⥤ D(Y_proét) ⥤ D(Z_proét)`, whose underlying morphism is
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

/-- The isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` in `D(Z_proét)`, for `K, M` in `D(Y_proét)`. -/
noncomputable def leftDerivedUpperStarTensorIso
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    L((g)^*[A]).obj (((-⊗ᴸ-(Y)[A]).obj K).obj M) ≅
      ((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K)).obj (L((g)^*[A]).obj M) :=
  ((leftDerivedUpperStarTensorNatIso A g).app K).app M

@[simp]
lemma leftDerivedUpperStarTensorIso_hom
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (leftDerivedUpperStarTensorIso A g K M).hom =
      ((leftDerivedUpperStarTensorComparison A g).app K).app M :=
  rfl

end

/-- The canonical identification `Lg^* Λ_Y ≅ Λ_Z` of the units.

The unit `Λ_Y` is the image in `D(Y_proét)` of the unit sheaf placed in degree `0`. Since `g^*` is
exact, `Lg^*` is computed by applying `g^*` degreewise, and `g^*` sends the unit sheaf of `Y`
to that of `Z` because it is strong monoidal. -/
noncomputable def leftDerivedUpperStarUnitIso : (L((g)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (leftDerivedUpperStarIsoMapDerivedCategory A g).app _ ≪≫
    ((g)^*[A].mapDerivedCategoryFactors).app _ ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).app _) ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso (Functor.Monoidal.εIso (g)^*[A]).symm)

/-- The derived pullback preserves the unit, `Lg^* Λ_Y ≅ Λ_Z`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarUnitIso`). -/
theorem nonempty_iso_leftDerivedUpperStar_unit :
    Nonempty ((L((g)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) :=
  ⟨leftDerivedUpperStarUnitIso A g⟩

end ProEtale

end AlgebraicGeometry
