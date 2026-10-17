/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.InjectiveHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.UnitIsoBijective
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The trace isomorphism over a separably closed field: the point computations

Let `k` be a separably closed field, `s = Spec k` and `a : X ⟶ s` with `X` connected. This file
contains the two inputs of the trace isomorphism that are computations in the point category
`D(s_ét, Λ)`:

* `AlgebraicGeometry.Etale.bijective_comp_unit_rightDerivedLowerStar`: for a self-injective
  coefficient ring `Λ`, evaluation at the class `1 ∈ H⁰(X, Λ)`,
  `Hom(Ra_* Λ_X, Λ_s) ⟶ Hom(Λ_s, Λ_s)`, is bijective. This is `H⁰(X, Λ) = Λ` for the connected
  `X` together with `Ext^{>0}_Λ(-, Λ) = 0`.
* `AlgebraicGeometry.Etale.TateOrientation.bijective_untwistedTraceMap_of_bijective_traceMap`:
  over `s` the Tate twists are trivial, so the untwisted trace is bijective as soon as the
  twisted one is.

## Implementation notes

The elimination of the twists is first stated for a general coefficient category `A`, in terms
of `AlgebraicGeometry.Etale.derivedTensor` and its structure isomorphisms
(`AlgebraicGeometry.Etale.bijective_comp_derivedTensor_untwist`), and then specialised to
`A = ModuleCat Λ`: there the monoidal instance on `D(X_ét)` found by instance search is a term
which the kernel cannot compare with the one inside `derivedTensor` in reasonable time (see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- `CategoryTheory.MonoidalCategory.bijective_comp_untwist` in `D(X_ét)`, written with the
derived tensor product `AlgebraicGeometry.Etale.derivedTensor` and its structure isomorphisms:
for `c : Λ_X ≅ B ⊗ᴸ C` with `B ≅ Λ_X`, `C ≅ Λ_X`, an isomorphism `θ : M ⊗ᴸ B ⟶ N` and
`t : N ⟶ Λ_X` such that `y ↦ y ≫ t` is bijective on `Hom(Λ_X, N)`, the untwisted map
`M ⟶ C` built from `θ ≫ t` induces a bijection `Hom(Λ_X, M) ≃ Hom(Λ_X, C)`. -/
lemma bijective_comp_derivedTensor_untwist
    {M B C N : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (c : 𝟙_ _ ≅ ((derivedTensor A X).obj B).obj C) (eB : B ≅ 𝟙_ _) (eC : C ≅ 𝟙_ _)
    (θ : ((derivedTensor A X).obj M).obj B ⟶ N) [IsIso θ] (t : N ⟶ 𝟙_ _)
    (h : Function.Bijective (fun y : 𝟙_ _ ⟶ N ↦ y ≫ t)) :
    Function.Bijective (fun x : 𝟙_ _ ⟶ M ↦ x ≫ (derivedTensorRightUnitor A X M).inv ≫
      ((derivedTensor A X).obj M).map c.hom ≫ (derivedTensorAssociator A X M B C).inv ≫
        ((derivedTensor A X).map (θ ≫ t)).app C ≫ (derivedTensorLeftUnitor A X C).hom) :=
  bijective_comp_untwist c eB eC θ t h

end General

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

omit [IsSepClosed k] in
/-- For `a : X ⟶ s` with `X` connected, `g ↦ e⁻¹ ≫ La^* g ≫ e` is a bijection
`End(Λ_s) ≃ End(Λ_X)` for any `e : La^* Λ_s ≅ Λ_X`: both endomorphism rings are `Λ`, by
`r ↦ r • 𝟙`, and `La^*` is `Λ`-linear. -/
theorem bijective_leftDerivedUpperStar_map_comp {X : Scheme.{u}} [ConnectedSpace X]
    (a : X ⟶ Spec (.of k)) (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _) :
    Function.Bijective (fun g : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _ ↦
      (L((a)^*[ModuleCat.{u + 1} Λ])).map g ≫ e.hom) := by
  have hs := bijective_smul_id_unit Λ (Spec (.of k))
  have hX := bijective_smul_id_unit Λ X
  have h : ((fun z ↦ e.inv ≫ z ≫ (Iso.refl _).hom) ∘
      (fun g : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _ ↦
        (L((a)^*[ModuleCat.{u + 1} Λ])).map g ≫ e.hom)) ∘ (fun r : Λ ↦ r • 𝟙 (𝟙_ _)) =
      fun r : Λ ↦ r • 𝟙 (𝟙_ (DerivedCategoryModule Λ X)) := by
    funext r
    simp
  rw [← h] at hX
  exact ((bijective_conj e.symm (Iso.refl _)).of_comp_iff' _).1
    ((Function.Bijective.of_comp_iff _ hs).1 hX)

omit [IsSepClosed k] in
/-- For any morphism `a : X ⟶ Y`, `Ra_* Λ_X` lies in degrees `≥ 0`. -/
lemma isGE_rightDerivedLowerStar_obj_unit {X Y : Scheme.{u}} (a : X ⟶ Y) :
    ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ (DerivedCategoryModule Λ X))).IsGE 0 := by
  have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor ((a)_*[ModuleCat.{u + 1} Λ])
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((R((a)_*[ModuleCat.{u + 1} Λ])).mapIso (unitIsoSingleFunctorConstantSheaf Λ X)).symm 0

omit [IsSepClosed k] in
/-- For `a : X ⟶ s` with `X` connected and `e : La^* Λ_s ≅ Λ_X`, composition with the class
`u : Λ_s ⟶ Ra_* Λ_X` of `1 ∈ H⁰(X, Λ)` is a bijection `End(Λ_s) ≃ Hom(Λ_s, Ra_* Λ_X)`: it is
`AlgebraicGeometry.Etale.bijective_leftDerivedUpperStar_map_comp` read through `La^* ⊣ Ra_*`. -/
lemma bijective_comp_unit_comp_rightDerivedLowerStar_map {X : Scheme.{u}} [ConnectedSpace X]
    (a : X ⟶ Spec (.of k)) (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _) :
    Function.Bijective (fun g : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _ ↦
      g ≫ (derivedUpperStarLowerStarAdjunction _ a).unit.app (𝟙_ _) ≫
        (R((a)_*[ModuleCat.{u + 1} Λ])).map e.hom) := by
  have : (fun g : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _ ↦
      g ≫ (derivedUpperStarLowerStarAdjunction _ a).unit.app (𝟙_ _) ≫
        (R((a)_*[ModuleCat.{u + 1} Λ])).map e.hom) =
      (derivedUpperStarLowerStarAdjunction _ a).homEquiv _ _ ∘
        (fun g ↦ (L((a)^*[ModuleCat.{u + 1} Λ])).map g ≫ e.hom) := by
    funext g
    simp [Adjunction.homEquiv_unit]
  rw [this]
  exact (Equiv.bijective _).comp (bijective_leftDerivedUpperStar_map_comp a e)

/-- **Evaluation at `1` is bijective.** Let `k` be separably closed, `Λ` self-injective, and
`a : X ⟶ Spec k` with `X` connected. For an identification `e : La^* Λ_s ≅ Λ_X`, let
`u : Λ_s ⟶ Ra_* Λ_X` be the class `1 ∈ H⁰(X, Λ)` (the unit of `La^* ⊣ Ra_*` read through `e`).
Then `h ↦ u ≫ h`, `Hom(Ra_* Λ_X, Λ_s) ⟶ Hom(Λ_s, Λ_s)`, is bijective.

Indeed `Ra_* Λ_X ∈ D^{≥ 0}`, and `Hom(Λ_s, u)` is bijective since `H⁰(X, Λ) = Λ` for the connected
`X` (`AlgebraicGeometry.Etale.bijective_comp_unit_comp_rightDerivedLowerStar_map`), so the cone of
`u` lies in `D^{≥ 1}` (`AlgebraicGeometry.Etale.isGE_one_of_bijective_comp_of_isSepClosed`); and
`Λ_s` is an injective sheaf, so it has no morphisms from `D^{≥ 1}` and its shift
(`DerivedCategory.bijective_comp_singleFunctor_of_injective_of_isGE`). -/
theorem bijective_comp_unit_rightDerivedLowerStar [Module.Injective Λ Λ] {X : Scheme.{u}}
    [ConnectedSpace X] (a : X ⟶ Spec (.of k))
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _) :
    Function.Bijective (fun h : (R((a)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ⟶ 𝟙_ _ ↦
      ((derivedUpperStarLowerStarAdjunction _ a).unit.app (𝟙_ _) ≫
        (R((a)_*[ModuleCat.{u + 1} Λ])).map e.hom) ≫ h) := by
  let f := (derivedUpperStarLowerStarAdjunction _ a).unit.app (𝟙_ _) ≫
    (R((a)_*[ModuleCat.{u + 1} Λ])).map e.hom
  obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f v w
  have : T.obj₂.IsGE 0 := isGE_rightDerivedLowerStar_obj_unit a
  have : T.obj₃.IsGE 1 := isGE_one_of_bijective_comp_of_isSepClosed T hT (Iso.refl _)
    (bijective_comp_unit_comp_rightDerivedLowerStar_map a e)
  have hb := DerivedCategory.bijective_comp_singleFunctor_of_injective_of_isGE T hT
    ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ))
  let J := unitIsoSingleFunctorConstantSheaf Λ (Spec (.of k))
  have hJ : Function.Bijective (fun h : T.obj₂ ⟶ 𝟙_ _ ↦ T.mor₁ ≫ h) := by
    refine ⟨fun h₁ h₂ h₁₂ ↦ ?_, fun z ↦ ?_⟩
    · have := hb.1 (a₁ := h₁ ≫ J.hom) (a₂ := h₂ ≫ J.hom)
        (by simp only [← Category.assoc, h₁₂])
      simpa using this =≫ J.inv
    · obtain ⟨h, hh⟩ := hb.2 (z ≫ J.hom)
      refine ⟨h ≫ J.inv, ?_⟩
      change T.mor₁ ≫ h ≫ J.inv = z
      replace hh : T.mor₁ ≫ h = z ≫ J.hom := hh
      rw [← Category.assoc, hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact hJ

variable [HasTateTwist Λ]

variable (Λ k) [HasInvertibleExponent Λ (Spec (.of k))] in
/-- Over a separably closed field the Tate twists are trivial, `Λ_s(m) ≅ Λ_s`: the twisting
object is a locally constant sheaf in degree `0` whose stalk is free of rank one, and on
`Spec k` such a sheaf is constant. -/
theorem nonempty_tateObject_iso_unit (m : ℤ) :
    Nonempty (tateObject Λ (Spec (.of k)) m ≅ 𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) := by
  obtain ⟨L, -, hL, ⟨e⟩⟩ :=
    HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) (Spec (.of k)) m
  obtain ⟨f⟩ := hL k (𝟙 _)
  obtain ⟨g⟩ := Scheme.nonempty_iso_constantSheaf_of_sheafFiber_iso L f
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso g ≪≫
    (unitIsoSingleFunctorConstantSheaf Λ _).symm⟩

namespace TateOrientation

variable [Finite Λ] [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}}
  [HasInvertibleExponent Λ X]
  {a : X ⟶ Spec (.of k)} [HasCompactification a] {d : ℕ}

/-- Over a separably closed field the untwisted trace `tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)` is
bijective as soon as the twisted trace `tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ` is: the twists `Λ_s(±d)`
are trivial (`AlgebraicGeometry.Etale.nonempty_tateObject_iso_unit`) and the projection
formula identifies `(Ra_! Λ_X)[2d] ⊗ Λ_s(d)` with `(Ra_! Λ_X(d))[2d]`
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`). -/
theorem bijective_untwistedTraceMap_of_bijective_traceMap (γ : TateOrientation Λ a d)
    (h : Function.Bijective γ.traceMap) : Function.Bijective γ.untwistedTraceMap := by
  obtain ⟨eA⟩ := nonempty_tateObject_iso_unit Λ k (d : ℤ)
  obtain ⟨eB⟩ := nonempty_tateObject_iso_unit Λ k (-(d : ℤ))
  have := isIso_projectionMap_of_finite Λ a
  let M := (R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X)
  let θ := (((derivedTensor _ (Spec (.of k))).flip.obj (tateObject Λ (Spec (.of k)) d)).commShiftIso
      (2 * d : ℤ)).hom.app M ≫
    (((projectionMap _ a).app (constantComplex Λ X)).app
      (tateObject Λ (Spec (.of k)) d))⟦(2 * d : ℤ)⟧' ≫
    ((R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor _ X).obj _).map
      (leftDerivedUpperStarTateObjectIso a d).hom ≫
        (derivedTensorLeftUnitor _ X (tateObject Λ X d)).hom))⟦(2 * d : ℤ)⟧'
  have : IsIso θ := by
    dsimp only [θ]
    infer_instance
  let t := ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app
    (tateObject Λ X d) ≫ γ.smoothTrace
  have hθt : θ ≫ t = γ.twistedSmoothTrace := by
    simp only [θ, t, M, twistedSmoothTrace, Category.assoc]
  have key := bijective_comp_derivedTensor_untwist (constantComplexIsoTateObjectTensor _ d)
    eA eB θ t h
  rw [hθt] at key
  exact key

end TateOrientation

end AlgebraicGeometry.Etale
