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
  finite coefficient ring `Λ`, evaluation at the class `1 ∈ H⁰(X, Λ)`,
  `Hom(Ra_* Λ_X, Λ_s) ⟶ Hom(Λ_s, Λ_s)`, is bijective. This is `H⁰(X, Λ) = Λ` for the connected
  `X` together with `Ext^{>0}_Λ(-, Λ) = 0`.
* `AlgebraicGeometry.Etale.TateOrientation.bijective_untwistedTraceMap_of_bijective_traceMap`:
  over `s` the Tate twists are trivial, so the untwisted trace is bijective as soon as the
  twisted one is.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Stubs

variable {Λ : Type (u + 1)} [CommRing Λ]

-- TEMPORARY stubs (to be replaced by the lemmas of the constant-sheaf file)
theorem stub_bijective_smul_id_unit (X : Scheme.{u}) [ConnectedSpace X] :
    Function.Bijective (fun r : Λ ↦ r • 𝟙 (𝟙_ (DerivedCategoryModule Λ X))) := sorry

theorem stub_injective {k : Type u} [Field k] [IsSepClosed k] [Module.Injective Λ Λ] :
    Injective ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ)) := sorry

theorem stub_iso {k : Type u} [Field k] [IsSepClosed k]
    (L : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (e : (Scheme.pointSmallEtale (𝟙 (Spec (.of k)))).sheafFiber.obj L ≅ ModuleCat.of Λ Λ) :
    Nonempty (L ≅ (constantSheaf _ _).obj (ModuleCat.of Λ Λ)) := sorry

end Stubs

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

/-- For `a : X ⟶ s` with `X` connected, `g ↦ e⁻¹ ≫ La^* g ≫ e` is a bijection
`End(Λ_s) ≃ End(Λ_X)` for any `e : La^* Λ_s ≅ Λ_X`: both endomorphism rings are `Λ`, by
`r ↦ r • 𝟙`, and `La^*` is `Λ`-linear. -/
theorem bijective_leftDerivedUpperStar_map_comp {X : Scheme.{u}} [ConnectedSpace X]
    (a : X ⟶ Spec (.of k)) (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _) :
    Function.Bijective (fun g : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _ ↦
      (L((a)^*[ModuleCat.{u + 1} Λ])).map g ≫ e.hom) := by
  have hs := stub_bijective_smul_id_unit (Λ := Λ) (Spec (.of k))
  have hX := stub_bijective_smul_id_unit (Λ := Λ) X
  have h : ((fun z ↦ e.inv ≫ z ≫ (Iso.refl _).hom) ∘
      (fun g : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _ ↦
        (L((a)^*[ModuleCat.{u + 1} Λ])).map g ≫ e.hom)) ∘ (fun r : Λ ↦ r • 𝟙 (𝟙_ _)) =
      fun r : Λ ↦ r • 𝟙 (𝟙_ (DerivedCategoryModule Λ X)) := by
    funext r
    simp
  rw [← h] at hX
  exact (bijective_conj e.symm (Iso.refl _)).of_comp_iff'.1
    ((Function.Bijective.of_comp_iff _ hs).1 hX)

/-- **Evaluation at `1` is bijective.** Let `k` be separably closed, `Λ` self-injective, and
`a : X ⟶ Spec k` with `X` connected. For an identification `e : La^* Λ_s ≅ Λ_X`, let
`u : Λ_s ⟶ Ra_* Λ_X` be the class `1 ∈ H⁰(X, Λ)` (the unit of `La^* ⊣ Ra_*` read through `e`).
Then `h ↦ u ≫ h`, `Hom(Ra_* Λ_X, Λ_s) ⟶ Hom(Λ_s, Λ_s)`, is bijective.

Indeed `Ra_* Λ_X ∈ D^{≥ 0}`, and `Hom(Λ_s, u)` is bijective since `H⁰(X, Λ) = Λ` for the connected
`X` (`AlgebraicGeometry.Etale.bijective_leftDerivedUpperStar_map_comp`), so the cone of `u` lies
in `D^{≥ 1}` (`AlgebraicGeometry.Etale.isGE_one_of_bijective_comp_of_isSepClosed`); and `Λ_s` is
an injective sheaf, so it has no morphisms from `D^{≥ 1}` and its shift
(`DerivedCategory.bijective_comp_singleFunctor_of_injective_of_isGE`). -/
theorem bijective_comp_unit_rightDerivedLowerStar [Module.Injective Λ Λ] {X : Scheme.{u}}
    [ConnectedSpace X] (a : X ⟶ Spec (.of k))
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _) :
    Function.Bijective (fun h : (R((a)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ⟶ 𝟙_ _ ↦
      ((derivedUpperStarLowerStarAdjunction _ a).unit.app (𝟙_ _) ≫
        (R((a)_*[ModuleCat.{u + 1} Λ])).map e.hom) ≫ h) := by
  set u := (derivedUpperStarLowerStarAdjunction _ a).unit.app (𝟙_ _) ≫
    (R((a)_*[ModuleCat.{u + 1} Λ])).map e.hom
  have hP : ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      (𝟙_ (DerivedCategoryModule Λ X))).IsGE 0 := by
    have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor ((a)_*[ModuleCat.{u + 1} Λ])
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((R((a)_*[ModuleCat.{u + 1} Λ])).mapIso (unitIsoSingleFunctorConstantSheaf Λ X)).symm 0
  have hu : Function.Bijective (fun g : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _ ↦
      g ≫ u) := by
    have : (fun g : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _ ↦ g ≫ u) =
        (derivedUpperStarLowerStarAdjunction _ a).homEquiv _ _ ∘
          (fun g ↦ (L((a)^*[ModuleCat.{u + 1} Λ])).map g ≫ e.hom) := by
      funext g
      simp [u, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit]
    rw [this]
    exact (Equiv.bijective _).comp (bijective_leftDerivedUpperStar_map_comp a e)
  obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle u
  have : Z.IsGE 1 := isGE_one_of_bijective_comp_of_isSepClosed (Triangle.mk u v w) hT
    (Iso.refl _) hu
  have := stub_injective (Λ := Λ) (k := k)
  have hb := DerivedCategory.bijective_comp_singleFunctor_of_injective_of_isGE
    (Triangle.mk u v w) hT ((constantSheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
  let J := unitIsoSingleFunctorConstantSheaf Λ (Spec (.of k))
  have : (fun h : (R((a)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ⟶ 𝟙_ _ ↦ u ≫ h) =
      (fun z ↦ (Iso.refl _).hom ≫ z ≫ J.inv) ∘ (fun h ↦ u ≫ h) ∘
        (fun h ↦ (Iso.refl _).hom ≫ h ≫ J.hom) := by
    funext h
    simp
  rw [this]
  exact (bijective_conj _ _).comp (hb.comp (bijective_conj _ _))

variable [HasTateTwist Λ]

variable (Λ k) in
/-- Over a separably closed field the Tate twists are trivial, `Λ_s(m) ≅ Λ_s`: the twisting
object is a locally constant sheaf in degree `0` whose stalk is free of rank one, and on
`Spec k` such a sheaf is constant. -/
theorem nonempty_tateObject_iso_unit (m : ℤ) :
    Nonempty (tateObject Λ (Spec (.of k)) m ≅ 𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) := by
  obtain ⟨L, -, hL, ⟨e⟩⟩ :=
    HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) (Spec (.of k)) m
  obtain ⟨f⟩ := hL k (𝟙 _)
  obtain ⟨g⟩ := stub_iso L f
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso g ≪≫
    (unitIsoSingleFunctorConstantSheaf Λ _).symm⟩

namespace TateOrientation

variable [Finite Λ] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} [HasCompactification a] {d : ℕ}

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
  let θ := (((derivedTensor _ (Spec (.of k))).flip.obj (tateObject Λ (Spec (.of k)) d)).commShiftIso
      (2 * d : ℤ)).hom.app _ ≫
    (((projectionMap _ a).app (constantComplex Λ X)).app
      (tateObject Λ (Spec (.of k)) d))⟦(2 * d : ℤ)⟧' ≫
    ((R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor _ X).obj _).map
      (leftDerivedUpperStarTateObjectIso a d).hom ≫
        (derivedTensorLeftUnitor _ X _).hom))⟦(2 * d : ℤ)⟧'
  have : IsIso θ := by
    dsimp only [θ]
    infer_instance
  let t := ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace
  have hθt : θ ≫ t = γ.twistedSmoothTrace := by
    simp only [θ, t, twistedSmoothTrace, Category.assoc]
  have key := MonoidalCategory.bijective_comp_untwist (constantComplexIsoTateObjectTensor _ d)
    eA eB θ t h
  rw [hθt] at key
  exact key

end TateOrientation

end AlgebraicGeometry.Etale
