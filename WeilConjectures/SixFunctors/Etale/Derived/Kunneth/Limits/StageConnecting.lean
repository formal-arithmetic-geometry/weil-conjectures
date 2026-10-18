/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageTransition
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StalkColimit
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.CommShiftPlus
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The connecting maps of the stages of a limit system

For a stage `α` of a limit system and a short exact sequence `E` of sheaves on the limit, the
connecting maps of the long exact sequences of homology of the functor of the stage
(`AlgebraicGeometry.Etale.LimitStage.connecting`) and their exactness properties on stalks.
These are used for the dimension shifting in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DimensionShift`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The functor `K ↦ H^q(K)` followed by the geometric stalk at `x`. -/
noncomputable abbrev stalkHomology {B : Scheme.{u}} (q : ℤ) (x : B) :
    DerivedCategory.Plus (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      ModuleCat.{u + 1} Λ :=
  DerivedCategory.Plus.homologyFunctor _ q ⋙ (B.uliftPointSmallEtale x).sheafFiber

lemma _root_.ModuleCat.eq_zero_of_isZero {R : Type*} [Ring R] {M : ModuleCat R} (h : IsZero M)
    (m : M) : m = 0 := by
  have := congrArg (fun f : M ⟶ M ↦ f.hom m) (h.eq_of_src (𝟙 M) 0)
  simpa using this

/-- An exact sequence of sheaves is exact on geometric stalks, elementwise. -/
lemma exists_of_exact_sheafFiber {X : Scheme.{u}}
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.Exact)
    (x : X) (y : ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj S.X₂)
    (hy : (((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).map S.g).hom y = 0) :
    ∃ z, (((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).map S.f).hom z =
      y := by
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  have : PreservesFiniteLimits ((X.uliftPointSmallEtale x).sheafFiber
    (A := ModuleCat.{u + 1} Λ)) := inferInstance
  have : PreservesFiniteColimits ((X.uliftPointSmallEtale x).sheafFiber
    (A := ModuleCat.{u + 1} Λ)) := inferInstance
  have h := hS.map (X.uliftPointSmallEtale x).sheafFiber
  rw [ShortComplex.moduleCat_exact_iff] at h
  exact h y hy

namespace LimitStage

variable {B W : Scheme.{u}}

set_option maxHeartbeats 1000000 in
-- the instance arguments of the whiskered transformations are large
instance commShift_transition {α β : LimitStage B W} (φ : Hom α β) :
    NatTrans.CommShift (transition Λ φ) ℤ := by
  unfold transition
  infer_instance

/-- `H^q(π^* Rg_* w^*(G[0]))` vanishes for `q < 0`. -/
lemma isZero_homology_functor_obj_single_of_lt (α : LimitStage B W)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {q : ℤ} (hq : q < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((functor Λ α).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  refine IsZero.of_iso ?_ ((((α.π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
    q).app _).symm
  refine Functor.map_isZero ((α.π)^*[ModuleCat.{u + 1} Λ]) ?_
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (R+((α.g)_*[ModuleCat.{u + 1} Λ]).mapIso
      ((((α.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app G)))
  exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (((α.w)^*[ModuleCat.{u + 1} Λ]).obj G)) 0 hq

/-- `H^q(π^* Rg_* w^*(J[0]))` vanishes for `q ≠ 0` when `w^* J` is injective. -/
lemma isZero_homology_functor_obj_single_of_injective (α : LimitStage B W)
    (J : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Injective (((α.w)^*[ModuleCat.{u + 1} Λ]).obj J)] {q : ℤ} (hq : q ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((functor Λ α).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj J))) := by
  refine IsZero.of_iso ?_ ((((α.π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
    q).app _).symm
  refine Functor.map_isZero ((α.π)^*[ModuleCat.{u + 1} Λ]) ?_
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (R+((α.g)_*[ModuleCat.{u + 1} Λ]).mapIso
      ((((α.w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app J)))
  exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor _ _ hq

section LES

variable {E : ShortComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
  (δ : (DerivedCategory.Plus.singleFunctor _ 0).obj E.X₃ ⟶
    ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₁)⟦(1 : ℤ)⟧)
  (hT : Triangle.mk ((DerivedCategory.Plus.singleFunctor _ 0).map E.f)
    ((DerivedCategory.Plus.singleFunctor _ 0).map E.g) δ ∈ distTriang _)

/-- The connecting map `H^{n₀}(Φ(E.X₃[0])) ⟶ H^{n₁}(Φ(E.X₁[0]))` of the long exact sequence of
the functor `Φ` of a stage, for a distinguished triangle on a short exact sequence `E`. -/
noncomputable def connecting (α : LimitStage B W) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (DerivedCategory.Plus.homologyFunctor _ n₀).obj
        ((functor Λ α).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₃)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ n₁).obj
        ((functor Λ α).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₁)) :=
  (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
    ((functor Λ α).mapTriangle.obj (Triangle.mk ((DerivedCategory.Plus.singleFunctor _ 0).map E.f)
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.g) δ)) n₀ n₁ h

variable {Λ} in
include hT in
/-- Exactness at `H^{n}(Φ(E.X₂[0]))`, on stalks. -/
lemma exists_of_stalk_exact₂ (α : LimitStage B W) (n : ℤ) (x : B)
    (y : (stalkHomology Λ n x).obj
      ((functor Λ α).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₂)))
    (hy : ((stalkHomology Λ n x).map ((functor Λ α).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.g))).hom y = 0) :
    ∃ z, ((stalkHomology Λ n x).map ((functor Λ α).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.f))).hom z = y :=
  exists_of_exact_sheafFiber Λ ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₂
    _ ((functor Λ α).map_distinguished _ hT) n) x y hy

variable {Λ} in
include hT in
/-- Exactness at `H^{n₀}(Φ(E.X₃[0]))`, on stalks. -/
lemma exists_of_stalk_exact₃ (α : LimitStage B W) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (x : B)
    (y : (stalkHomology Λ n₀ x).obj
      ((functor Λ α).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₃)))
    (hy : ((B.uliftPointSmallEtale x).sheafFiber.map (connecting Λ δ α n₀ n₁ h)).hom y = 0) :
    ∃ z, ((stalkHomology Λ n₀ x).map ((functor Λ α).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.g))).hom z = y :=
  exists_of_exact_sheafFiber Λ ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₃
    _ ((functor Λ α).map_distinguished _ hT) n₀ n₁ h) x y hy

variable {Λ} in
include hT in
/-- Exactness at `H^{n₁}(Φ(E.X₁[0]))`, on stalks. -/
lemma exists_of_stalk_exact₁ (α : LimitStage B W) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (x : B)
    (y : (stalkHomology Λ n₁ x).obj
      ((functor Λ α).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₁)))
    (hy : ((stalkHomology Λ n₁ x).map ((functor Λ α).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.f))).hom y = 0) :
    ∃ z, ((B.uliftPointSmallEtale x).sheafFiber.map (connecting Λ δ α n₀ n₁ h)).hom z = y :=
  exists_of_exact_sheafFiber Λ ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₁
    _ ((functor Λ α).map_distinguished _ hT) n₀ n₁ h) x y hy

variable {Λ} in
include hT in
lemma connecting_comp_eq_zero (α : LimitStage B W) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (DerivedCategory.Plus.homologyFunctor _ n₀).map ((functor Λ α).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.g)) ≫ connecting Λ δ α n₀ n₁ h = 0 :=
  (DerivedCategory.Plus.homologyFunctor _ 0).comp_homologySequenceδ _
    ((functor Λ α).map_distinguished _ hT) n₀ n₁ h

end LES

end LimitStage

end AlgebraicGeometry.Etale
