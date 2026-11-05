/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroSource
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounit
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroApex
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation
/-! # Constructed target comparison for the degree-zero open square
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
(blueprint: lem-pc-open-pinned-single-degree-zero-target). -/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
/-- Naturality of the canonical mate in its derived input, from the naturality
of the pullback composition comparisons and the adjunction Hom equivalence.
Source: Stacks Project, Tag 08HY, the canonical derived base-change construction. -/
private theorem baseChange_naturality
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : g' ≫ f = f' ≫ g)
    {E F : schemeDerivedCategory X} (s : E ⟶ F) :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map s) ≫
        schemeDerivedBaseChangeMap f f' g g' h F =
      schemeDerivedBaseChangeMap f f' g g' h E ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map s) :=
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    set_option synthInstance.maxSize 2048 in
    open MonoidalCategory in by
  classical
  have : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      (Scheme.Modules.tensorPullback k).Additive :=
    @Classical.choose _ _ exists_derivedPullbackComposition.{u, w}
  let ε : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings B.toRingedSpace)) ⋙
        derivedPullback k ⟶
        (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings A.toRingedSpace)) :=
    fun k ↦ (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k
  have hε : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      (derivedPullback k).IsLeftDerivedFunctor (ε k)
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings B.toRingedSpace)) (.up ℤ)) :=
    fun k ↦ (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) k
  let c : ∀ {A B D : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ D),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let adj := Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f) (ε f) (hε f))
  let adj' := Classical.choose (exists_schemeDerivedAdjunction f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f') (ε f') (hε f'))
  let γ : (schemeDerivedDirectImage f ⋙ derivedPullback g) ⋙ derivedPullback f' ⟶
      derivedPullback g' :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (c f' g).hom ≫
      Functor.whiskerLeft _ (eqToHom (congrArg (fun k ↦ derivedPullback k) h.symm)) ≫
      Functor.whiskerLeft _ (c g' f).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight adj.counit (derivedPullback g') ≫
      (Functor.leftUnitor _).hom
  have hγ (K : schemeDerivedCategory X) :
      γ.app K = (c f' g).hom.app ((schemeDerivedDirectImage f).obj K) ≫
        eqToHom (congrArg (fun k ↦
          (derivedPullback k).obj ((schemeDerivedDirectImage f).obj K)) h.symm) ≫
        (c g' f).inv.app ((schemeDerivedDirectImage f).obj K) ≫
        (derivedPullback g').map (adj.counit.app K) := by
    simp only [γ, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, eqToHom_app, Category.id_comp]
    change _ ≫ _ ≫ _ ≫ _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
  have hbc (K : schemeDerivedCategory X) :
      schemeDerivedBaseChangeMap f f' g g' h K = adj'.homEquiv _ _ (γ.app K) := by
    rw [hγ]
    rfl
  rw [hbc E, hbc F]
  exact adj'.homEquiv_naturality_left_square
    ((schemeDerivedDirectImage f ⋙ derivedPullback g).map s)
    (γ.app F) (γ.app E) ((derivedPullback g').map s) (γ.naturality s)


private theorem combine_restriction_square
    {C : Type*} [Category C] {A B B₀ C₁ C₀ C₂ A₀ D₀ A₁ D₁ : C}
    (x : A ⟶ B) (r : B ⟶ C₁) (d₁ : B ⟶ B₀) (d₂ : C₁ ⟶ C₀)
    (a : A ⟶ A₀) (y : A₀ ⟶ D₀) (δ : D₀ ⟶ B₀) (c : B₀ ⟶ C₀)
    (t : C₀ ⟶ C₂) (z : D₀ ⟶ D₁) (c₀ : D₁ ⟶ C₂)
    (s : A₀ ⟶ A₁) (y₁ : A₁ ⟶ D₁)
    (hx : x ≫ d₁ = a ≫ y ≫ δ) (hr : r ≫ d₂ = d₁ ≫ c)
    (hc : δ ≫ c ≫ t = z ≫ c₀) (hy : y ≫ z = s ≫ y₁) :
    x ≫ r ≫ (d₂ ≫ t) = (a ≫ s) ≫ (y₁ ≫ c₀) := by
  calc
    _ = (x ≫ d₁) ≫ c ≫ t := by rw [← Category.assoc r d₂, hr]; simp [Category.assoc]
    _ = a ≫ y ≫ (δ ≫ c ≫ t) := by rw [hx]; simp [Category.assoc]
    _ = a ≫ (y ≫ z) ≫ c₀ := by rw [hc]; simp [Category.assoc]
    _ = _ := by rw [hy]; simp [Category.assoc]

set_option maxHeartbeats 1000000 in
-- Explicit mate and single-restriction comparisons require extra elaboration heartbeats.
end AlgebraicGeometry
