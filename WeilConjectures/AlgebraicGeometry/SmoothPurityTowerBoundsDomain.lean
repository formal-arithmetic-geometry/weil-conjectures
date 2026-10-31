/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.CoefficientTowerSectionCoordinates
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Uniform level bounds give the ordinary tower domain

Source: blueprint latest, Local pairs, bounded-below strict-tower domain
(blueprint: lem-sp-level-bounds-tower-domain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpChartAdmissibility

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem presheaf_ext {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    {M N : PresheafOfModules R} (hobj : ∀ U, M.obj U = N.obj U)
    (hmap : ∀ {U V} (f : U ⟶ V), HEq (M.map f) (N.map f)) : M = N := by
  cases M with | mk MO MM MI MC =>
    cases N with | mk NO NM NI NC =>
      dsimp only at hobj hmap
      have ho : MO = NO := funext hobj
      subst ho
      have hm : @MM = @NM := by
        funext U V f
        exact eq_of_heq (hmap f)
      subst hm
      rfl

private theorem sheaf_ext {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} (h : M.val = N.val) : M = N := by
  cases M with | mk MV MS =>
    cases N with | mk NV NS =>
      dsimp only at h
      cases h
      rfl

private theorem sheafHom_hext {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M₁ M₂ N₁ N₂ : SheafOfModules R}
    (hM : M₁ = M₂) (hN : N₁ = N₂) (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂)
    (h : ∀ U, HEq (f.val.app U) (g.val.app U)) : HEq f g := by
  cases hM
  cases hN
  apply heq_of_eq
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro U
  exact eq_of_heq (h U)

private theorem sp_evaluation_obj_eq (T : Scheme.{u}) (D₁ D₂ : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) :
    (spCoefficientEvaluation l E T D₁.equivalence n).obj M =
      (spCoefficientEvaluation l E T D₂.equivalence n).obj M := by
  suffices h : ((D₁.equivalence.functor.obj M).level n).val =
      ((D₂.equivalence.functor.obj M).level n).val by
    exact sheaf_ext h
  apply presheaf_ext
  · intro U
    exact eq_of_heq ((D₁.sections M n U).trans (D₂.sections M n U).symm)
  · intro U V f
    exact (D₁.restrictions M n f).trans (D₂.restrictions M n f).symm

private theorem sp_evaluation_eq (T : Scheme.{u})
    (D₁ D₂ : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    spCoefficientEvaluation l E T D₁.equivalence n =
      spCoefficientEvaluation l E T D₂.equivalence n := by
  apply Functor.hext (fun M ↦ sp_evaluation_obj_eq l E T D₁ D₂ M n)
  intro M N f
  apply sheafHom_hext (sp_evaluation_obj_eq l E T D₁ D₂ M n)
    (sp_evaluation_obj_eq l E T D₁ D₂ N n)
  intro U
  exact (D₁.morphisms f n U).trans (D₂.morphisms f n U).symm

private noncomputable def sp_realization_evaluation (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (spTowerShriekRealization l E b T D).functor ⋙ SpTowerShriek.Ev l E T n ≅
      spDerivedCoefficientEvaluation l E T D n := by
  letI := D.hasDerived
  haveI := b.realizationAdditive T
  haveI := D.equivalenceAdditive
  haveI := D.evaluationLimits n
  haveI := D.evaluationColimits n
  haveI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  let q := Classical.choice (SpTowerCalculus.coordinates_realization l E b)
  let e := q.ordinaryEvaluation T n ≪≫ eqToIso (sp_evaluation_eq l E T (q.abelian T) D n)
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso e

private theorem sp_tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem sp_finite_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, a', b', ht⟩ := h
  refine ⟨⟨a, b, hab, fun i hi ↦
    (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩, ?_,
    a', b', sp_tor_of_iso T A e ht⟩
  intro i
  apply (Scheme.proEtaleModuleRestriction_constructible_iff T A _).mpr
  exact isConstructible_of_iso
    ((Scheme.proEtaleModuleRestriction T A).mapIso
      ((DerivedCategory.homologyFunctor _ i).mapIso e))
    ((Scheme.proEtaleModuleRestriction_constructible_iff T A _).mp (hc i))

/-- Uniform finite-level bounds give the recorded domain for the actual ordinary tower.
The origins hypothesis concerns independent finite complexes and contains no tower claim.
Source: blueprint latest, Local pairs, and chart-admissibility proof steps 2--3
(blueprint: lem-sp-level-bounds-tower-domain).

Proof: exact evaluation commutes with homology. If i < a, all evaluations of H^i(C)
vanish. The ordinary tower sheaf has zero components, so is zero, proving C.IsGE a.
Transport C by the inverse of the section-preserving derived realization. Its evaluated
levels are naturally isomorphic to the original levels: the abelian realization changes
no section or restriction map. Transport finite constructibility, cohomology vanishing
and Tor amplitude across these isomorphisms. The same a,b,s,t therefore establish
spConstructibleTorTowers for every presentation D. For each n apply the given origins
assertion to the n-th level and its prescribed intervals. The etale witness is bounded
below; its exact comparison is bounded below too. Transport the fixed-scalar comparison
through the canonical intrinsic module equivalence to obtain Origin n C. This is a
separate witness for each n; no compatibility or normalized transitions are asserted. -/
theorem domain_of_level_bounds
    (base : SpTowerShriek.Base l E) (T : Scheme.{u}) [IsNoetherian T]
    (horig : origins l E T)
    (C : SpTowerShriek.D l E T) (a b s t : ℤ) (hab : a ≤ b) (hst : s ≤ t)
    (hC : bounds l E T C a b s t) : domain l E base T C := by
  classical
  have hvan (n : ℕ) (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((SpTowerShriek.Ev l E T n).obj C)) := by
    by_contra hn
    have hm := (hC n).2.1 hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge hm.1) hi
    · exact (not_lt_of_ge hm.2) hi
  refine ⟨?_, ⟨a, ?_⟩, ?_⟩
  · intro D
    let R := spTowerShriekRealization l E base T D
    let K := R.inverse.obj C
    have e (n : ℕ) :
        (spDerivedCoefficientEvaluation l E T D n).obj K ≅
          (SpTowerShriek.Ev l E T n).obj C :=
      (sp_realization_evaluation l E base T D n).symm.app K ≪≫
        (SpTowerShriek.Ev l E T n).mapIso (R.counitIso.app C)
    refine ⟨fun n ↦ sp_finite_of_iso T _ (e n).symm (hC n).1,
      a, b, s, t, hab, hst, fun n ↦ ⟨?_, ?_⟩⟩
    · intro i hi
      exact (hvan n i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (e n))
    · exact sp_tor_of_iso T _ (e n).symm (hC n).2.2
  · apply (DerivedCategory.isGE_iff C a).2
    intro i hi
    let H := (DerivedCategory.homologyFunctor (SpTowerShriek.S l E T) i).obj C
    have hz (n : ℕ) : IsZero ((SpTowerShriek.ev l E T n).obj H) :=
      (hvan n i (.inl hi)).of_iso
        (((SpTowerShriek.ev l E T n).mapDerivedCategoryHomologyFunctorIso i).app C)
    apply (IsZero.iff_id_eq_zero H).2
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    have heq := congrArg (fun k ↦ k.val.app (op U.unop.2) x)
      ((hz U.unop.1).eq_of_src
        ((SpTowerShriek.ev l E T U.unop.1).map (𝟙 H))
        ((SpTowerShriek.ev l E T U.unop.1).map (0 : H ⟶ H)))
    exact heq
  · intro n
    let A := SpTowerShriek.R l E n
    let F := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
    let R := finiteCoefficientIntrinsicRealization T A
    obtain ⟨L, _, _, hv, ⟨eL⟩⟩ :=
      horig n ((SpTowerShriek.Ev l E T n).obj C) (hC n).1
        a b s t hab hst (hC n).2.1 (hC n).2.2
    have hplus : DerivedCategory.TStructure.t.plus L :=
      ⟨a, (DerivedCategory.isGE_iff L a).2 fun i hi ↦ hv i (.inl hi)⟩
    let LP : DerivedCategory.Plus _ := ⟨L, hplus⟩
    let level := F.mapDerivedCategoryPlus.obj LP
    refine ⟨{
      level := level
      realization := R.mapDerivedCategory.mapIso
          (F.mapDerivedCategoryPlusCompatibility.app LP) ≪≫
        (Functor.mapDerivedCategoryCompIso F R).symm.app L ≪≫ eL
      witness := {
        complex := LP
        iso := F.mapDerivedCategoryPlusCompatibility.symm.app LP } }⟩

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
