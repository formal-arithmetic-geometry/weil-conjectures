/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA, SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps
import Sheaf.Paper.RefinementExchangeCoherence
import Mathlib.Algebra.Ring.PUnit

/-!
# Composition pasting for strict constant-coefficient towers

Source: Stacks Project, Tags 0F7J, 0F7C, 0F7D and 0F7F.
The shared constructions live in `StrictTowerCompositionMaps`, so refinement
independence can be used here without an import cycle.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- Composition pasting is invertible on the stated finite-origin inputs, commutes with
all compatible proper refinements, and satisfies vertical interchange under arbitrary
base change. The latter two clauses are equalities of natural transformations on the
whole derived strict-tower categories; no evaluation-faithfulness premise is made.

Source: Stacks, Tags 0F7J, 0F7C, 0F7D and 0F7F, adapted to strict towers
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence).

Proof plan, following the node's ten steps:
1. Evaluation commutes with J_c. A scalar etale origin L_n evaluates J_c M as the
   scalar realization of c_! L_n, by finite constant coefficient transport and
   lem-cbc-proetale-extension-zero-comparison. Exactness of etale c_!
   (lem-weil-pbc-extension-by-zero-exact) retains its individual lower bound.
2. Apply gamma_isIso to Q at J_c M, and whisker with R_q. The jComp and rComp
   identifications give exactly compositionD, naturally in M.
3. For a refinement let A be its c-square, H its i-square, and T its b-square.
   Horizontal pasting in normalizedProperOpenCalculus gives
   gamma_a = (gamma_T J_c1)(J_b2 gamma_A). T need not be cartesian.
4. Apply vertical pasting to T above Q2 and Q1 above H; their outer squares agree.
   Thus (R_p2 gamma_T)(gamma_Q2 R_w) = (R_u gamma_Q1)(gamma_H R_r1).
5. Naturality of gamma_Q2 at gamma_A moves gamma_A past gamma_Q2.
6. Expand C_hf D2 using step 3, then steps 5 and 4. Normalize R_q2 R_u to R_q1.
   The result is D1 (C_h F_f1)(F_h2 C_f), with the displayed associators.
7. For base change, mate-pasting identifies E_qp with (R_q' E_p)(E_q R_p).
   Open composition identifies beta_a with (J_b' beta_c)(beta_b J_c).
8. The base-change clause of normalizedProperOpenCalculus gives
   (R_p' beta_b)(E_p J_b)(G_t gamma_Q)
     = (gamma_Q' G_d)(J_i' E_r)(beta_i R_r).
9. In e_hf(G_g D), naturality of E_q moves gamma_Q inside R_q'. Apply step 8.
   Naturality of gamma_Q' at beta_c leaves precisely
   (D' G_x)(F_h' e_f)(e_h F_f), proving vertical interchange before evaluation.
10. The same calculus cube on refinement squares transports both boundaries;
    common-refinement and independence are recorded below. No common bound or
    finite coefficient ring for all levels, and no properness of the base change,
    is used anywhere.
-/
theorem compositionPastingCoherence :
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T : Compactification.Triangle f h)
      [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
      (M : Derived B X),
      (∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) →
      IsIso ((compositionD B T).app M)) ∧
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T₁ T₂ : Compactification.Triangle f h)
      [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i] [QuasiCompact T₁.cfg.i]
      [QuasiCompact T₁.q]
      [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i] [QuasiCompact T₂.cfg.i]
      [QuasiCompact T₂.q] (r : CompositionRefinement T₁ T₂),
      compositionD B T₂ ≫ compositionC B r.rfh =
        compositionH B r ≫ compositionD B T₁) ∧
    (∀ {X Y Z X' Y' Z' : Scheme.{u}}
      (f : X ⟶ Y) (h : Y ⟶ Z) (f' : X' ⟶ Y') (h' : Y' ⟶ Z')
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
      [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
      [QuasiCompact T'.cf.i] [QuasiCompact T'.cg.i] [QuasiCompact T'.q]
      (x : X' ⟶ X) (y : Y' ⟶ Y) (g : Z' ⟶ Z)
      (A : CompositionBaseChange T T' x y g),
      Functor.whiskerRight (compositionD B T) (G B g) ≫ compositionEhf B A =
        compositionHorizontalE B A ≫ Functor.whiskerLeft (G B x) (compositionD B T')) := by
  sorry

private theorem refinementFactor_isIso {A C D E : Type*}
    [Category A] [Category C] [Category D] [Category E]
    (J₁ : A ⥤ C) (J₂ : A ⥤ D) (R₀ : A ⥤ A) (R₁ : C ⥤ D) (R₂ : D ⥤ E)
    (H : C ⥤ E) (e₀ : R₀ ≅ 𝟭 A) (e₁ : R₁ ⋙ R₂ ≅ H)
    (g : R₀ ⋙ J₂ ⟶ J₁ ⋙ R₁) (a : J₂ ⋙ R₂ ⟶ J₁ ⋙ H)
    (ha : a = Functor.whiskerRight
        ((Functor.leftUnitor J₂).inv ≫ Functor.whiskerRight e₀.inv J₂ ≫ g) R₂ ≫
      (Functor.associator J₁ R₁ R₂).hom ≫ Functor.whiskerLeft J₁ e₁.hom)
    (M : A) (hg : IsIso (g.app M)) : IsIso (a.app M) := by
  subst a
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- Both boundaries of the refinement square are invertible on finite-origin objects.
Source: Stacks, Tag 0F7J, choice independence
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence).
Proof: apply gamma_isIso to the refinement square for the compactifications of hf;
its left proper map is identity. Whisker by the outer proper direct image to obtain
invertibility of C_hf. By compositionPastingCoherence both D's are invertible and
C_hf D2 = D1 H, so H = D1⁻¹ C_hf D2 is invertible. This avoids any finite-origin
assumption on F_f M, as in step 10 of the node. -/
theorem compositionRefinement_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T₁ T₂ : Compactification.Triangle f h)
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i] [QuasiCompact T₁.cfg.i]
    [QuasiCompact T₁.q]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i] [QuasiCompact T₂.cfg.i]
    [QuasiCompact T₂.q] (r : CompositionRefinement T₁ T₂) (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    IsIso ((compositionC B r.rfh).app M) ∧ IsIso ((compositionH B r).app M) := by
  have hc : IsIso ((compositionC B r.rfh).app M) :=
    refinementFactor_isIso (J B T₁.cfg.i) (J B T₂.cfg.i) (R B (𝟙 X))
      (R B r.rfh.hom) (R B T₂.cfg.g) (R B T₁.cfg.g) (rId B X)
      (rComp B r.rfh.hom T₂.cfg.g ≪≫ eqToIso (congrArg (R B) r.rfh.hom_g))
      (gamma B T₁.cfg.i (𝟙 X) r.rfh.hom T₂.cfg.i
        (r.rfh.i_hom.trans (Category.id_comp T₂.cfg.i).symm))
      (compositionC B r.rfh) rfl M
      (gamma_isIso B T₁.cfg.i (𝟙 X) r.rfh.hom T₂.cfg.i
        (r.rfh.i_hom.trans (Category.id_comp T₂.cfg.i).symm) M hM)
  have hd₁ := (compositionPastingCoherence B).1 f h T₁ M hM
  have hd₂ := (compositionPastingCoherence B).1 f h T₂ M hM
  have heq := congrArg (fun η => η.app M)
    ((compositionPastingCoherence B).2.1 f h T₁ T₂ r)
  simp only [NatTrans.comp_app] at heq
  have hh : IsIso ((compositionH B r).app M ≫ (compositionD B T₁).app M) := by
    rw [← heq]
    infer_instance
  exact ⟨hc, IsIso.of_isIso_comp_right _ ((compositionD B T₁).app M)⟩

private theorem finiteOrigin_zero (X : Scheme.{u}) (n : ℕ) :
    Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj 0)) := by
  let Λ := PUnit.{u + 2}
  let : TopologicalSpace Λ := ⊥
  let φ : B →+* Λ :=
    { toFun := fun _ => PUnit.unit
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := 0
  let F := (finiteCoefficientComparison X Λ).mapDerivedCategoryPlus.obj L
  let w : ScalarEtaleOrigin B X
      ((finiteRestriction B X Λ φ).mapDerivedCategory.obj F.obj) :=
    { Λ := Λ
      φ := φ
      F := F
      origin := ⟨L, Iso.refl _⟩
      iso := Iso.refl _ }
  have : (HD B X Λ φ).Additive := by
    dsimp only [HD]
    infer_instance
  exact ⟨{ w with iso := (originIso B w).symm ≪≫
    (HD B X Λ φ).mapZeroObject ≪≫ (ev B X n).mapZeroObject.symm }⟩

private theorem horizontalRefinement
    {A₁ A₂ C₁ C₂ E₁ E₂ : Type*}
    [Category A₁] [Category A₂] [Category C₁] [Category C₂]
    [Category E₁] [Category E₂]
    (F₁ F₂ : A₁ ⥤ C₁) (H₁ H₂ : C₁ ⥤ E₁)
    (F₁' F₂' : A₂ ⥤ C₂) (H₁' H₂' : C₂ ⥤ E₂)
    (a : A₁ ⥤ A₂) (c : C₁ ⥤ C₂) (e : E₁ ⥤ E₂)
    (r : F₂ ⟶ F₁) (s : H₂ ⟶ H₁) (r' : F₂' ⟶ F₁') (s' : H₂' ⟶ H₁')
    (ef₁ : F₁ ⋙ c ⟶ a ⋙ F₁') (ef₂ : F₂ ⋙ c ⟶ a ⋙ F₂')
    (eh₁ : H₁ ⋙ e ⟶ c ⋙ H₁') (eh₂ : H₂ ⋙ e ⟶ c ⋙ H₂')
    (hf : ef₂ ≫ Functor.whiskerLeft a r' = Functor.whiskerRight r c ≫ ef₁)
    (hh : eh₂ ≫ Functor.whiskerLeft c s' = Functor.whiskerRight s e ≫ eh₁)
    (M : A₁) :
    eh₂.app (F₂.obj M) ≫ H₂'.map (ef₂.app M) ≫
        H₂'.map (r'.app (a.obj M)) ≫ s'.app (F₁'.obj (a.obj M)) =
      e.map (H₂.map (r.app M)) ≫ e.map (s.app (F₁.obj M)) ≫
        eh₁.app (F₁.obj M) ≫ H₁'.map (ef₁.app M) := by
  have hfM := congrArg (fun η => η.app M) hf
  have hhM := congrArg (fun η => η.app (F₁.obj M)) hh
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hfM hhM
  rw [← Functor.map_comp_assoc, hfM, Functor.map_comp]
  have hn := eh₂.naturality (r.app M)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc (eh₂.app _) (H₂'.map (c.map (r.app M))), ← hn]
  simp only [Category.assoc]
  have hs := s'.naturality (ef₁.app M)
  dsimp only [Functor.comp_obj] at hs
  rw [hs]
  rw [← Category.assoc (eh₂.app _) (s'.app _), hhM]
  simp only [Category.assoc]

/-- Refinement transport of both sides of the vertical interchange square, before evaluation.
Source: Stacks, Tags 0F7F and 0F7J
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence).
Proof: apply the calculus base-change cube to the three refinement squares A,H,a.
It gives C'_bullet e_bullet,2 = e_bullet,1 (G C_bullet) for f,h,hf, on every input.
Naturality of e_h with C_f combines the first two equations into the equation for H.
Substitution in the third clause of compositionPastingCoherence, together with its
refinement clause and the primed refinement clause, transports the entire vertical
interchange identity unchanged. This is node step 10; neither equality is deduced
from evaluation, and no finite-origin hypothesis on F_f M is used. -/
theorem compositionRefinementExchange
    {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (h : Y ⟶ Z) (f' : X' ⟶ Y') (h' : Y' ⟶ Z')
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T₁ T₂ : Compactification.Triangle f h)
    (T₁' T₂' : Compactification.Triangle f' h')
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i] [QuasiCompact T₁.cfg.i]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i] [QuasiCompact T₂.cfg.i]
    [QuasiCompact T₁'.cf.i] [QuasiCompact T₁'.cg.i] [QuasiCompact T₁'.cfg.i]
    [QuasiCompact T₂'.cf.i] [QuasiCompact T₂'.cg.i] [QuasiCompact T₂'.cfg.i]
    (r : CompositionRefinement T₁ T₂) (r' : CompositionRefinement T₁' T₂')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (g : Z' ⟶ Z)
    (A₁ : CompositionBaseChange T₁ T₁' x y g)
    (A₂ : CompositionBaseChange T₂ T₂' x y g)
    (wf : r'.rf.hom ≫ A₂.d = A₁.d ≫ r.rf.hom)
    (wh : r'.rh.hom ≫ A₂.t = A₁.t ≫ r.rh.hom)
    (wfh : r'.rfh.hom ≫ A₂.s = A₁.s ≫ r.rfh.hom) :
    compositionEhf B A₂ ≫ Functor.whiskerLeft (G B x) (compositionC B r'.rfh) =
      Functor.whiskerRight (compositionC B r.rfh) (G B g) ≫ compositionEhf B A₁ ∧
    compositionHorizontalE B A₂ ≫ Functor.whiskerLeft (G B x) (compositionH B r') =
      Functor.whiskerRight (compositionH B r) (G B g) ≫ compositionHorizontalE B A₁ := by
  have sf : IsPullback x f' f y := by
    simpa only [← T₁'.cf.comm, ← T₁.cf.comm] using A₁.cf_i.paste_vert A₁.cf_g
  have sh : IsPullback y h' h g := by
    simpa only [← T₁'.cg.comm, ← T₁.cg.comm] using A₁.cg_i.paste_vert A₁.cg_g
  have sfh : IsPullback x (f' ≫ h') (f ≫ h) g := by
    simpa only [← T₁'.cfg.comm, ← T₁.cfg.comm] using A₁.cfg_i.paste_vert A₁.cfg_g
  have ef := (refinementExchangeCoherence B (f := f) 0 (finiteOrigin_zero B X)).2.2.2.1
    x y sf T₁.cf T₂.cf T₁'.cf T₂'.cf A₁.d A₂.d
    A₁.cf_i A₁.cf_g A₂.cf_i A₂.cf_g r.rf r'.rf wf
  have eh := (refinementExchangeCoherence B (f := h) 0 (finiteOrigin_zero B Y)).2.2.2.1
    y g sh T₁.cg T₂.cg T₁'.cg T₂'.cg A₁.t A₂.t
    A₁.cg_i A₁.cg_g A₂.cg_i A₂.cg_g r.rh r'.rh wh
  have ehf := (refinementExchangeCoherence B (f := f ≫ h) 0
    (finiteOrigin_zero B X)).2.2.2.1
    x g sfh T₁.cfg T₂.cfg T₁'.cfg T₂'.cfg A₁.s A₂.s
    A₁.cfg_i A₁.cfg_g A₂.cfg_i A₂.cfg_g r.rfh r'.rfh wfh
  simp only [refinementComparison] at ef eh ehf
  refine ⟨ehf, ?_⟩
  ext M
  simpa only [compositionHorizontalE, compositionH, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc] using
    horizontalRefinement (compositionF B T₁.cf) (compositionF B T₂.cf)
      (compositionF B T₁.cg) (compositionF B T₂.cg)
      (compositionF B T₁'.cf) (compositionF B T₂'.cf)
      (compositionF B T₁'.cg) (compositionF B T₂'.cg)
      (G B x) (G B y) (G B g)
      (compositionC B r.rf) (compositionC B r.rh)
      (compositionC B r'.rf) (compositionC B r'.rh)
      (compositionEf B A₁) (compositionEf B A₂)
      (compositionEh B A₁) (compositionEh B A₂) ef eh M

/-- The horizontal and hf comparisons from a common refining compatible tower, on a
finite-origin input. In the node's right-to-left convention they are H₂⁻¹H₁ and C₂⁻¹C₁.
Source: Stacks, Tag 0F7J, common refinements
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionCommonComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T₁ T₂ S : Compactification.Triangle f h)
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i] [QuasiCompact T₁.cfg.i]
    [QuasiCompact T₁.q]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i] [QuasiCompact T₂.cfg.i]
    [QuasiCompact T₂.q]
    [QuasiCompact S.cf.i] [QuasiCompact S.cg.i] [QuasiCompact S.cfg.i]
    [QuasiCompact S.q]
    (r₁ : CompositionRefinement S T₁) (r₂ : CompositionRefinement S T₂)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    (((compositionF B T₁.cf ⋙ compositionF B T₁.cg).obj M ⟶
      (compositionF B T₂.cf ⋙ compositionF B T₂.cg).obj M) ×
      ((compositionF B T₁.cfg).obj M ⟶ (compositionF B T₂.cfg).obj M)) :=
  ⟨(compositionH B r₁).app M ≫
      @inv _ _ _ _ ((compositionH B r₂).app M)
        (compositionRefinement_isIso B f h S T₂ r₂ M hM).2,
    (compositionC B r₁.rfh).app M ≫
      @inv _ _ _ _ ((compositionC B r₂.rfh).app M)
        (compositionRefinement_isIso B f h S T₂ r₂ M hM).1⟩

/-- Transport through a common refining compatible tower preserves D, independently of
both the common tower and its refinement arrows.
Source: Stacks, Tag 0F7J, final choice-independence argument
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence).
Proof: the refinement equality for each of r₁,r₂ and their invertible boundaries
identifies H₂⁻¹H₁ followed by D₂ with D₁ followed by C₂⁻¹C₁.
The compactifications of hf are supplied compactifications of the same morphism.
The independence and cocycle in lem-cbc-complete-proetale-refinement-exchange-coherence,
applied there at M, identify C₂⁻¹C₁ for any second common tower and any arrows.
Since H = D₂⁻¹ (C₂⁻¹C₁) D₁, this also identifies the horizontal comparison.
The compatible-tower theorem supplies a common tower for any two choices.
Finally compositionRefinementExchange transports both boundary exchanges; substituting
these boundary equations in vertical interchange transports the whole identity through
each common tower. Thus both D and its interchange identity are independent of the
common refinement, as in node step 10. All equalities occur before evaluation. -/
theorem compositionCommonCoherence
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T₁ T₂ S : Compactification.Triangle f h)
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i] [QuasiCompact T₁.cfg.i]
    [QuasiCompact T₁.q]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i] [QuasiCompact T₂.cfg.i]
    [QuasiCompact T₂.q]
    [QuasiCompact S.cf.i] [QuasiCompact S.cg.i] [QuasiCompact S.cfg.i]
    [QuasiCompact S.q]
    (r₁ : CompositionRefinement S T₁) (r₂ : CompositionRefinement S T₂)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    (compositionCommonComparison B f h T₁ T₂ S r₁ r₂ M hM).1 ≫
        (compositionD B T₂).app M =
      (compositionD B T₁).app M ≫
        (compositionCommonComparison B f h T₁ T₂ S r₁ r₂ M hM).2 ∧
    (∀ (S' : Compactification.Triangle f h)
      [QuasiCompact S'.cf.i] [QuasiCompact S'.cg.i] [QuasiCompact S'.cfg.i]
      [QuasiCompact S'.q]
      (s₁ : CompositionRefinement S' T₁) (s₂ : CompositionRefinement S' T₂),
      compositionCommonComparison B f h T₁ T₂ S r₁ r₂ M hM =
        compositionCommonComparison B f h T₁ T₂ S' s₁ s₂ M hM) := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower
