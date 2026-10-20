/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension

/-!
# Composition pasting for strict constant-coefficient towers

Source: Stacks Project, Tags 0F7J, 0F7C, 0F7D and 0F7F, and the strict-tower adaptation
in the blueprint (blueprint: lem-cbc-complete-proetale-composition-pasting-coherence).

`Compactification.Triangle` names the node's maps as follows: `cf.i = c`, `cf.g = p_Y`,
`cg.i = i`, `cg.g = q`, `cfg.i = a`, `q = b`, and `p = p`.
All maps below are constructed in the derived category of strict towers, before evaluation.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The supplied-compactification functor `R_p J_j`.
Source: Stacks, Tag 0F7J
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionF {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Derived B X ⥤ Derived B Y := J B c.i ⋙ R B c.g

/-- The actual composition comparison `R_q gamma_Q J_c`, including both compositors.
Source: Stacks, Tag 0F7J
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionD {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    [QuasiCompact T.q] :
    compositionF B T.cf ⋙ compositionF B T.cg ⟶ compositionF B T.cfg :=
  (Functor.associator (J B T.cf.i) (R B T.cf.g) (J B T.cg.i ⋙ R B T.cg.g)).hom ≫
  Functor.whiskerLeft (J B T.cf.i)
    ((Functor.associator (R B T.cf.g) (J B T.cg.i) (R B T.cg.g)).inv ≫
      Functor.whiskerRight (gamma B T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
        (R B T.cg.g) ≫
      (Functor.associator (J B T.q) (R B T.p) (R B T.cg.g)).hom) ≫
  (Functor.associator (J B T.cf.i) (J B T.q) (R B T.p ⋙ R B T.cg.g)).inv ≫
  Functor.whiskerRight
    ((jComp B T.cf.i T.q).hom ≫ (jCongr B T.i_q).hom)
    (R B T.p ⋙ R B T.cg.g) ≫
  Functor.whiskerLeft (J B T.cfg.i)
    ((rComp B T.p T.cg.g).hom ≫ (eqToIso (congrArg (R B) T.p_g)).hom)

/-- The refinement comparison is gamma for the identity-left square, followed by R.
Source: Stacks, Tag 0F7J, choice independence
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionC {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d) : compositionF B d ⟶ compositionF B c :=
  Functor.whiskerRight
    ((Functor.leftUnitor (J B d.i)).inv ≫
      Functor.whiskerRight (rId B X).inv (J B d.i) ≫
      gamma B c.i (𝟙 X) r.hom d.i (r.i_hom.trans (Category.id_comp d.i).symm))
    (R B d.g) ≫
  (Functor.associator (J B c.i) (R B r.hom) (R B d.g)).hom ≫
  Functor.whiskerLeft (J B c.i)
    ((rComp B r.hom d.g).hom ≫ (eqToIso (congrArg (R B) r.hom_g)).hom)

/-- The specified exchange: first the proper-square mate, then the open comparison.
Source: Stacks, Tag 0F7F
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionE {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (wi : x ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ y)
    (si : IsPullback x c'.i c.i s) :
    compositionF B c ⋙ G B y ⟶ G B x ⋙ compositionF B c' :=
  (Functor.associator (J B c.i) (R B c.g) (G B y)).hom ≫
  Functor.whiskerLeft (J B c.i) (exchange B s c'.g c.g y wp) ≫
  (Functor.associator (J B c.i) (G B s) (R B c'.g)).inv ≫
  Functor.whiskerRight (beta B x c'.i c.i s wi si).hom (R B c'.g) ≫
  (Functor.associator (G B x) (J B c'.i) (R B c'.g)).hom

/-- A refinement of the supplied towers consists of the three existing compactification
refinements and the two remaining compatibility equations. No cartesian condition is imposed.
Source: Stacks, Tag 0F7J, refinement diagram; compatible-tower dependency
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
structure CompositionRefinement {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T₁ T₂ : Compactification.Triangle f h) where
  rf : T₁.cf.Refinement T₂.cf
  rh : T₁.cg.Refinement T₂.cg
  rfh : T₁.cfg.Refinement T₂.cfg
  b_comm : T₁.q ≫ rfh.hom = rf.hom ≫ T₂.q
  p_comm : rfh.hom ≫ T₂.p = T₁.p ≫ rh.hom

/-- The horizontal refinement `(C_h F_f1)(F_h2 C_f)`.
Source: Stacks, Tag 0F7J
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionH {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    {T₁ T₂ : Compactification.Triangle f h}
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i]
    (r : CompositionRefinement T₁ T₂) :
    compositionF B T₂.cf ⋙ compositionF B T₂.cg ⟶
      compositionF B T₁.cf ⋙ compositionF B T₁.cg :=
  Functor.whiskerRight (compositionC B r.rf) (compositionF B T₂.cg) ≫
    Functor.whiskerLeft (compositionF B T₁.cf) (compositionC B r.rh)

/-- The cartesian faces of a base change of a supplied compatible tower. All arrows
are supplied projections; this does not choose a compactification or an arbitrary comparison.
Source: Stacks, Tags 0F7J and 0F7F; compatible-tower dependency
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
structure CompositionBaseChange {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (g : Z' ⟶ Z) where
  d : T'.cf.Z ⟶ T.cf.Z
  t : T'.cg.Z ⟶ T.cg.Z
  s : T'.cfg.Z ⟶ T.cfg.Z
  cf_i : IsPullback x T'.cf.i T.cf.i d
  cf_g : IsPullback d T'.cf.g T.cf.g y
  cg_i : IsPullback y T'.cg.i T.cg.i t
  cg_g : IsPullback t T'.cg.g T.cg.g g
  cfg_i : IsPullback x T'.cfg.i T.cfg.i s
  cfg_g : IsPullback s T'.cfg.g T.cfg.g g
  b : IsPullback d T'.q T.q s
  p : IsPullback s T'.p T.p t

/-- Exchange for f on the supplied pulled-back tower.
Source: Stacks, Tag 0F7F
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionEf {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE B T.cf T'.cf x y A.d A.cf_i.w A.cf_g.w A.cf_i

/-- Exchange for h on the supplied pulled-back tower.
Source: Stacks, Tag 0F7F
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionEh {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE B T.cg T'.cg y g A.t A.cg_i.w A.cg_g.w A.cg_i

/-- Exchange for hf on the supplied pulled-back tower.
Source: Stacks, Tag 0F7F
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionEhf {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE B T.cfg T'.cfg x g A.s A.cfg_i.w A.cfg_g.w A.cfg_i

/-- The horizontal exchange `(F_h' e_f)(e_h F_f)` with explicit associators.
Source: Stacks, Tag 0F7F
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionHorizontalE {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :
    (compositionF B T.cf ⋙ compositionF B T.cg) ⋙ G B g ⟶
      G B x ⋙ (compositionF B T'.cf ⋙ compositionF B T'.cg) :=
  (Functor.associator (compositionF B T.cf) (compositionF B T.cg) (G B g)).hom ≫
  Functor.whiskerLeft (compositionF B T.cf) (compositionEh B A) ≫
  (Functor.associator (compositionF B T.cf) (G B y) (compositionF B T'.cg)).inv ≫
  Functor.whiskerRight (compositionEf B A) (compositionF B T'.cg) ≫
  (Functor.associator (G B x) (compositionF B T'.cf) (compositionF B T'.cg)).hom

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
  sorry

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
  sorry

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
