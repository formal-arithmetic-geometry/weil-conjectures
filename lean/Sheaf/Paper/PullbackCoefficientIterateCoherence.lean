/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Endomorphism
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence

/-!
# Pullback comparisons and coefficient-map iterates

Source: the blueprint, `sec-trace-formula/sk-i-global-additivity`,
`prop-trf-trace-additivity-open-closed.proof.md`, Steps 1 and 6; Stacks Project,
Tags 03D8 and 0D6D (blueprint: lem-trf-pullback-coefficient-iterate-coherence).

The helper declarations render the powers, comparisons and recursion explicitly
introduced by this node; the main theorem states its two displayed identities.

The powers below are powers of scheme endomorphisms, not powers of a chosen pullback
functor. At exponent zero the comparisons are the canonical unital comparisons for
pullback of the identity morphism. Positive coefficient iterates are indexed by `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v v' u'

open CategoryTheory

namespace AlgebraicGeometry.Scheme

-- Keep categorical calculations from unfolding the termwise derived-pullback construction.
set_option allowUnsafeReducibility true in
attribute [local irreducible] proEtaleConstantRingPullbackComposition
  proEtaleCanonicalPullbackComposition proEtaleConstantRingDerivedPullback
  proEtaleRingModuleAdjunctionNormalized proEtaleRingModuleUnitSection
  proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors
  CochainComplex.IsAcyclicTensorKFlat SheafOfModules.IsFlatOnSite
  proEtaleRingModulePullback proEtaleConstantRingComparison proEtaleRingDirectImageMap

/-- Powers of a commuting square still commute.
Source: blueprint, trace additivity proof, Step 1
(blueprint: lem-trf-pullback-coefficient-iterate-coherence).
Proof: for exponent zero use the identity laws. For the successor, write each power
as its preceding power followed by the endomorphism. Reassociate, use the original
square, then the induction hypothesis, and reassociate back. This is Step 5 of the
node's proof, before applying the pullback-composition comparisons. -/
theorem trf_commuting_endomorphism_powers {W X : Scheme.{u}} (h : W ⟶ X)
    (tW : W ⟶ W) (t : X ⟶ X) (w : tW ≫ h = h ≫ t) (m : ℕ) :
    ((End.of tW) ^ m : W ⟶ W) ≫ h = h ≫ ((End.of t) ^ m : X ⟶ X) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, pow_succ, End.mul_def, End.mul_def, Category.assoc, ih,
        ← Category.assoc, w]
      simp only [Category.assoc]

/-- The canonical comparison around an arbitrary commuting square, with no Cartesian
assumption. It is the two recorded composition comparisons joined by transport along
the equality of composite scheme morphisms.
Source: blueprint, trace additivity proof, Step 1; Stacks Tag 0D6D
(blueprint: lem-trf-pullback-coefficient-iterate-coherence). -/
def trfPullbackSquareComparison (A : Type u) [CommRing A]
    {W X : Scheme.{u}} (h : W ⟶ X) (a : W ⟶ W) (b : X ⟶ X)
    (w : a ≫ h = h ≫ b) :
    proEtaleConstantRingDerivedPullback A h ⋙ proEtaleConstantRingDerivedPullback A a ≅
      proEtaleConstantRingDerivedPullback A b ⋙ proEtaleConstantRingDerivedPullback A h :=
  proEtaleConstantRingPullbackComposition a h A ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) w) ≪≫
    (proEtaleConstantRingPullbackComposition h b A).symm

/-- The specified comparison `d_m : P_(m+1) ≅ P_1 P_m`, including the canonical
identity comparison at `m = 0`. The only transport is the standard power equality.
Source: blueprint, trace additivity proof, Step 1; Stacks Tag 0D6D
(blueprint: lem-trf-pullback-coefficient-iterate-coherence). -/
def trfPullbackPowerStep (A : Type u) [CommRing A] {X : Scheme.{u}}
    (t : X ⟶ X) (m : ℕ) :
    proEtaleConstantRingDerivedPullback A ((End.of t) ^ (m + 1)) ≅
      proEtaleConstantRingDerivedPullback A ((End.of t) ^ m) ⋙
        proEtaleConstantRingDerivedPullback A t :=
  eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) (pow_succ (End.of t) m)) ≪≫
    (proEtaleConstantRingPullbackComposition t ((End.of t) ^ m) A).symm

/-- The coefficient morphism `u_(n+1)`, with `u_1 = u` after the canonical transport
along `t^1 = t`, and `u_(m+1) = u ∘ P_1(u_m) ∘ d_m` thereafter.
Source: blueprint, trace additivity proof, Steps 1 and 6
(blueprint: lem-trf-pullback-coefficient-iterate-coherence). -/
def trfCoefficientIterate (A : Type u) [CommRing A] {X : Scheme.{u}}
    (t : X ⟶ X) (K : proEtaleDerivedCategory X A)
    (f : (proEtaleConstantRingDerivedPullback A t).obj K ⟶ K) :
    (n : ℕ) → (proEtaleConstantRingDerivedPullback A ((End.of t) ^ (n + 1))).obj K ⟶ K
  | 0 => (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
      (pow_one (End.of t)))).hom.app K ≫ f
  | n + 1 => (trfPullbackPowerStep A t (n + 1)).hom.app K ≫
      (proEtaleConstantRingDerivedPullback A t).map (trfCoefficientIterate A t K f n) ≫ f

private theorem square_formula (A : Type u) [CommRing A]
    {W X : Scheme.{u}} (h : W ⟶ X) (a : W ⟶ W) (b : X ⟶ X)
    (w : a ≫ h = h ≫ b) :
    trfPullbackSquareComparison A h a b w =
      proEtaleConstantRingPullbackComposition a h A ≪≫
        eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) w) ≪≫
          (proEtaleConstantRingPullbackComposition h b A).symm := rfl

private theorem step_formula (A : Type u) [CommRing A] {X : Scheme.{u}}
    (t : X ⟶ X) (m : ℕ) :
    trfPullbackPowerStep A t m =
      eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) (pow_succ (End.of t) m)) ≪≫
        (proEtaleConstantRingPullbackComposition t ((End.of t) ^ m) A).symm := rfl

private theorem iterate_zero_formula (A : Type u) [CommRing A] {X : Scheme.{u}}
    (t : X ⟶ X) (K : proEtaleDerivedCategory X A)
    (f : (proEtaleConstantRingDerivedPullback A t).obj K ⟶ K) :
    trfCoefficientIterate A t K f 0 =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
        (pow_one (End.of t)))).hom.app K ≫ f := rfl

private theorem iterate_succ_formula (A : Type u) [CommRing A] {X : Scheme.{u}}
    (t : X ⟶ X) (K : proEtaleDerivedCategory X A)
    (f : (proEtaleConstantRingDerivedPullback A t).obj K ⟶ K) (n : ℕ) :
    trfCoefficientIterate A t K f n.succ =
      (trfPullbackPowerStep A t (n + 1)).hom.app K ≫
        (proEtaleConstantRingDerivedPullback A t).map (trfCoefficientIterate A t K f n) ≫ f :=
  trfCoefficientIterate.eq_2 A t K f n

private theorem coefficient_step
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (H : C ⥤ D) (P : C ⥤ C) (Q : D ⥤ D)
    (e : H ⋙ Q ≅ P ⋙ H) (Pₙ Pₛ : C ⥤ C) (Qₙ Qₛ : D ⥤ D)
    (cₙ : H ⋙ Qₙ ≅ Pₙ ⋙ H) (cₛ : H ⋙ Qₛ ≅ Pₛ ⋙ H)
    (dP : Pₛ ≅ Pₙ ⋙ P) (dQ : Qₛ ≅ Qₙ ⋙ Q)
    (K : C) (f : P.obj K ⟶ K) (fₙ : Pₙ.obj K ⟶ K)
    (gₙ : Qₙ.obj (H.obj K) ⟶ H.obj K)
    (ih : gₙ = cₙ.hom.app K ≫ H.map fₙ)
    (hc : cₛ.hom.app K ≫ H.map (dP.hom.app K) =
      dQ.hom.app (H.obj K) ≫ Q.map (cₙ.hom.app K) ≫ e.hom.app (Pₙ.obj K)) :
    dQ.hom.app (H.obj K) ≫ Q.map gₙ ≫
        (e.hom.app K ≫ H.map f) =
      cₛ.hom.app K ≫ H.map (dP.hom.app K ≫ P.map fₙ ≫ f) := by
  rw [ih]
  have hn := e.hom.naturality fₙ
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← reassoc_of% hc]

@[reassoc] private theorem transport_right₂
    {C D E : Type*} [Category C] [Category D] [Category E] {T : Type*}
    (F : T → (C ⥤ D)) (G : D ⥤ E) (H : T → (C ⥤ E))
    (c : ∀ t, F t ⋙ G ≅ H t) {t t' : T} (e : t = t') (K : C) :
    (c t).inv.app K ≫ G.map ((eqToIso (congrArg F e)).hom.app K) =
      (eqToIso (congrArg H e)).hom.app K ≫ (c t').inv.app K := by
  cases e
  simp

@[reassoc] private theorem transport_left₂
    {C D E : Type*} [Category C] [Category D] [Category E] {T : Type*}
    (F : T → (D ⥤ E)) (G : C ⥤ D) (H : T → (C ⥤ E))
    (c : ∀ t, G ⋙ F t ≅ H t) {t t' : T} (e : t = t') (K : C) :
    (c t).inv.app K ≫ (eqToIso (congrArg F e)).hom.app (G.obj K) =
      (eqToIso (congrArg H e)).hom.app K ≫ (c t').inv.app K := by
  cases e
  simp

-- Use two fixed categories so specialization retains their category instances.
section
variable {C : Type v} {D : Type v'} [Category C] [Category D]
variable {W X : Scheme.{u}}
variable (P : (X ⟶ X) → (C ⥤ C)) (Q : (W ⟶ W) → (D ⥤ D))
variable (H : (W ⟶ X) → (C ⥤ D))
variable (cX : ∀ f g, P g ⋙ P f ≅ P (f ≫ g))
variable (cW : ∀ f g, Q g ⋙ Q f ≅ Q (f ≫ g))
variable (cL : ∀ f g, H g ⋙ Q f ≅ H (f ≫ g))
variable (cR : ∀ f g, P g ⋙ H f ≅ H (f ≫ g))
variable (hcR : ∀ (j : W ⟶ X) (h k : X ⟶ X) (K : C),
    (cR j (h ≫ k)).inv.app K ≫ (H j).map ((cX h k).inv.app K) =
      (eqToIso (congrArg H (Category.assoc j h k).symm)).hom.app K ≫
        (cR (j ≫ h) k).inv.app K ≫ (cR j h).inv.app ((P k).obj K))
variable (hcM : ∀ (j : W ⟶ W) (h : W ⟶ X) (k : X ⟶ X) (K : C),
    (cL j (h ≫ k)).inv.app K ≫ (Q j).map ((cR h k).inv.app K) =
      (eqToIso (congrArg H (Category.assoc j h k).symm)).hom.app K ≫
        (cR (j ≫ h) k).inv.app K ≫ (cL j h).inv.app ((P k).obj K))
variable (hcL : ∀ (j h : W ⟶ W) (k : W ⟶ X) (K : C),
    (cL j (h ≫ k)).inv.app K ≫ (Q j).map ((cL h k).inv.app K) =
      (eqToIso (congrArg H (Category.assoc j h k).symm)).hom.app K ≫
        (cL (j ≫ h) k).inv.app K ≫ (cW j h).inv.app ((H k).obj K))

include hcL in
@[reassoc] private theorem assoc_reverse₂
    (j h : W ⟶ W) (k : W ⟶ X) (K : C) :
    (cL (j ≫ h) k).inv.app K ≫ (cW j h).inv.app ((H k).obj K) =
      (eqToIso (congrArg H (Category.assoc j h k))).hom.app K ≫
        (cL j (h ≫ k)).inv.app K ≫ (Q j).map ((cL h k).inv.app K) := by
  have ht := congrArg (fun q ↦
    (eqToIso (congrArg H (Category.assoc j h k))).hom.app K ≫ q) (hcL j h k K)
  simpa only [Category.assoc, eqToIso.hom, eqToHom_app, eqToHom_trans_assoc,
    eqToHom_refl, NatTrans.id_app, Category.id_comp] using ht.symm

include hcR hcM hcL in
private theorem power_cocycle₂
    (h : W ⟶ X) (tW : W ⟶ W) (t : X ⟶ X) (w : tW ≫ h = h ≫ t) (m : ℕ)
    (wm : ((End.of tW) ^ m : W ⟶ W) ≫ h = h ≫ ((End.of t) ^ m : X ⟶ X))
    (ws : ((End.of tW) ^ (m + 1) : W ⟶ W) ≫ h =
      h ≫ ((End.of t) ^ (m + 1) : X ⟶ X)) (K : C) :
    (cL ((End.of tW) ^ (m + 1)) h ≪≫ eqToIso (congrArg H ws) ≪≫
        (cR h ((End.of t) ^ (m + 1))).symm).hom.app K ≫
        (H h).map ((eqToIso (congrArg P (pow_succ (End.of t) m)) ≪≫
          (cX t ((End.of t) ^ m)).symm).hom.app K) =
      (eqToIso (congrArg Q (pow_succ (End.of tW) m)) ≪≫
          (cW tW ((End.of tW) ^ m)).symm).hom.app ((H h).obj K) ≫
        (Q tW).map ((cL ((End.of tW) ^ m) h ≪≫ eqToIso (congrArg H wm) ≪≫
          (cR h ((End.of t) ^ m)).symm).hom.app K) ≫
        (cL tW h ≪≫ eqToIso (congrArg H w) ≪≫
          (cR h t).symm).hom.app ((P ((End.of t) ^ m)).obj K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  apply (cancel_epi ((cL ((End.of tW) ^ (m + 1)) h).inv.app K)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [transport_right₂_assoc P (H h) (fun g ↦ H (h ≫ g)) (cR h)
    (pow_succ (End.of t) m) K]
  simp only [End.mul_def]
  rw [hcR h t ((End.of t) ^ m) K]
  conv_rhs => rw [transport_left₂_assoc Q (H h) (fun f ↦ H (f ≫ h))
    (fun f ↦ cL f h)
    (show ((End.of tW) ^ (m + 1) : W ⟶ W) = tW ≫ ((End.of tW) ^ m) from
      pow_succ (End.of tW) m) K]
  conv_rhs =>
    enter [2]
    rw [assoc_reverse₂_assoc Q H cW cL hcL tW ((End.of tW) ^ m) h K]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  conv_rhs => rw [transport_right₂_assoc H (Q tW) (fun g ↦ H (tW ≫ g)) (cL tW) wm K]
  conv_rhs => rw [reassoc_of% (hcM tW h ((End.of t) ^ m) K)]
  simp only [Iso.inv_hom_id_app_assoc]
  conv_rhs => rw [transport_left₂_assoc H (P ((End.of t) ^ m))
    (fun f ↦ H (f ≫ ((End.of t) ^ m))) (fun f ↦ cR f ((End.of t) ^ m)) w K]
  simp only [eqToIso.hom, eqToHom_app, eqToHom_trans_assoc]

private theorem coefficient_zero₂
    (h : W ⟶ X) (tW : W ⟶ W) (t : X ⟶ X) (w : tW ≫ h = h ≫ t)
    {a : W ⟶ W} {b : X ⟶ X} (ea : a = tW) (eb : b = t)
    (w₁ : a ≫ h = h ≫ b) (K : C) (f : (P t).obj K ⟶ K) :
    (eqToIso (congrArg Q ea)).hom.app ((H h).obj K) ≫
        ((cL tW h ≪≫ eqToIso (congrArg H w) ≪≫ (cR h t).symm).hom.app K ≫
          (H h).map f) =
      (cL a h ≪≫ eqToIso (congrArg H w₁) ≪≫ (cR h b).symm).hom.app K ≫
        (H h).map ((eqToIso (congrArg P eb)).hom.app K ≫ f) := by
  cases ea
  cases eb
  simp

variable (h : W ⟶ X) (tW : W ⟶ W) (t : X ⟶ X) (w : tW ≫ h = h ≫ t) (K : C)
variable (S : ∀ (a : W ⟶ W) (b : X ⟶ X),
  a ≫ h = h ≫ b → (H h ⋙ Q a ≅ P b ⋙ H h))
variable (dP : ∀ m : ℕ, P ((End.of t) ^ (m + 1)) ≅ P ((End.of t) ^ m) ⋙ P t)
variable (dQ : ∀ m : ℕ, Q ((End.of tW) ^ (m + 1)) ≅ Q ((End.of tW) ^ m) ⋙ Q tW)
variable (I : ((P t).obj K ⟶ K) → (n : ℕ) → (P ((End.of t) ^ (n + 1))).obj K ⟶ K)
variable (J : ((Q tW).obj ((H h).obj K) ⟶ (H h).obj K) →
  (n : ℕ) → (Q ((End.of tW) ^ (n + 1))).obj ((H h).obj K) ⟶ (H h).obj K)
variable (hs : ∀ (a : W ⟶ W) (b : X ⟶ X) (w : a ≫ h = h ≫ b),
    S a b w = cL a h ≪≫ eqToIso (congrArg H w) ≪≫ (cR h b).symm)
variable (hdP : ∀ m : ℕ, dP m = eqToIso (congrArg P (pow_succ (End.of t) m)) ≪≫
    (cX t ((End.of t) ^ m)).symm)
variable (hdQ : ∀ m : ℕ, dQ m = eqToIso (congrArg Q (pow_succ (End.of tW) m)) ≪≫
    (cW tW ((End.of tW) ^ m)).symm)
variable (hi0 : ∀ f, I f 0 = (eqToIso (congrArg P (pow_one (End.of t)))).hom.app K ≫ f)
variable (hj0 : ∀ f, J f 0 =
    (eqToIso (congrArg Q (pow_one (End.of tW)))).hom.app ((H h).obj K) ≫ f)
variable (his : ∀ f n, I f n.succ = (dP (n + 1)).hom.app K ≫ (P t).map (I f n) ≫ f)
variable (hjs : ∀ f n, J f n.succ = (dQ (n + 1)).hom.app ((H h).obj K) ≫
    (Q tW).map (J f n) ≫ f)
include hcR hcM hcL hs hdP hdQ hi0 hj0 his hjs

private theorem coherence_two_categories :
    (∀ m : ℕ,
      (S ((End.of tW) ^ (m + 1)) ((End.of t) ^ (m + 1))
        (trf_commuting_endomorphism_powers h tW t w (m + 1))).hom.app K ≫
          (H h).map ((dP m).hom.app K) =
        (dQ m).hom.app ((H h).obj K) ≫
          (Q tW).map ((S ((End.of tW) ^ m) ((End.of t) ^ m)
            (trf_commuting_endomorphism_powers h tW t w m)).hom.app K) ≫
          (S tW t w).hom.app ((P ((End.of t) ^ m)).obj K)) ∧
      (∀ f n,
        J ((S tW t w).hom.app K ≫ (H h).map f) n =
          (S ((End.of tW) ^ (n + 1)) ((End.of t) ^ (n + 1))
            (trf_commuting_endomorphism_powers h tW t w (n + 1))).hom.app K ≫
              (H h).map (I f n)) := by
  have hcoh (m : ℕ) :
      (S ((End.of tW) ^ (m + 1)) ((End.of t) ^ (m + 1))
        (trf_commuting_endomorphism_powers h tW t w (m + 1))).hom.app K ≫
          (H h).map ((dP m).hom.app K) =
        (dQ m).hom.app ((H h).obj K) ≫
          (Q tW).map ((S ((End.of tW) ^ m) ((End.of t) ^ m)
            (trf_commuting_endomorphism_powers h tW t w m)).hom.app K) ≫
          (S tW t w).hom.app ((P ((End.of t) ^ m)).obj K) := by
    simp only [hs, hdP, hdQ]
    exact power_cocycle₂ P Q H cX cW cL cR hcR hcM hcL h tW t w m
      (trf_commuting_endomorphism_powers h tW t w m)
      (trf_commuting_endomorphism_powers h tW t w (m + 1)) K
  refine ⟨hcoh, ?_⟩
  intro f n
  induction n with
  | zero =>
      simp only [hi0, hj0, hs]
      exact coefficient_zero₂ P Q H cL cR h tW t w
        (pow_one (End.of tW)) (pow_one (End.of t))
        (trf_commuting_endomorphism_powers h tW t w 1) K f
  | succ n ih =>
      rw [his, hjs]
      exact coefficient_step (H h) (P t) (Q tW) (S tW t w)
        (P ((End.of t) ^ (n + 1))) (P ((End.of t) ^ (n + 1 + 1)))
        (Q ((End.of tW) ^ (n + 1))) (Q ((End.of tW) ^ (n + 1 + 1)))
        (S ((End.of tW) ^ (n + 1)) ((End.of t) ^ (n + 1))
          (trf_commuting_endomorphism_powers h tW t w (n + 1)))
        (S ((End.of tW) ^ (n + 1 + 1)) ((End.of t) ^ (n + 1 + 1))
          (trf_commuting_endomorphism_powers h tW t w (n + 1 + 1)))
        (dP (n + 1)) (dQ (n + 1)) K f (I f n) _ ih (hcoh (n + 1))

end

/-- Canonical pullback comparisons satisfy the cocycle for every nonnegative exponent
and intertwine every positive coefficient iterate, without any invertibility,
finite-type, or Cartesian-square hypothesis.
Source: blueprint, trace additivity proof, Steps 1 and 6; Stacks Tags 03D8, 0B65,
0DV0 and 0D6D (blueprint: lem-trf-pullback-coefficient-iterate-coherence).

Proof (the six steps of the node):
1. The direct-image composition maps are the fibre-product pasting maps. Their
   associativity and units follow from their two projections. Their constant-ring
   maps send each constant to itself, so the scalar identifications also compose.
2. Use the composite adjunction and conjugate-iso unit equation to characterize
   the ordinary module pullback comparisons uniquely. On tensors the forward map
   inserts a scalar unit, and the inverse multiplies scalars; balancing verifies
   the normalization and inverse identities.
3. Both triple comparisons transpose to the same three successive units. The
   conjugate-iso uniqueness gives associativity, and the identity adjunction gives
   the unit laws, on all module sheaves.
4. Exact termwise pullback descends through localization. The localization universal
   property preserves composition and is faithful on natural transformations, so
   associativity and units descend. On flat K-flat resolutions these are exactly
   the comparisons of the recorded composition lemma; naturality across the
   resolution quasi-isomorphism identifies them on every derived object.
5. The commuting-power equality follows by induction. Apply associativity to the
   triples `(h,t,t^m)`, `(tW,h,t^m)` and `(tW,tW^m,h)`, substitute the commuting
   equalities, and cancel the two inverse composition comparisons. This gives the
   first displayed identity, including exponent zero by the same associativity calculation.
6. Induct on the positive coefficient exponent. The first case is the definition
   of the pulled-back coefficient map. In the successor step expand the recursion,
   use naturality of `c_1` at the preceding iterate, then the first identity and
   functoriality of pullback. No inverse of the coefficient morphism is used. -/
theorem trf_pullback_coefficient_iterate_coherence (A : Type u) [CommRing A] [Finite A]
    {W X : Scheme.{u}} (h : W ⟶ X) (tW : W ⟶ W) (t : X ⟶ X)
    (w : tW ≫ h = h ≫ t) (K : proEtaleDerivedCategory X A) :
    (∀ m : ℕ,
      (trfPullbackSquareComparison A h ((End.of tW) ^ (m + 1))
        ((End.of t) ^ (m + 1)) (trf_commuting_endomorphism_powers h tW t w (m + 1))).hom.app K ≫
          (proEtaleConstantRingDerivedPullback A h).map ((trfPullbackPowerStep A t m).hom.app K) =
        (trfPullbackPowerStep A tW m).hom.app
            ((proEtaleConstantRingDerivedPullback A h).obj K) ≫
          (proEtaleConstantRingDerivedPullback A tW).map
            ((trfPullbackSquareComparison A h ((End.of tW) ^ m) ((End.of t) ^ m)
              (trf_commuting_endomorphism_powers h tW t w m)).hom.app K) ≫
          (trfPullbackSquareComparison A h tW t w).hom.app
            ((proEtaleConstantRingDerivedPullback A ((End.of t) ^ m)).obj K)) ∧
      (∀ (f : (proEtaleConstantRingDerivedPullback A t).obj K ⟶ K) (n : ℕ),
        trfCoefficientIterate A tW ((proEtaleConstantRingDerivedPullback A h).obj K)
            ((trfPullbackSquareComparison A h tW t w).hom.app K ≫
              (proEtaleConstantRingDerivedPullback A h).map f) n =
          (trfPullbackSquareComparison A h ((End.of tW) ^ (n + 1))
              ((End.of t) ^ (n + 1))
              (trf_commuting_endomorphism_powers h tW t w (n + 1))).hom.app K ≫
            (proEtaleConstantRingDerivedPullback A h).map (trfCoefficientIterate A t K f n)) := by
  -- Pass the functor families directly to avoid expanding them through eta conversion.
  exact coherence_two_categories
    (@proEtaleConstantRingDerivedPullback A _ X X)
    (@proEtaleConstantRingDerivedPullback A _ W W)
    (@proEtaleConstantRingDerivedPullback A _ W X)
    (fun f g ↦ proEtaleConstantRingPullbackComposition f g A)
    (fun f g ↦ proEtaleConstantRingPullbackComposition f g A)
    (fun f g ↦ proEtaleConstantRingPullbackComposition f g A)
    (fun f g ↦ proEtaleConstantRingPullbackComposition f g A)
    (fun j h k K ↦ proEtaleConstantRingDerivedPullback_composition_coherence j h k A K)
    (fun j h k K ↦ proEtaleConstantRingDerivedPullback_composition_coherence j h k A K)
    (fun j h k K ↦ proEtaleConstantRingDerivedPullback_composition_coherence j h k A K)
    h tW t w K (trfPullbackSquareComparison A h)
    (trfPullbackPowerStep A t) (trfPullbackPowerStep A tW)
    (trfCoefficientIterate A t K)
    (trfCoefficientIterate A tW ((proEtaleConstantRingDerivedPullback A h).obj K))
    (square_formula A h) (step_formula A t) (step_formula A tW)
    (iterate_zero_formula A t K)
    (iterate_zero_formula A tW ((proEtaleConstantRingDerivedPullback A h).obj K))
    (iterate_succ_formula A t K)
    (iterate_succ_formula A tW ((proEtaleConstantRingDerivedPullback A h).obj K))

end AlgebraicGeometry.Scheme
