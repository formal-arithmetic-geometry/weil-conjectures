/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsBase
import WeilConjectures.AlgebraicGeometry.CondensedCompactReturnCoherence
import WeilConjectures.AlgebraicGeometry.CondensedIterateStructureNormalization

/-! Strict subgoal of the global condensed model Frobenius comparison. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

open CondensedOpenProper

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

private theorem power_return_induction {M : Type*} [Monoid M]
    (F : ℕ → M) (hstep : ∀ n : ℕ, F (n + 1) = F 1 * F n) :
    ∀ m : ℕ, 1 ≤ m → F m = F 1 ^ m := by
  intro m
  induction m with
  | zero =>
    intro hm
    omega
  | succ n ih =>
    intro hm
    by_cases hn : n = 0
    · subst n
      exact (pow_one (F 1)).symm
    · rw [hstep n, ih (by omega), pow_succ']

private theorem isIso_pow_return
    {C : Type*} [Category C] {T : C} (f : End T) [IsIso f] (n : ℕ) :
    IsIso (f ^ n) := by
  induction n with
  | zero =>
    change IsIso (𝟙 T)
    infer_instance
  | succ n ih =>
    let := ih
    simpa only [pow_succ, End.mul_def] using (inferInstance : IsIso (f ≫ f ^ n))

private theorem compactReturn_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Z : Scheme.{u}} {k : Type u} [Field k] [IsSepClosed k]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Spec (.of k))
    (g g' : End X) (gZ : End Z) (gS : End (Spec (.of k))) (e : g = g')
    (wj : g ≫ j = j ≫ gZ) (wj' : g' ≫ j = j ≫ gZ)
    (wp : gZ ≫ p = p ≫ gS) {L : D Λ X} (θ : (P Λ g').obj L ⟶ L) :
    compactReturn Λ j p g gZ gS wj wp
        (eqToHom (congrArg (fun a : End X ↦ (P Λ a).obj L) e) ≫ θ) =
      compactReturn Λ j p g' gZ gS wj' wp θ := by
  subst g'
  simp only [eqToHom_refl, Category.id_comp]

set_option maxHeartbeats 1200000 in
-- Dependent transports compare model pullback functors on the large derived categories.
/-- The compact-return power law, the first strict subgoal of the global theorem.
Source: latest blueprint, `lem-fd-realness-pushforward.proof.md`, Step 1;
original operator comparison proof steps 4--11.
(blueprint: lem-fd-condensed-model-frobenius-global-power).

Proof: normalize the proper mate as successive derived restriction and the inverse
open mate as the specified Cartesian open exchange. Their pasting equations give
the compact-exchange composition law. Exact derivation of the ordinary point
trivialization law gives its matching composition law. Naturality combines these
into a compact-return law. The defining successor recursion of iterateStructure,
its degree-one unit normalization, and induction give the displayed equality of
actual derived morphisms. -/
theorem condensed_model_frobenius_global_power
    [IsSeparated X₀.hom] (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D₀.p)]
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D₀ X₀)) (c₀ : Compactification X₀.hom)
    (w : Factorization D₀ X₀)
    (hB : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D₀.geometricFiber X₀).left)
      K.carrier.obj)
    (hf : ∀ m : ℕ, IsFinite (frobeniusIterate (modelEnd D₀ X₀) m).left)
    (hu : ∀ m : ℕ, IsUniversalHomeomorphism (frobeniusIterate (modelEnd D₀ X₀) m).left)
    (wj : ∀ m : ℕ,
      ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m) ≫
          (geometricCompactification D₀ X₀ c₀).i =
        (geometricCompactification D₀ X₀ c₀).i ≫
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m))
    (wp : ∀ m : ℕ,
      ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m) ≫
          (geometricCompactification D₀ X₀ c₀).g =
        (geometricCompactification D₀ X₀ c₀).g ≫
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m)) :
(∀ m : ℕ, 1 ≤ m →
        compactReturn (Profinite.padicAlgClRingObj ell)
          (geometricCompactification D₀ X₀ c₀).i (geometricCompactification D₀ X₀ c₀).g
          ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m)
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m)
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) (wj m) (wp m)
          (iterateStructure (Profinite.padicAlgClRingObj ell)
            (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) m).hom =
        (compactReturn (Profinite.padicAlgClRingObj ell)
          (geometricCompactification D₀ X₀ c₀).i (geometricCompactification D₀ X₀ c₀).g
          ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ 1)
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ 1)
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ 1) (wj 1) (wp 1)
          (iterateStructure (Profinite.padicAlgClRingObj ell)
            (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) 1).hom) ^ m) := by
  have _ := w
  have _ := hB
  have _ := hf
  have _ := hu
  let Λ := Profinite.padicAlgClRingObj ell
  let j := (geometricCompactification D₀ X₀ c₀).i
  let p := (geometricCompactification D₀ X₀ c₀).g
  let fX := End.of (StrictWeil.modelFrobenius D₀ X₀).hom
  let fZ := End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom
  let fS := End.of (StrictWeil.pointFrobenius D₀).hom
  let θ := ambientStructure _ K
  let : IsIso fX := inferInstance
  let : IsIso fZ := inferInstance
  let : IsIso fS := inferInstance
  have hΛ : IsAdmissibleCoefficient Λ := by
    refine ⟨ell, inferInstance, ?_⟩
    right; right; right; right; right
    exact ⟨Iso.refl _⟩
  have wj1 : fX ≫ j = j ≫ fZ := by simpa only [pow_one] using wj 1
  have wp1 : fZ ≫ p = p ≫ fS := by simpa only [pow_one] using wp 1
  let F : ℕ → End ((J Λ j ⋙ R Λ p).obj K.carrier.obj) := fun n =>
    compactReturn Λ j p (fX ^ n) (fZ ^ n) (fS ^ n) (wj n) (wp n)
      (iterateStructure Λ fX θ n).hom
  have hone : F 1 = compactReturn Λ j p fX fZ fS wj1 wp1 θ.hom := by
    dsimp only [F]
    rw [iterateStructure_one]
    have wjr : fX ≫ j = j ≫ fZ ^ 1 := by simpa only [pow_one] using wj1
    rw [compactReturn_transport Λ j p (fX ^ 1) fX (fZ ^ 1) (fS ^ 1)
      (pow_one fX) (wj 1) wjr (wp 1) θ.hom]
    simp only [pow_one]
  have hstep : ∀ n : ℕ, F (n + 1) = F n ≫ F 1 := by
    intro n
    let := isIso_pow_return fX n
    let := isIso_pow_return fZ n
    let := isIso_pow_return fS n
    have wjo : (fX ≫ fX ^ n) ≫ j = j ≫ (fZ ≫ fZ ^ n) := by
      simpa only [pow_succ, End.mul_def] using wj (n + 1)
    have wpo : (fZ ≫ fZ ^ n) ≫ p = p ≫ (fS ≫ fS ^ n) := by
      simpa only [pow_succ, End.mul_def] using wp (n + 1)
    rw [hone]
    have h := compactReturn_comp Λ hΛ j p (fX ^ n) fX (fZ ^ n) fZ
      (fS ^ n) fS (wj n) wj1 (wp n) wp1 wjo wpo K.carrier.obj
      (iterateStructure Λ fX θ n).hom θ.hom
    dsimp only [F]
    simp only [iterateStructure, Iso.trans_hom, eqToIso.hom, Iso.app_hom,
      Functor.mapIso_hom]
    have wjr : (fX ^ n * fX) ≫ j = j ≫ fZ ^ (n + 1) := by
      simpa only [pow_succ, End.mul_def] using wj (n + 1)
    have ht := compactReturn_transport Λ j p (fX ^ (n + 1)) (fX ^ n * fX)
      (fZ ^ (n + 1)) (fS ^ (n + 1)) (pow_succ fX n) (wj (n + 1)) wjr
      (wp (n + 1)) ((pComp Λ fX (fX ^ n)).hom.app K.carrier.obj ≫
        (P Λ fX).map (iterateStructure Λ fX θ n).hom ≫ θ.hom)
    refine ht.trans ?_
    simpa only [pow_succ, End.mul_def] using h
  change ∀ m : ℕ, 1 ≤ m → F m = F 1 ^ m
  apply power_return_induction F
  intro n
  simpa only [End.mul_def] using hstep n

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
