/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.ZetaWeil.FiniteProjectiveModuleDualPairing
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Data.Int.Interval
import WeilConjectures.Algebra.Homology.Monoidal.Dual

/-!
# Explicit dual pairing for a bounded finite-projective complex

Source: Stacks Project, More on Algebra, Tag 0FNK, converse of
`lemma-left-dual-complex`, and Tag 0FNJ
(blueprint: lem-zl-bounded-projective-complex-dual-pairing).

The degree identifications are indexed by `n` as `D.X (-n) ≅ Hom(P.X n, A)`.
This avoids dependent casts in the formulas for evaluation and coevaluation.
The monoidal tensor is the signed direct-sum total tensor `mapBifunctor`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex

@[instance_reducible]
private noncomputable def finiteProjectiveRightDual (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) [Module.Finite A M] [Module.Projective A M] :
    HasRightDual M where
  rightDual := ModuleCat.of A (Module.Dual A M)
  exact :=
    { coevaluation' := ModuleCat.ofHom (LinearMap.finiteProjectiveCoevaluation A M)
      evaluation' := ModuleCat.ofHom (LinearMap.finiteProjectiveEvaluation A M)
      coevaluation_evaluation' := by
        let ε := ModuleCat.ofHom (LinearMap.finiteProjectiveEvaluation A M)
        let η := ModuleCat.ofHom (LinearMap.finiteProjectiveCoevaluation A M)
        have zag : (ρ_ (ModuleCat.of A (Module.Dual A M))).inv ≫
            ModuleCat.of A (Module.Dual A M) ◁ η ≫
              (α_ (ModuleCat.of A (Module.Dual A M)) M
                (ModuleCat.of A (Module.Dual A M))).inv ≫
                ε ▷ ModuleCat.of A (Module.Dual A M) ≫ (λ_ _).hom = 𝟙 _ :=
          ModuleCat.hom_ext (LinearMap.finiteProjectiveModuleDualPairing A M).2.2.2.2
        rw [← cancel_epi (ρ_ (ModuleCat.of A (Module.Dual A M))).inv,
          ← cancel_mono (λ_ (ModuleCat.of A (Module.Dual A M))).hom]
        simpa using zag
      evaluation_coevaluation' := by
        let ε := ModuleCat.ofHom (LinearMap.finiteProjectiveEvaluation A M)
        let η := ModuleCat.ofHom (LinearMap.finiteProjectiveCoevaluation A M)
        have zig : (λ_ M).inv ≫ η ▷ M ≫
            (α_ M (ModuleCat.of A (Module.Dual A M)) M).hom ≫ M ◁ ε ≫ (ρ_ M).hom =
              𝟙 M :=
          ModuleCat.hom_ext (LinearMap.finiteProjectiveModuleDualPairing A M).2.2.2.1
        rw [← cancel_epi (λ_ M).inv, ← cancel_mono (ρ_ M).hom]
        simpa using zig }

private lemma finiteProjectiveRightDual_mate (A : Type u) [CommRing A]
    (M N : ModuleCat.{u} A) [Module.Finite A M] [Module.Projective A M]
    [Module.Finite A N] [Module.Projective A N] (f : M ⟶ N) :
    let _ := finiteProjectiveRightDual A M
    let _ := finiteProjectiveRightDual A N
    fᘁ = ModuleCat.ofHom f.hom.dualMap := by
  let _ := finiteProjectiveRightDual A M
  let _ := finiteProjectiveRightDual A N
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  have h := rightAdjointMate_comp_evaluation f
  have hx := congrArg (fun (g : ModuleCat.of A (Module.Dual A N) ⊗ M ⟶
      ModuleCat.of A A) ↦ g.hom (φ ⊗ₜ[A] x)) h
  change contractLeft A M (((fᘁ).hom φ) ⊗ₜ[A] x) =
    contractLeft A N (φ ⊗ₜ[A] f.hom x) at hx
  exact hx

section Coordinates

variable (A : Type u) [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
  [∀ n : ℤ, Module.Finite A (P.X n)] [∀ n : ℤ, Module.Projective A (P.X n)]

private noncomputable abbrev termRightDual (n : ℤ) : HasRightDual (P.X n) :=
  finiteProjectiveRightDual A (P.X n)

attribute [local instance] termRightDual

private noncomputable def moduleDualDegreeIso (q p : ℤ) (h : p = -q) :
    P.rightDual.X q ≅ ModuleCat.of A (Module.Dual A (P.X p)) := by
  subst p
  exact Iso.refl _

private lemma moduleDual_d (q r p s : ℤ) (hp : p = -q) (hs : s = -r) :
    P.rightDual.d q r =
      (moduleDualDegreeIso A P q p hp).hom ≫
        ModuleCat.ofHom (r.negOnePow • (P.d s p).hom.dualMap) ≫
          (moduleDualDegreeIso A P r s hs).inv := by
  subst p
  subst s
  change r.negOnePow • (P.d (-r) (-q))ᘁ = 𝟙 _ ≫ _ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, finiteProjectiveRightDual_mate]
  rfl

private lemma moduleDual_evalPQ (q p : ℤ) (h : q + p = 0) (hp : p = -q) :
    rightDual.evalPQ P q p h =
      (moduleDualDegreeIso A P q p hp).hom ▷ P.X p ≫
        ModuleCat.ofHom (LinearMap.finiteProjectiveEvaluation A (P.X p)) := by
  subst p
  change (P.X (-q))ᘁ ◁ (𝟙 _) ≫ ε_ _ _ = (𝟙 _) ▷ _ ≫ _
  simp only [whiskerLeft_id, id_whiskerRight, Category.id_comp]
  rfl

private lemma moduleDual_coevPQ (p q : ℤ) (h : p + q = 0) (hp : p = -q) :
    rightDual.coevPQ P p q h =
      ModuleCat.ofHom (LinearMap.finiteProjectiveCoevaluation A (P.X p)) ≫
        P.X p ◁ (moduleDualDegreeIso A P q p hp).inv := by
  subst p
  change η_ (P.X (-q)) (P.X (-q))ᘁ ≫ (𝟙 _) ▷ _ = _ ≫ _ ◁ (𝟙 _)
  simp only [id_whiskerRight, whiskerLeft_id, Category.comp_id]
  rfl

end Coordinates

/-- A bounded finite-projective complex has its explicitly specified signed dual and
its evaluation and coevaluation satisfy both triangle identities.

Source: Stacks Project, More on Algebra, Tag 0FNK, converse of
`lemma-left-dual-complex`, with Tag 0FNJ for the dual terms
(blueprint: lem-zl-bounded-projective-complex-dual-pairing).

Proof:
1. Set `D^n = Hom_A(P^(-n), A)`. Its support is `[-b,-a]`. The module dual pairing
   lemma `lem-zl-finite-projective-module-dual-pairing` makes every dual term finite
   projective, including terms outside the support.
2. Define the differential by `(-1)^(n+1)` times precomposition. Two successive
   differentials give minus precomposition with two successive differentials of P,
   which is zero by `def-weil-abstract-derived-category`.
3. Evaluation on the total-degree-zero summands and zero elsewhere commutes with
   the differential: its two terms have coefficients `(-1)^(1-n)` and `(-1)^n`.
   The finite sum of the module coevaluation tensors defines coevaluation.
   In the component `P^(n+1) tensor D^(-n)`, its differential is the sum of
   `(d_P tensor 1)c_n` and `(-1)^(n+1)(1 tensor d_D)c_(n+1)`.
   The module triangle identities give
   `(1 tensor d_D)c_(n+1) = (-1)^n(d_P tensor 1)c_n`, so this sum is zero.
   These calculations use the signed total tensor of `def-pc-tensor-complex-sheaves`.
4. On P^n and D^(-n), the two chain triangle identities reduce to the corresponding
   module identities of `lem-zl-finite-projective-module-dual-pairing`.
   Mixed-degree contributions vanish under evaluation. The canonical associator
   has no sign and the maps have degree zero, so no further signs occur.
5. For the zero complex the sums and maps vanish. For a one-term complex this is
   precisely the ordinary module pairing; no endpoint or characteristic exception arises.
-/
theorem boundedProjectiveComplexDualPairing (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (hab : a ≤ b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    [∀ n : ℤ, Module.Finite A (P.X n)] [∀ n : ℤ, Module.Projective A (P.X n)] :
    ∃ (D : CochainComplex (ModuleCat.{u} A) ℤ)
      (e : ∀ n : ℤ, D.X (-n) ≅ ModuleCat.of A (Module.Dual A (P.X n))),
      (∀ n m : ℤ, D.d (-n) (-m) =
        (e n).hom ≫ ModuleCat.ofHom ((-m).negOnePow • (P.d m n).hom.dualMap) ≫
          (e m).inv) ∧
      (∀ n : ℤ, n < -b ∨ -a < n → IsZero (D.X n)) ∧
      (∀ n : ℤ, Module.Finite A (D.X n) ∧ Module.Projective A (D.X n)) ∧
      ∃ (ε : D ⊗ P ⟶ 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ))
        (η : 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) ⟶ P ⊗ D),
        (∀ n : ℤ,
          HomologicalComplex.ιTensorObj D P (-n) n 0 (neg_add_cancel n) ≫ ε.f 0 ≫
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom =
            (e n).hom ▷ P.X n ≫
              ModuleCat.ofHom (LinearMap.finiteProjectiveEvaluation A (P.X n))) ∧
        (η.f 0 =
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom ≫
            ∑ n ∈ Finset.Icc a b,
              ModuleCat.ofHom (LinearMap.finiteProjectiveCoevaluation A (P.X n)) ≫
                P.X n ◁ (e n).inv ≫
                  HomologicalComplex.ιTensorObj P D n (-n) 0 (add_neg_cancel n)) ∧
        (∀ n : ℤ, n ≠ 0 → ε.f n = 0 ∧ η.f n = 0) ∧
        ((λ_ P).inv ≫ η ▷ P ≫ (α_ P D P).hom ≫ P ◁ ε ≫ (ρ_ P).hom = 𝟙 P) ∧
        ((ρ_ D).inv ≫ D ◁ η ≫ (α_ D P D).inv ≫ ε ▷ D ≫ (λ_ D).hom = 𝟙 D) := by
  let _ : ∀ n : ℤ, HasRightDual (P.X n) := fun n ↦ finiteProjectiveRightDual A (P.X n)
  let _ : P.IsStrictlyGE a := (P.isStrictlyGE_iff a).2 (fun n hn ↦ hP n (Or.inl hn))
  let _ : P.IsStrictlyLE b := by
    rw [← max_eq_right hab, P.isStrictlyLE_iff]
    exact fun n hn ↦ hP n (Or.inr (lt_of_le_of_lt (le_max_right a b) hn))
  let D := P.rightDual
  let e : ∀ n : ℤ, D.X (-n) ≅ ModuleCat.of A (Module.Dual A (P.X n)) :=
    fun n ↦ moduleDualDegreeIso A P (-n) n (by omega)
  refine ⟨D, e, ?_, ?_, ?_, rightDual.eval P, rightDual.coev P a b, ?_, ?_, ?_, ?_, ?_⟩
  · intro n m
    exact moduleDual_d A P (-n) (-m) n m (by omega) (by omega)
  · intro n hn
    apply rightDual.isZero_X
    apply hP
    omega
  · intro n
    exact ⟨inferInstanceAs (Module.Finite A (Module.Dual A (P.X (-n)))),
      inferInstanceAs (Module.Projective A (Module.Dual A (P.X (-n))))⟩
  · intro n
    rw [← Category.assoc, rightDual.ι_eval_f, Category.assoc]
    erw [Iso.inv_hom_id, Category.comp_id]
    exact moduleDual_evalPQ A P (-n) n (neg_add_cancel n) (by omega)
  · rw [rightDual.coev, HomologicalComplex.mkHomFromSingle_f]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [moduleDual_coevPQ A P n (-n) (add_neg_cancel n) (by omega)]
    simp only [Category.assoc]
    rfl
  · intro n hn
    exact ⟨rightDual.eval_f_eq_zero P n hn,
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of A A) n hn).eq_of_src
        _ _⟩
  · let _ := exactPairingRightDual P a b
    change (λ_ P).inv ≫ η_ P D ▷ P ≫ (α_ P D P).hom ≫ P ◁ ε_ P D ≫ (ρ_ P).hom = _
    simp
  · let _ := exactPairingRightDual P a b
    change (ρ_ D).inv ≫ D ◁ η_ P D ≫ (α_ D P D).inv ≫ ε_ P D ▷ D ≫ (λ_ D).hom = _
    simp

end CochainComplex
