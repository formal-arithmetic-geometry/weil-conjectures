/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.PopescuDelocalizeWeakLocalizationSmooth
import WeilConjectures.RingTheory.PopescuFinalSolve
import WeilConjectures.RingTheory.PopescuWeakClearPresentation
import WeilConjectures.RingTheory.SingularIdealMapEquiv
import WeilConjectures.RingTheory.PopescuWeakHomogenize
import WeilConjectures.RingTheory.SmoothStandardSmoothRetract
import WeilConjectures.RingTheory.StandardSmoothIncludeGenerators

/-!
# Weak delocalization of a Popescu resolution

A Popescu resolution of the localized problem at a prime `q` gives a finitely presented
factorization over the original base whose extended singular ideal is not contained in `q`.

## Implementation details

The localized resolution factors through a standard smooth algebra (Tags 07EU, 07CH) whose
presentation includes the generators of `A` (Tag 07EY). Clearing denominators of the equations,
the inverse determinant and the relations of `A`, and homogenizing the equations in the extra
variables, gives an algebra `B` with a smooth principal localization at an element mapping
outside `q`. The minimal-prime hypothesis is retained although it is not used.

The localized algebra is the base change `R_p ⊗[R] A`, and the induced map `A_p → Λ_q` is
`Algebra.TensorProduct.lift` of the structure map `R_p → Λ_q` and `α` followed by `Λ → Λ_q`. The
local algebra structure on `Λ_q` is the canonical one, and `q Λ_q` is its maximal ideal.

## References

* [Stacks, Tag 07F9]
* [Stacks, Tag 07EU]
* [Stacks, Tag 07CH]
* [Stacks, Tag 07EY]
-/

@[expose] public section

universe u v t

namespace Algebra

/-- A resolution after localization at a minimal prime over the extended singular ideal
can be delocalized to a finitely presented factorization whose extended singular ideal
is not contained in that prime. -/
theorem exists_factorization_singularIdeal_not_le_of_local_popescu_resolution
    {R : Type u} {A : Type v} {Λ : Type t}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
    (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)
    (hlocal :
      letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
      CanBePopescuResolved
        (Algebra.TensorProduct.lift
          (Algebra.ofId (Localization.AtPrime (q.asIdeal.under R))
            (Localization.AtPrime q.asIdeal))
          ((IsScalarTower.toAlgHom R Λ (Localization.AtPrime q.asIdeal)).comp α)
          (fun _ _ => Commute.all _ _))
        ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal), inferInstance⟩) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra R C),
      ∃ (β : A →ₐ[R] C) (γ : C →ₐ[R] Λ),
        FinitePresentation R C ∧ γ.comp β = α ∧
          ¬ Ideal.map γ.toRingHom (singularIdeal R C) ≤ q.asIdeal :=
  open MvPolynomial in
  open scoped BigOperators in by
  classical
  have _hminimal := hminimal
  let Rp := Localization.AtPrime (q.asIdeal.under R)
  let Lq := Localization.AtPrime q.asIdeal
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  let Ap := _root_.TensorProduct R Rp A
  let φ : Ap →ₐ[Rp] Lq := Algebra.TensorProduct.lift
    (Algebra.ofId Rp Lq) ((IsScalarTower.toAlgHom R Λ Lq).comp α)
    (fun _ _ ↦ Commute.all _ _)
  change CanBePopescuResolved φ ⟨IsLocalRing.maximalIdeal Lq, inferInstance⟩ at hlocal
  obtain ⟨C₁, _, _, β₁, γ₁, hfp, hcomp, _, hnot⟩ := hlocal
  have : FinitePresentation Rp C₁ := hfp
  have htop : Ideal.map γ₁.toRingHom (singularIdeal Rp C₁) = ⊤ := by
    apply Ideal.radical_eq_top.mp
    by_contra hne
    exact hnot (IsLocalRing.le_maximalIdeal hne)
  obtain ⟨C₂, _, _, hsmooth, δ, γ₂, hδ⟩ :=
    exists_smooth_factorization_of_singularIdeal_map_eq_top γ₁ htop
  have : Smooth Rp C₂ := hsmooth
  obtain ⟨D, _, _, hstd, ι, ρ, hρι, _⟩ := Smooth.exists_standardSmooth_retract Rp C₂
  have : IsStandardSmooth Rp D := hstd
  let : Algebra R D := Algebra.restrictScalars R Rp D
  have : IsScalarTower R Rp D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let βD : Ap →ₐ[Rp] D := ι.comp (δ.comp β₁)
  let γD : D →ₐ[Rp] Lq := γ₂.comp ρ
  have hD : γD.comp βD = φ := by
    dsimp [γD, βD]
    calc
      (γ₂.comp ρ).comp (ι.comp (δ.comp β₁)) =
          (γ₂.comp (ρ.comp ι)).comp (δ.comp β₁) := rfl
      _ = (γ₂.comp δ).comp β₁ := by rw [hρι]; rfl
      _ = φ := by rw [hδ, hcomp]
  obtain ⟨n, t, ⟨Q⟩⟩ := Presentation.exists_presentation_fin R A
  let η : A →ₐ[R] D := (βD.restrictScalars R).comp Algebra.TensorProduct.includeRight
  obtain ⟨m, c, hc, P, _, hmap, hval⟩ :=
    exists_standardSmoothPresentation_include_generators (R := Rp) n (fun i ↦ η (Q.val i))
  have hgD : ∀ j, aeval (fun i : Fin n ↦ P.val (Fin.castAdd m i)) (Q.relation j) = 0 := by
    intro j
    simp only [hval]
    rw [← MvPolynomial.comp_aeval_apply, Q.aeval_val_relation, map_zero]
  obtain ⟨f, s, h, hsnot, hs, hg, hfD⟩ :=
    exists_cleared_submersive_presentation (q.asIdeal.under R) n m c t hc P hmap
      Q.relation hgD
  let y : Fin (n + m) → Lq := fun i ↦ γD (P.val i)
  have hy : ∀ i : Fin n, y (Fin.castAdd m i) = algebraMap Λ Lq (α (Q.val i)) := by
    intro i
    dsimp [y]
    rw [hval]
    have he := DFunLike.congr_fun hD (_root_.TensorProduct.tmul R (1 : Rp) (Q.val i))
    change γD (βD (_root_.TensorProduct.tmul R (1 : Rp) (Q.val i))) = algebraMap Λ Lq (α (Q.val i))
    change γD (βD (_root_.TensorProduct.tmul R (1 : Rp) (Q.val i))) =
      φ (_root_.TensorProduct.tmul R (1 : Rp) (Q.val i)) at he
    rw [he]
    change (Algebra.ofId Rp Lq) 1 *
      ((IsScalarTower.toAlgHom R Λ Lq).comp α) (Q.val i) = _
    simp only [map_one, one_mul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
  have hf : ∀ j, aeval y (f j) = 0 := by
    intro j
    change aeval (fun i ↦ (γD.restrictScalars R) (P.val i)) (f j) = 0
    rw [← MvPolynomial.comp_aeval_apply, hfD, map_zero]
  obtain ⟨d, F, l, hdegree, hF, hl, hlzero, hllast, hlF⟩ :=
    exists_homogenized_local_equations q n m c f (fun i ↦ α (Q.val i)) y hy hf
  let k : Fin n → Fin (n + m + 2) := fun i ↦
    (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ
  let I : Ideal (MvPolynomial (Fin (n + m + 2)) R) := Ideal.span
    (Set.range (fun j : Fin t ↦ rename k (Q.relation j)) ∪
      Set.range (fun j : Fin c ↦ X (0 : Fin (n + m + 2)) * F j))
  let B := MvPolynomial (Fin (n + m + 2)) R ⧸ I
  let π : MvPolynomial (Fin (n + m + 2)) R →ₐ[R] B := Ideal.Quotient.mkₐ R I
  let ev : MvPolynomial (Fin (n + m + 2)) R →ₐ[R] Λ := aeval l
  have hev : ∀ p ∈ I, ev p = 0 := by
    change I ≤ RingHom.ker ev.toRingHom
    apply Ideal.span_le.mpr
    rintro p (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · change aeval l (rename k (Q.relation j)) = 0
      rw [aeval_rename]
      have he : aeval (l ∘ k) = α.comp (aeval Q.val) := by
        ext i
        simpa only [aeval_X, AlgHom.comp_apply, Function.comp_apply] using hl i
      rw [he, AlgHom.comp_apply, Q.aeval_val_relation, map_zero]
    · exact hlF j
  let γ : B →ₐ[R] Λ := Ideal.Quotient.liftₐ I ev hev
  let e : MvPolynomial (Fin n) R →ₐ[R] B := aeval (fun i ↦ π (X (k i)))
  have he : ∀ p ∈ Q.ker, e p = 0 := by
    change Q.ker ≤ RingHom.ker e.toRingHom
    rw [← Q.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro p ⟨j, rfl⟩
    have heq : e = π.comp (rename k) := by
      ext i
      simp [e]
    change e (Q.relation j) = 0
    rw [heq, AlgHom.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨j, rfl⟩))
  let β : A →ₐ[R] B := (Ideal.Quotient.liftₐ Q.ker e he).comp
    (Q.quotientEquiv.symm.restrictScalars R).toAlgHom
  have hγπ (p) : γ (π p) = ev p := rfl
  have hβQ : β.comp (aeval Q.val) = e := by
    apply AlgHom.ext
    intro p
    change (Ideal.Quotient.liftₐ Q.ker e he)
      (Q.quotientEquiv.symm (aeval Q.val p)) = e p
    have hQ : aeval Q.val p = Q.quotientEquiv ((Ideal.Quotient.mkₐ R Q.ker) p) := by
      exact (Q.algebraMap_apply p).symm
    rw [hQ, AlgEquiv.symm_apply_apply]
    rfl
  have hβα : γ.comp β = α := by
    apply (AlgHom.cancel_right Q.aeval_val_surjective).mp
    rw [AlgHom.comp_assoc, hβQ]
    ext i
    change γ (e (X i)) = α (aeval Q.val (X i))
    simp only [e, aeval_X, hγπ, ev]
    exact hl i
  let b : B := π (X (0 : Fin (n + m + 2)) * X (Fin.last (n + m + 1)) *
    MvPolynomial.C (∏ j : Fin (t + 1), s j))
  have hbSmooth : Smooth R (Localization.Away b) :=
    popescu_delocalize_weak_localization_smooth R n m c t hc f Q.relation s h hs hg
      d hdegree F hF
  have hb : b ∈ singularIdeal R B :=
    Ideal.le_radical (Ideal.subset_span hbSmooth)
  have hbnot : γ b ∉ q.asIdeal := by
    have hsprod : algebraMap R Λ (∏ j : Fin (t + 1), s j) ∉ q.asIdeal := by
      rw [map_prod]
      intro hmem
      obtain ⟨j, _, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact hsnot j hj
    change γ (π _) ∉ q.asIdeal
    rw [hγπ]
    simpa only [ev, map_mul, aeval_X, aeval_C] using
      q.isPrime.mul_notMem (q.isPrime.mul_notMem hlzero hllast) hsprod
  have hfg : I.FG := by
    dsimp [I]
    rw [Ideal.span_union]
    exact (Submodule.fg_span (Set.finite_range _)).sup
      (Submodule.fg_span (Set.finite_range _))
  have : FinitePresentation R B := FinitePresentation.quotient hfg
  let C := ULift.{max u v} B
  let E : B ≃ₐ[R] C := ULift.algEquiv.symm
  have : FinitePresentation R C := FinitePresentation.equiv E
  refine ⟨C, inferInstance, inferInstance, E.toAlgHom.comp β,
    γ.comp E.symm.toAlgHom, inferInstance, ?_, ?_⟩
  · ext a
    change γ (E.symm (E (β a))) = α a
    rw [AlgEquiv.symm_apply_apply]
    exact DFunLike.congr_fun hβα a
  · intro hle
    have hbC : E b ∈ singularIdeal R C := singularIdeal_map_equiv_le E
      (Ideal.mem_map_of_mem E.toRingHom hb)
    have hmem := hle (Ideal.mem_map_of_mem (γ.comp E.symm.toAlgHom).toRingHom hbC)
    change γ (E.symm (E b)) ∈ q.asIdeal at hmem
    rw [AlgEquiv.symm_apply_apply] at hmem
    exact hbnot hmem

end Algebra
