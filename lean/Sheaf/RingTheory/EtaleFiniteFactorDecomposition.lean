/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Sheaf.AlgebraicGeometry.FiniteIsolatedPointsOfFiniteType
import Sheaf.RingTheory.EtaleIsolatedPointRemoval
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Algebra.Ring.PUnit
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Finiteness.Prod

/-!
# A finite factor after an étale base change

Source: Stacks Project, Algebra, Lemma 10.145.3 (Tag 00UK), with the finite factors combined
(blueprint: lem-weil-pbc-finite-type-etale-finite-factor-decomposition).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

private theorem finiteFactor_of_fibre_ncard
    {R : Type u} {S : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] (n : ℕ)
    (hn : {q : PrimeSpectrum (p.Fiber S) |
      IsOpen ({q} : Set (PrimeSpectrum (p.Fiber S)))}.ncard ≤ n) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p)
      (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R' A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R' B)
      (_ : Algebra.FiniteType R' B),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId R R') (P.over_def p)) ∧
      Nonempty ((R' ⊗[R] S) ≃ₐ[R'] (A × B)) ∧ Module.Finite R' A ∧
      ∀ q : PrimeSpectrum B, q.asIdeal.LiesOver P → ¬ IsQuasiFiniteAtPrime R' B q := by
  classical
  induction n using Nat.strong_induction_on generalizing R S with
  | h n ih =>
    let F := {q : PrimeSpectrum (p.Fiber S) |
      IsOpen ({q} : Set (PrimeSpectrum (p.Fiber S)))}
    by_cases hzero : F.ncard = 0
    · have hfin : F.Finite :=
        AlgebraicGeometry.Spec.finite_setOf_isOpen_singleton_of_finiteType
          p.ResidueField (p.Fiber S)
      have hempty : F = ∅ := (Set.ncard_eq_zero hfin).mp hzero
      let : p.LiesOver p := ⟨by simp [Ideal.under]⟩
      refine ⟨R, inferInstance, inferInstance, inferInstance, p, inferInstance, inferInstance,
        PUnit.{max u v + 1}, inferInstance, inferInstance, S, inferInstance, inferInstance,
        inferInstance, ?_, ?_, inferInstance, ?_⟩
      · have hid : Ideal.ResidueField.mapₐ p p (Algebra.ofId R R) (p.over_def p) =
            AlgHom.id R p.ResidueField := by
          apply Ideal.ResidueField.algHom_ext
          ext
        rw [hid]
        exact Function.bijective_id
      · exact ⟨(Algebra.TensorProduct.lid R S).trans AlgEquiv.uniqueProd.symm⟩
      · intro q hq hquasi
        let := hq
        have hp : p = q.asIdeal.comap (algebraMap R S) := q.asIdeal.over_def p
        subst p
        have hmem : ∃ x, x ∈ F := ⟨_, hquasi⟩
        rw [hempty] at hmem
        simp at hmem
    · have hpos : 0 < F.ncard := Nat.pos_of_ne_zero hzero
      obtain ⟨R₁, hR₁, hRR₁, hE₁, P₁, hP₁, hP₁p, A₁, hA₁, hR₁A₁,
        D, hD, hR₁D, hftD, hres₁, ⟨e₁⟩, hfinite₁, hdrop⟩ :=
        exists_etale_finiteFactor_smaller_fibre p hpos
      let := hR₁
      let := hRR₁
      let := hE₁
      let := hP₁
      let := hP₁p
      let := hA₁
      let := hR₁A₁
      let := hD
      let := hR₁D
      let := hftD
      let := hfinite₁
      obtain ⟨R₂, hR₂, hR₁R₂, hE₂, P₂, hP₂, hP₂P₁, A₂, hA₂, hR₂A₂,
        B₂, hB₂, hR₂B₂, hftB₂, hres₂, ⟨e₂⟩, hfinite₂, hnone₂⟩ :=
        ih _ (lt_of_lt_of_le hdrop hn) (S := D) P₁ le_rfl
      let := hR₂
      let := hR₁R₂
      let := hE₂
      let := hP₂
      let := hP₂P₁
      let := hA₂
      let := hR₂A₂
      let := hB₂
      let := hR₂B₂
      let := hftB₂
      let := hfinite₂
      let : Algebra R R₂ := (algebraMap R₁ R₂).comp (algebraMap R R₁) |>.toAlgebra
      let : IsScalarTower R R₁ R₂ := IsScalarTower.of_algebraMap_eq' rfl
      let : Algebra.Etale R R₂ := Algebra.Etale.comp R R₁ R₂
      let : P₂.LiesOver p := Ideal.LiesOver.trans P₂ P₁ p
      let A := (R₂ ⊗[R₁] A₁) × A₂
      refine ⟨R₂, inferInstance, inferInstance, inferInstance, P₂, inferInstance, inferInstance,
        A, inferInstance, inferInstance, B₂, inferInstance, inferInstance, inferInstance,
        ?_, ?_, inferInstance, hnone₂⟩
      · have hcomp : Ideal.ResidueField.map p P₂ (Algebra.ofId R R₂).toRingHom (P₂.over_def p) =
            (Ideal.ResidueField.map P₁ P₂ (Algebra.ofId R₁ R₂).toRingHom (P₂.over_def P₁)).comp
              (Ideal.ResidueField.map p P₁ (Algebra.ofId R R₁).toRingHom (P₁.over_def p)) := by
          apply Ideal.ResidueField.ringHom_ext
          ext r
          simp [IsScalarTower.algebraMap_apply R R₁ R₂]
        change Function.Bijective
          (Ideal.ResidueField.map p P₂ (Algebra.ofId R R₂).toRingHom (P₂.over_def p))
        rw [hcomp]
        exact hres₂.comp hres₁
      · let e₃ := (Algebra.TensorProduct.cancelBaseChange R R₁ R₂ R₂ S).symm
        let e₄ := Algebra.TensorProduct.congr (AlgEquiv.refl : R₂ ≃ₐ[R₂] R₂) e₁
        let e₅ := Algebra.TensorProduct.prodRight R₁ R₂ R₂ A₁ D
        let e₆ := AlgEquiv.prodCongr
          (AlgEquiv.refl : (R₂ ⊗[R₁] A₁) ≃ₐ[R₂] (R₂ ⊗[R₁] A₁)) e₂
        let e₇ : ((R₂ ⊗[R₁] A₁) × (A₂ × B₂)) ≃ₐ[R₂] (A × B₂) :=
          { __ := (Equiv.prodAssoc _ _ _).symm
            map_mul' := fun _ _ ↦ rfl
            map_add' := fun _ _ ↦ rfl
            commutes' := fun _ ↦ rfl }
        exact ⟨e₃.trans (e₄.trans (e₅.trans (e₆.trans e₇)))⟩

/-- (blueprint: lem-weil-pbc-finite-type-etale-finite-factor-decomposition)
Stacks Project, Algebra, Tag 00UK: a finite-type algebra admits, after an étale neighbourhood
of a prime with unchanged residue field, a decomposition into a finite algebra and an algebra
which is not quasi-finite at any prime above the chosen prime. The finite-type witness for
`B` records a consequence of the product decomposition, needed by `IsQuasiFiniteAtPrime`.

Proof from the node, step by step:
1. The fibre `κ(p) ⊗[R] S` has finitely many isolated points by
   `lem-weil-pbc-finite-type-field-finite-isolated-points`. The correspondence
   `lem-weil-pbc-fibre-ring-primes-bijection` identifies them with primes above `p` where
   the map is quasi-finite. Induct on an upper bound for their number.
2. If the bound is zero, take `R' = R`, `P = p`, the zero ring as `A`, and `B = S`.
   The identity is étale and induces the identity on residue fields.
3. Otherwise choose one isolated fibre prime and apply
   `lem-weil-pbc-etale-quasi-finite-finite-one-prime` (Tag 00UJ). Its idempotent `e` splits
   `C = R₁ ⊗[R] S` into the finite factor `C_e` and the finite-type factor `D = C_(1-e)`.
4. The unchanged residue field identifies the new fibre with the old one. The fibre of `D`
   is the complementary clopen factor and omits the selected isolated point. Thus the bound
   for its isolated points drops by one (use `lem-weil-pbc-fibre-ring-primes-bijection`).
5. Apply induction to `D`. Use `lem-weil-pbc-algebra-tensor-product-distributes-product`
   to assemble the finite factor from the base change of `C_e` and the finite factor supplied
   by induction. Finiteness survives base change and finite products. The composite is étale
   by `lem-weil-pbc-etale-composition-cancellation`; the residue-field isomorphisms compose.
6. The complementary factor is the one from induction, so it has no quasi-finite prime
   above the selected prime. This proves the final clause. -/
theorem exists_etale_finiteFactor_decomposition
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p)
      (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R' A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R' B)
      (_ : Algebra.FiniteType R' B),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId R R') (P.over_def p)) ∧
      Nonempty ((R' ⊗[R] S) ≃ₐ[R'] (A × B)) ∧ Module.Finite R' A ∧
      ∀ q : PrimeSpectrum B, q.asIdeal.LiesOver P → ¬ IsQuasiFiniteAtPrime R' B q := by
  let T := ULift.{u} S
  let : Algebra.FiniteType R T :=
    Algebra.FiniteType.equiv inferInstance (ULift.algEquiv (R := R)).symm
  obtain ⟨R', hR', hRR', hE, P, hP, hPp, A, hA, hR'A, B, hB, hR'B,
    hftB, hres, ⟨e⟩, hfinite, hnone⟩ :=
    finiteFactor_of_fibre_ncard (S := T) p _ le_rfl
  let := hR'
  let := hRR'
  let := hE
  let := hP
  let := hPp
  let := hA
  let := hR'A
  let := hB
  let := hR'B
  let := hftB
  exact ⟨R', hR', hRR', hE, P, hP, hPp, A, hA, hR'A, B, hB, hR'B, hftB,
    hres, ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl)
      (ULift.algEquiv (R := R)).symm).trans e⟩, hfinite, hnone⟩

end Algebra
