module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Prime localization and residue fibres of scalar-extended modules

Source: Stacks Project, Algebra, Tags 00SI and 00SJ, the displayed comparisons in
`lemma-lci-field-change-local` and `lemma-lci-field-change`.
(blueprint: lem-weil-pbc-prime-localized-module-base-change).

Tensor factors are commuted to Mathlib's convention: scalar extension of `M` to `B`
is `B ⊗[A] M`. Thus `b ⊗ m` represents the node's `m ⊗ b`, with the action on `B`.
The transparent proposition installs the specified maps and their canonical scalar actions.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace LocalizedModule

/-- The complete prime-localization and residue-fibre comparison assertion.
Source: Stacks Project, Algebra, Tags 00SI and 00SJ, displayed fibre comparisons.
(blueprint: lem-weil-pbc-prime-localized-module-base-change).

The `let` bindings occur in a transparent definition, not in the theorem signature.
They construct the contracted prime, the induced local homomorphism, and its induced
residue-field algebra. The two cancellation equivalences in the last equation are
Mathlib's tensor associativity and tensor-unit maps, with the scalar factors on the left.
-/
noncomputable def primeLocalizedModuleBaseChange
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (M : Type w) [AddCommGroup M] [Module A M]
    (q : Ideal B) [q.IsPrime] : Prop :=
  letI : Algebra A B := f.toAlgebra
  let p := q.comap f
  let Ap := Localization.AtPrime p
  let Bq := Localization.AtPrime q
  let Mp := LocalizedModule p.primeCompl M
  let Nq := LocalizedModule q.primeCompl (B ⊗[A] M)
  letI : Algebra Ap Bq := (Localization.localRingHom p q f rfl).toAlgebra
  letI : IsLocalHom (algebraMap Ap Bq) :=
    Localization.isLocalHom_localRingHom p q f rfl
  Ideal.comap (Localization.localRingHom p q f rfl) (IsLocalRing.maximalIdeal Bq) =
      IsLocalRing.maximalIdeal Ap ∧
    algebraMap p.ResidueField q.ResidueField = Ideal.ResidueField.map p q f rfl ∧
    ∃ (Φ : Nq ≃ₗ[Bq] Bq ⊗[Ap] Mp)
      (Ψ : (q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[Ap] Mp)) ≃ₗ[q.ResidueField]
        q.ResidueField ⊗[Bq] Nq),
      (∀ (m : M) (b : B) (t : q.primeCompl),
        Φ (LocalizedModule.mk (b ⊗ₜ[A] m) t) =
          Localization.mk b t ⊗ₜ[Ap] LocalizedModule.mk m 1) ∧
      (∀ (m : M) (s : p.primeCompl) (a : p.ResidueField) (b : q.ResidueField),
        Ψ (b ⊗ₜ[p.ResidueField] (a ⊗ₜ[Ap] LocalizedModule.mk m s)) =
          (Ideal.ResidueField.map p q f rfl a * b / algebraMap B q.ResidueField (f s)) ⊗ₜ[Bq]
            LocalizedModule.mk ((1 : B) ⊗ₜ[A] m) 1) ∧
      Ψ =
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          Ap p.ResidueField q.ResidueField q.ResidueField Mp) ≪≫ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          Ap Bq q.ResidueField q.ResidueField Mp).symm ≪≫ₗ
        Φ.symm.baseChange Bq q.ResidueField (Bq ⊗[Ap] Mp) Nq

/-- Prime localization commutes with arbitrary module scalar extension, and the induced
residue-fibre comparison has the stated fraction formula and agrees with tensoring the
inverse localization comparison.
Source: Stacks Project, Algebra, Tags 00SI and 00SJ, displayed fibre comparisons.
(blueprint: lem-weil-pbc-prime-localized-module-base-change).

Proof:
1. Set `p = f⁻¹(q)`. The localization universal property
   (lem-weil-pbc-ring-localization-universal-property) constructs `f_q(a/s) = f(a)/f(s)`.
   A fraction lies in the maximal ideal exactly when its numerator is in the prime;
   hence `f_q` is local. Quotienting induces the displayed residue-field map. The
   residue of `a/s` corresponds to `ā/s̄` in the fraction field of `A/p`.
2. Localization-tensor compatibility (lem-weil-pbc-localization-tensor-over-base),
   tensor units and symmetry identify each localized module `P_r` with `C_r ⊗[C] P`,
   sending `x/s` to `(1/s) ⊗ x`. This identification is `C_r`-linear.
3. Apply base-change transitivity (lem-weil-pbc-module-base-change-transitive) to
   `A → B → Bq` and `A → Ap → Bq`. The two maps `A → Bq` agree since
   `f_q(a/1) = f(a)/1`. Their common tensor product gives `Φ` and its pure-tensor
   formula, by the two localization identifications of step 2.
4. The two maps `Ap → κ(q)` through `κ(p)` and through `Bq` agree on fractions.
   Base-change transitivity for these towers gives `α` and `β`. Define
   `Ψ = (Φ⁻¹ ⊗ 1) β⁻¹ α`; this is precisely the last equality in the assertion.
5. In `κ(q) ⊗[Ap] Mp`, balancing moves the denominator of `m/s` to the scalar,
   dividing by the nonzero residue of `f(s)`. Apply `β⁻¹`, then the formula for
   `Φ⁻¹` on `(m/1) ⊗ 1`, to obtain the displayed formula for `Ψ`.
No step requires flatness, finite generation, or injectivity of `f`.
-/
theorem prime_localized_module_base_change
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (M : Type w) [AddCommGroup M] [Module A M]
    (q : Ideal B) [q.IsPrime] : primeLocalizedModuleBaseChange f M q := by
  sorry

end LocalizedModule
