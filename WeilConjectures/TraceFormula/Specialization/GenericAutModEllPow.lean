/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericAutModEll
public import WeilConjectures.TraceFormula.Specialization.GenericAutPow
public import WeilConjectures.SixFunctors.NearbyCycles.ActionTrivialModEllSeparated

/-!

# Generic automorphisms trivial modulo `ℓ` act trivially

For `K` algebraically closed, every generic automorphism is an `ℓ ^ m`-th power for `ℓ` a prime
different from the characteristic of `k'` (`NearbyCyclesModel.GenericAut.exists_pow_ell_pow_eq`,
from `NearbyCyclesModel.GenericAut.exists_pow_eq`). Hence a normal subgroup `V` of finite index
of `P'` acting trivially on the nearby cycles `Ψ_{M''} Z` of a reduction `A ⟶ Z` modulo `ℓ`
acts trivially on `Ψ_{M''} A`:

* for `A` killed by `ℓ ^ m` (`NearbyCyclesModel.autAction_baseChangeAut_eq_id_of_distinguished'`);
* for `A` whose nearby cycles have `ℓ`-adically separated endomorphisms, e.g. with
  `𝒪_E`-coefficients
  (`NearbyCyclesModel.autAction_baseChangeAut_eq_id_of_distinguished_of_separated`).

This is the step of the finiteness of the action of `P'` on `ℚ̄_ℓ`-nearby cycles (SGA 4½,
[Th. finitude], §3.7) which makes the subgroup `V` obtained modulo `ℓ` work integrally.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- Every generic automorphism is an `ℓ ^ m`-th power, for `ℓ` a prime different from the
characteristic of `k'` and `K` algebraically closed. -/
theorem GenericAut.exists_pow_ell_pow_eq [IsAlgClosed K] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓk : ringChar k' ≠ ℓ) (m : ℕ) (σ : GenericAut k' K) : ∃ τ, τ ^ ℓ ^ m = σ := by
  obtain ⟨p, hp, hpk, hpℓ⟩ : ∃ p : ℕ, p.Prime ∧ (∀ n : ℕ, (n : k') = 0 → p ∣ n) ∧ p ≠ ℓ := by
    rcases CharP.char_is_prime_or_zero k' (ringChar k') with h | h
    · exact ⟨ringChar k', h, fun n hn ↦ (ringChar.spec k' n).1 hn, hℓk⟩
    · obtain ⟨p, hp₁, hp₂⟩ := Nat.exists_infinite_primes (ℓ + 1)
      refine ⟨p, hp₂, fun n hn ↦ ?_, by omega⟩
      have := (ringChar.spec k' n).1 hn
      rw [h, zero_dvd_iff] at this
      exact this ▸ dvd_zero p
  refine GenericAut.exists_pow_eq hp hpk (fun h ↦ hpℓ ?_) σ
  exact (Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h)

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Generic automorphisms trivial modulo `ℓ` are trivial, torsion case**: for `K`
algebraically closed, `ℓ` a prime different from the characteristic of `k'`, `A` killed by
`ℓ ^ m` and `A --ℓ--> A ⟶ Z ⟶ A⟦1⟧` distinguished, every element of a normal subgroup `V` of
finite index acting trivially on `Ψ_{M''} Z` acts trivially on `Ψ_{M''} A`. -/
theorem autAction_baseChangeAut_eq_id_of_distinguished' [IsAlgClosed K] {ℓ m : ℕ}
    (hℓ : ℓ.Prime) (hℓk : ringChar k' ≠ ℓ)
    {A Z : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (π : A ⟶ Z) (δ : Z ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (ℓ • 𝟙 A) π δ ∈ distTriang _) (hℓA : (ℓ ^ m) • 𝟙 A = 0)
    (V : Subgroup (GenericAut k' K)) [V.Normal] [V.FiniteIndex]
    (hV : ∀ σ ∈ V, (baseChangeAut hM b hb v hv σ).autAction Λ Z = 𝟙 _) {σ : GenericAut k' K}
    (hσ : σ ∈ V) : (baseChangeAut hM b hb v hv σ).autAction Λ A = 𝟙 _ :=
  autAction_baseChangeAut_eq_id_of_distinguished hM b hb v hv Λ π δ hT hℓA
    (GenericAut.exists_pow_ell_pow_eq hℓ hℓk m) V hV hσ

/-- **Generic automorphisms trivial modulo `ℓ` are trivial, integral case**: for `K`
algebraically closed, `ℓ` a prime different from the characteristic of `k'`, `A` such that no
nonzero endomorphism of `Ψ_{M''} A` is divisible by every power of `ℓ` (e.g. with
`𝒪_E`-coefficients) and `A --ℓ--> A ⟶ Z ⟶ A⟦1⟧` distinguished, every element of a normal
subgroup `V` of finite index acting trivially on `Ψ_{M''} Z` acts trivially on `Ψ_{M''} A`. -/
theorem autAction_baseChangeAut_eq_id_of_distinguished_of_separated [IsAlgClosed K] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓk : ringChar k' ≠ ℓ)
    {A Z : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (π : A ⟶ Z) (δ : Z ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (ℓ • 𝟙 A) π δ ∈ distTriang _)
    (hsep : ∀ f : End (((baseChange hM b hb v hv).nearbyCycles Λ).obj A),
      (∀ m : ℕ, ∃ g : End (((baseChange hM b hb v hv).nearbyCycles Λ).obj A),
        f = (ℓ ^ m) • g) → f = 0)
    (V : Subgroup (GenericAut k' K)) [V.Normal] [V.FiniteIndex]
    (hV : ∀ σ ∈ V, (baseChangeAut hM b hb v hv σ).autAction Λ Z = 𝟙 _) {σ : GenericAut k' K}
    (hσ : σ ∈ V) : (baseChangeAut hM b hb v hv σ).autAction Λ A = 𝟙 _ := by
  let Ψ := (baseChange hM b hb v hv).nearbyCycles Λ
  have hT' := Ψ.map_distinguished _ hT
  let ρ := (baseChangeAutActionHom hM b hb v hv Λ A).comp V.subtype
  have hρ : ∀ τ : V, ρ τ ≫ Ψ.map π = Ψ.map π := fun τ ↦
    (Hom.autAction_naturality _ _ π).trans
      (by rw [Subgroup.coe_subtype, hV _ τ.2, Category.comp_id])
  have hπ : ∀ f : End (Ψ.obj A), f ≫ Ψ.map π = 0 → ∃ g : End (Ψ.obj A), f = ℓ • g := by
    intro f hf
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT' f hf
    let g' : Ψ.obj A ⟶ Ψ.obj A := g
    have hg' : f = g' ≫ Ψ.map (ℓ • 𝟙 A) := hg
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.comp_nsmul,
      Category.comp_id] at hg'
    exact ⟨g', hg'⟩
  have hdivV : ∀ (m : ℕ) (τ : V), ∃ τ' : V, τ' ^ ℓ ^ m = τ := fun m τ ↦ by
    obtain ⟨τ', hτ', h⟩ := V.exists_mem_pow_eq_of_forall_exists_pow
      (GenericAut.exists_pow_ell_pow_eq hℓ hℓk m) τ.2
    exact ⟨⟨τ', hτ'⟩, Subtype.ext (by rw [Subgroup.coe_pow]; exact h)⟩
  have key := @CategoryTheory.MonoidHom.eq_one_of_comp_eq_of_forall_exists_pow_of_separated _ _ _
    (Ψ.obj A) (Ψ.obj Z) (Ψ.map π) ℓ hsep hπ V _ ρ hρ hdivV ⟨σ, hσ⟩
  rw [MonoidHom.comp_apply, baseChangeAutActionHom_apply, End.one_def] at key
  exact key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
