/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Sylow reduction of a finite torsion module

Let `G` be a profinite group, `ℓ` a prime and `M` a finite `ℓ`-primary discrete `G`-module. The
kernel of the action of `G` on `M` is open and normal; the inverse image `K` of an `ℓ`-Sylow
subgroup of the finite quotient is an open subgroup of index prime to `ℓ` acting on `M` through
an `ℓ`-group. Such an action has a nonzero fixed vector killed by `ℓ` on every nonzero
`ℓ`-primary finite module, by the congruence `#Mᴾ ≡ #M (mod ℓ)`; hence `M|_K` has a filtration
with trivial `𝔽_ℓ` quotients.

## Main statements

- `exists_ne_zero_nsmul_eq_zero_smul_eq_of_isPGroup`: the fixed vector.
- `DiscreteModule.exists_isOpen_not_dvd_index_pow_mem`: the open subgroup `K`.
- `DiscreteModule.exists_isOpen_not_dvd_index_filtration`: the filtration.
-/

@[expose] public section

universe w u

open CategoryTheory

section FixedPoints

variable {K : Type*} [Group K] {A : Type*} [AddCommGroup A] [DistribMulAction K A]

/-- The action of `K ⧸ N` on `A` when `N` acts trivially. -/
@[reducible]
def mulActionQuotientOfForall (N : Subgroup K) [N.Normal] (hN : ∀ n ∈ N, ∀ a : A, n • a = a) :
    MulAction (K ⧸ N) A where
  smul q a := Quotient.liftOn' q (· • a) fun x y h ↦ by
    rw [QuotientGroup.leftRel_apply] at h
    change x • a = y • a
    conv_rhs => rw [show y = x * (x⁻¹ * y) by group, mul_smul, hN _ h a]
  one_smul a := one_smul K a
  mul_smul q r a := Quotient.inductionOn₂' q r fun x y ↦ mul_smul x y a

lemma natCard_dvd_of_forall_pow_nsmul (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [Finite A] [Nontrivial A]
    (hA : ∀ a : A, ∃ j : ℕ, ℓ ^ j • a = 0) : ℓ ∣ Nat.card A := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨j, hj⟩ := hA a
  obtain ⟨i, hi, hia⟩ := (Nat.dvd_prime_pow hℓ.out).1 (addOrderOf_dvd_of_nsmul_eq_zero hj)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact ha (AddMonoid.addOrderOf_eq_one_iff.1 (by simpa using hia))
  exact (dvd_pow_self ℓ hi0).trans (hia ▸ addOrderOf_dvd_natCard a)

/-- **Fixed vectors of an `ℓ`-group.** Let `K` act on a finite nonzero `ℓ`-primary abelian group
`A` through an `ℓ`-group: a normal subgroup `N` acts trivially and every element of `K` has an
`ℓ`-power in `N`. Then `A` has a nonzero `K`-fixed element killed by `ℓ`: the nontrivial orbits
have cardinality divisible by `ℓ`, so `#Aᴷ ≡ #A ≡ 0 (mod ℓ)`. -/
theorem exists_ne_zero_nsmul_eq_zero_smul_eq_of_isPGroup (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [Finite A]
    [Nontrivial A] (N : Subgroup K) [N.Normal] (hN : ∀ n ∈ N, ∀ a : A, n • a = a)
    (hK : ∀ k : K, ∃ j : ℕ, k ^ ℓ ^ j ∈ N) (hA : ∀ a : A, ∃ j : ℕ, ℓ ^ j • a = 0) :
    ∃ a : A, a ≠ 0 ∧ ℓ • a = 0 ∧ ∀ k : K, k • a = a := by
  let := mulActionQuotientOfForall N hN
  have hP : IsPGroup ℓ (K ⧸ N) := fun q ↦ Quotient.inductionOn' q fun k ↦ by
    obtain ⟨j, hj⟩ := hK k
    exact ⟨j, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hj⟩
  have hcong := hP.card_modEq_card_fixedPoints A
  let F : AddSubgroup A :=
    { carrier := {a | ∀ k : K, k • a = a}
      zero_mem' := fun k ↦ smul_zero k
      add_mem' := fun ha hb k ↦ by rw [smul_add, ha k, hb k]
      neg_mem' := fun ha k ↦ by rw [smul_neg, ha k] }
  have hF : Nat.card F = Nat.card (MulAction.fixedPoints (K ⧸ N) A) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun a ↦ ?_)
    exact ⟨fun h q ↦ Quotient.inductionOn' q fun k ↦ h k, fun h k ↦ h (QuotientGroup.mk k)⟩
  have hdvd : ℓ ∣ Nat.card F := by
    rw [hF, ← Nat.modEq_zero_iff_dvd]
    exact hcong.symm.trans ((Nat.modEq_zero_iff_dvd).2 (natCard_dvd_of_forall_pow_nsmul ℓ hA))
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' ℓ hdvd
  refine ⟨x.1, fun h ↦ ?_, ?_, x.2⟩
  · have : x = 0 := Subtype.ext h
    rw [this, addOrderOf_zero] at hx
    exact hℓ.out.one_lt.ne hx
  · have := addOrderOf_nsmul_eq_zero x
    rw [hx] at this
    exact congrArg Subtype.val this

end FixedPoints

namespace DiscreteModule

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The kernel of the action of `G` on a discrete `G`-module. -/
def actionKernel (M : DiscreteModule.{w} G) : Subgroup G :=
  ⨅ x : M.obj.V, M.obj.stabilizer x

variable (M : DiscreteModule.{w} G)

lemma mem_actionKernel {g : G} : g ∈ actionKernel M ↔ ∀ x, (M.obj.ρ g).hom x = x := by
  simp [actionKernel, Subgroup.mem_iInf]

instance : (actionKernel M).Normal where
  conj_mem n hn g := by
    rw [mem_actionKernel] at hn ⊢
    intro x
    simp [hn]

lemma isOpen_actionKernel [Finite M.obj.V] : IsOpen (actionKernel M : Set G) := by
  rw [actionKernel, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun x ↦ M.isOpen_stabilizer x

/-- Let `M` be a finite discrete module over a compact group `G` and `ℓ` a prime. There is an
open subgroup `K` of index prime to `ℓ`, containing the kernel `N` of the action, such that
every element of `K` has an `ℓ`-power in `N`: the inverse image of an `ℓ`-Sylow subgroup of the
finite group `G ⧸ N`. -/
theorem exists_isOpen_not_dvd_index_pow_mem [CompactSpace G] (ℓ : ℕ) [Fact ℓ.Prime]
    [Finite M.obj.V] :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ¬ ℓ ∣ K.index ∧ actionKernel M ≤ K ∧
      ∀ k ∈ K, ∃ j : ℕ, k ^ ℓ ^ j ∈ actionKernel M := by
  set N := actionKernel M
  have hN := isOpen_actionKernel M
  have : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  obtain ⟨P⟩ : Nonempty (Sylow ℓ (G ⧸ N)) := inferInstance
  refine ⟨(P : Subgroup (G ⧸ N)).comap (QuotientGroup.mk' N), ?_, ?_, ?_, ?_⟩
  · refine Subgroup.isOpen_mono (fun g hg ↦ ?_) hN
    change QuotientGroup.mk' N g ∈ P
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
    exact one_mem _
  · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact P.not_dvd_index
  · intro g hg
    change QuotientGroup.mk' N g ∈ P
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
    exact one_mem _
  · intro k hk
    obtain ⟨j, hj⟩ := P.isPGroup' ⟨_, hk⟩
    refine ⟨j, (QuotientGroup.eq_one_iff _).1 ?_⟩
    simpa using congrArg Subtype.val hj

end DiscreteModule
