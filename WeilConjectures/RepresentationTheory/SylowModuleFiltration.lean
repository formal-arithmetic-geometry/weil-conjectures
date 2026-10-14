/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Sylow reduction of a finite `ℓ`-primary representation

Let `G` be a compact topological group, `ℓ` a prime and `M` a finite `ℓ`-primary `ℤ`-linear
representation of `G` with open stabilizers. The kernel of the action is open, and the inverse
image of an `ℓ`-Sylow subgroup of the finite quotient is an open subgroup `H` of index prime to
`ℓ` acting on `M` through an `ℓ`-group. Such an action has nonzero fixed vectors killed by `ℓ`
on every nonzero finite `ℓ`-primary module (by the congruence `#Mᴾ ≡ #M (mod ℓ)`), so `M|_H`
has a filtration with trivial `𝔽_ℓ` quotients.

## Main statements

- `exists_ne_zero_nsmul_eq_zero_smul_eq_of_isPGroup`: the fixed vector.
- `exists_filtration_of_isPGroup`: the filtration for an action through an `ℓ`-group.
- `Rep.exists_openSubgroup_primary_module_filtration`: the filtration of `M|_H`.
-/

@[expose] public section

universe u w

section FixedPoints

variable {K : Type*} [Group K] {A : Type*} [AddCommGroup A] [DistribMulAction K A]

/-- The action of `K ⧸ N` on `A` when `N` acts trivially. -/
private abbrev mulActionQuotientOfForall (N : Subgroup K) [N.Normal]
    (hN : ∀ n ∈ N, ∀ a : A, n • a = a) : MulAction (K ⧸ N) A where
  smul q a := Quotient.liftOn' q (· • a) fun x y h ↦ by
    rw [QuotientGroup.leftRel_apply] at h
    conv_rhs => rw [show y = x * (x⁻¹ * y) by group, mul_smul, hN _ h a]
  one_smul a := one_smul K a
  mul_smul q r a := Quotient.inductionOn₂' q r fun x y ↦ mul_smul x y a

omit [Group K] [DistribMulAction K A] in
private lemma natCard_dvd_of_forall_pow_nsmul (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [Finite A]
    [Nontrivial A] (hA : ∀ a : A, ∃ j : ℕ, ℓ ^ j • a = 0) : ℓ ∣ Nat.card A := by
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

/-- The action of `K` on the quotient of `A` by a `K`-stable subgroup. -/
private abbrev distribMulActionQuotient (B : AddSubgroup A)
    (hB : ∀ k : K, ∀ b ∈ B, k • b ∈ B) : DistribMulAction K (A ⧸ B) where
  smul k := QuotientAddGroup.map B B (DistribSMul.toAddMonoidHom A k) fun b hb ↦ hB k b hb
  one_smul q := QuotientAddGroup.induction_on q fun a ↦ by
    change QuotientAddGroup.mk ((1 : K) • a) = _
    rw [one_smul]
  mul_smul k k' q := QuotientAddGroup.induction_on q fun a ↦ by
    change QuotientAddGroup.mk ((k * k') • a) = QuotientAddGroup.mk (k • k' • a)
    rw [mul_smul]
  smul_zero k := map_zero _
  smul_add k := map_add _

/-- **Filtration of a module over an `ℓ`-group.** Let `K` act on a finite `ℓ`-primary abelian
group `A` through an `ℓ`-group, and let `B` be a `K`-stable subgroup. Then there is a finite
increasing chain of `K`-stable subgroups from `B` to `A` whose successive quotients are killed
by `ℓ` and have trivial `K`-action. -/
theorem exists_filtration_of_isPGroup_of_le (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [Finite A]
    (N : Subgroup K) [N.Normal] (hN : ∀ n ∈ N, ∀ a : A, n • a = a)
    (hK : ∀ k : K, ∃ j : ℕ, k ^ ℓ ^ j ∈ N) (hA : ∀ a : A, ∃ j : ℕ, ℓ ^ j • a = 0)
    (B : AddSubgroup A) (hB : ∀ k : K, ∀ b ∈ B, k • b ∈ B) :
    ∃ (n : ℕ) (F : ℕ → AddSubgroup A), F 0 = B ∧ F n = ⊤ ∧ Monotone F ∧
      (∀ i, ∀ k : K, ∀ x ∈ F i, k • x ∈ F i) ∧ (∀ i, ∀ x ∈ F (i + 1), ℓ • x ∈ F i) ∧
      (∀ i, ∀ k : K, ∀ x ∈ F (i + 1), k • x - x ∈ F i) := by
  induction B using WellFoundedGT.induction with
  | _ B ih =>
  by_cases htop : B = ⊤
  · refine ⟨0, fun _ ↦ B, rfl, htop, monotone_const, fun _ ↦ hB, fun _ x _ ↦ ?_,
      fun _ k x _ ↦ ?_⟩
    · rw [htop]
      exact AddSubgroup.mem_top _
    · rw [htop]
      exact AddSubgroup.mem_top _
  let := distribMulActionQuotient B hB
  have : Nontrivial (A ⧸ B) := by
    obtain ⟨a, ha⟩ : ∃ a, a ∉ B := by
      by_contra! h
      exact htop (eq_top_iff.2 fun a _ ↦ h a)
    exact ⟨⟨QuotientAddGroup.mk a, 0, fun h ↦ ha ((QuotientAddGroup.eq_zero_iff a).1 h)⟩⟩
  have : Finite (A ⧸ B) := Finite.of_surjective _ (QuotientAddGroup.mk_surjective (s := B))
  obtain ⟨q, hq0, hqℓ, hqK⟩ := exists_ne_zero_nsmul_eq_zero_smul_eq_of_isPGroup (A := A ⧸ B) ℓ N
    (fun n hn q ↦ QuotientAddGroup.induction_on q fun a ↦ congrArg QuotientAddGroup.mk
      (hN n hn a))
    hK (fun q ↦ QuotientAddGroup.induction_on q fun a ↦ by
      obtain ⟨j, hj⟩ := hA a
      exact ⟨j, by rw [← QuotientAddGroup.mk_nsmul, hj, QuotientAddGroup.mk_zero]⟩)
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hxB : x ∉ B := fun h ↦ hq0 ((QuotientAddGroup.eq_zero_iff x).2 h)
  have hxℓ : ℓ • x ∈ B := (QuotientAddGroup.eq_zero_iff _).1 (by
    rw [QuotientAddGroup.mk_nsmul]; exact hqℓ)
  have hxK (k : K) : k • x - x ∈ B := by
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    exact hqK k
  let B' := B ⊔ AddSubgroup.zmultiples x
  have hmem {y : A} (hy : y ∈ B') : ∃ b ∈ B, ∃ m : ℤ, b + m • x = y := by
    obtain ⟨b, hb, z, ⟨m, rfl⟩, rfl⟩ := AddSubgroup.mem_sup.1 hy
    exact ⟨b, hb, m, rfl⟩
  have hB' : ∀ k : K, ∀ y ∈ B', k • y ∈ B' := by
    intro k y hy
    obtain ⟨b, hb, m, rfl⟩ := hmem hy
    rw [smul_add, smul_comm, show k • x = (k • x - x) + x by abel, smul_add, ← add_assoc]
    refine add_mem (AddSubgroup.mem_sup_left (add_mem (hB k b hb) (zsmul_mem (hxK k) m)))
      (AddSubgroup.mem_sup_right (zsmul_mem (AddSubgroup.mem_zmultiples x) m))
  have hlt : B < B' := lt_of_le_of_ne le_sup_left fun h ↦
    hxB (h ▸ AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples x))
  obtain ⟨n, F, hF0, hFn, hFm, hFK, hFℓ, hFt⟩ := ih B' hlt hB'
  refine ⟨n + 1, fun i ↦ Nat.casesOn i B F, rfl, hFn, monotone_nat_of_le_succ fun i ↦ ?_,
    fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · cases i with
    | zero =>
      change B ≤ F 0
      exact hF0 ▸ hlt.le
    | succ i => exact hFm i.le_succ
  · cases i with
    | zero => exact hB
    | succ i => exact hFK i
  · cases i with
    | zero =>
      intro y hy
      obtain ⟨b, hb, m, rfl⟩ := hmem (show y ∈ B' from hF0 ▸ hy)
      change _ ∈ B
      rw [smul_add, smul_comm]
      exact add_mem (nsmul_mem hb ℓ) (zsmul_mem hxℓ m)
    | succ i => exact hFℓ i
  · cases i with
    | zero =>
      intro k y hy
      obtain ⟨b, hb, m, rfl⟩ := hmem (show y ∈ B' from hF0 ▸ hy)
      change _ ∈ B
      rw [smul_add, smul_comm, show k • b + m • k • x - (b + m • x) =
        (k • b - b) + m • (k • x - x) by rw [zsmul_sub]; abel]
      exact add_mem (sub_mem (hB k b hb) hb) (zsmul_mem (hxK k) m)
    | succ i => exact hFt i

/-- The filtration of `exists_filtration_of_isPGroup_of_le` starting from `0`. -/
theorem exists_filtration_of_isPGroup (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [Finite A]
    (N : Subgroup K) [N.Normal] (hN : ∀ n ∈ N, ∀ a : A, n • a = a)
    (hK : ∀ k : K, ∃ j : ℕ, k ^ ℓ ^ j ∈ N) (hA : ∀ a : A, ∃ j : ℕ, ℓ ^ j • a = 0) :
    ∃ (n : ℕ) (F : ℕ → AddSubgroup A), F 0 = ⊥ ∧ F n = ⊤ ∧ Monotone F ∧
      (∀ i, ∀ k : K, ∀ x ∈ F i, k • x ∈ F i) ∧ (∀ i, ∀ x ∈ F (i + 1), ℓ • x ∈ F i) ∧
      (∀ i, ∀ k : K, ∀ x ∈ F (i + 1), k • x - x ∈ F i) :=
  exists_filtration_of_isPGroup_of_le ℓ N hN hK hA ⊥ fun k b hb ↦ by
    rw [(AddSubgroup.mem_bot).1 hb, smul_zero]
    exact zero_mem _

end FixedPoints

namespace Rep

/-- **Sylow reduction of a finite `ℓ`-primary representation.** Let `G` be a compact (e.g.
profinite) group, `ℓ` a prime and `M` a finite `ℓ`-primary `G`-module with open stabilizers.
There is an open subgroup `H` of index prime to `ℓ` and a finite filtration
`0 = F₀ ≤ F₁ ≤ ⋯ ≤ Fₙ = M` by `H`-stable subgroups whose successive quotients are trivial
`𝔽_ℓ`-representations of `H`: they are killed by `ℓ` and `H` acts trivially on them.
(blueprint: `lem-sc-sylow-module-filtration`) -/
theorem exists_openSubgroup_primary_module_filtration
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (M : Rep.{w} ℤ G) [Finite M.V]
    (hM_open : ∀ x : M.V, IsOpen {g : G | M.ρ g x = x})
    (hM : ∀ x : M.V, ∃ j : ℕ, ℓ ^ j • x = 0) :
    ∃ H : OpenSubgroup G, H.toSubgroup.index.Coprime ℓ ∧
      ∃ (n : ℕ) (F : Fin (n + 1) → AddSubgroup M.V),
        Monotone F ∧ F 0 = ⊥ ∧ F (Fin.last n) = ⊤ ∧
        (∀ (i : Fin (n + 1)) (g : H) (x : M.V), x ∈ F i → M.ρ (g : G) x ∈ F i) ∧
        (∀ (i : Fin n) (x : M.V), x ∈ F i.succ →
          ℓ • x ∈ F i.castSucc ∧ ∀ g : H, M.ρ (g : G) x - x ∈ F i.castSucc) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let := DistribMulAction.compHom M.V M.ρ
  -- the kernel of the action, an open normal subgroup
  let N : Subgroup G := ⨅ x : M.V, MulAction.stabilizer G x
  have hNmem {g : G} : g ∈ N ↔ ∀ x : M.V, M.ρ g x = x := Subgroup.mem_iInf
  have : N.Normal := ⟨fun n hn g ↦ by
    rw [hNmem] at hn ⊢
    intro x
    simp [hn]⟩
  have hNo : IsOpen (N : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hM_open
  have : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  obtain ⟨P⟩ : Nonempty (Sylow ℓ (G ⧸ N)) := inferInstance
  let K : Subgroup G := (P : Subgroup (G ⧸ N)).comap (QuotientGroup.mk' N)
  have hNK : N ≤ K := fun g hg ↦ by
    simp [K, (QuotientGroup.eq_one_iff g).2 hg]
  let H : OpenSubgroup G := ⟨K, Subgroup.isOpen_mono hNK hNo⟩
  have hidx : ¬ ℓ ∣ K.index := by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact P.not_dvd_index
  let : DistribMulAction K M.V := DistribMulAction.compHom M.V (M.ρ.comp K.subtype)
  obtain ⟨n, F, h0, hn, hmono, hK, hℓF, htriv⟩ := exists_filtration_of_isPGroup (K := K) ℓ
    (N.comap K.subtype) (fun k hk x ↦ hNmem.1 hk x) (fun k ↦ by
      obtain ⟨j, hj⟩ := P.isPGroup' ⟨_, k.2⟩
      refine ⟨j, ?_⟩
      rw [Subgroup.mem_comap, map_pow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact congrArg Subtype.val hj) hM
  refine ⟨H, Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hidx), n,
    fun i ↦ F i, fun i j hij ↦ hmono hij, h0, hn, fun i g x hx ↦ hK i ⟨g, g.2⟩ x hx,
    fun i x hx ↦ ⟨hℓF i x hx, fun g ↦ htriv i ⟨g, g.2⟩ x hx⟩⟩

end Rep
