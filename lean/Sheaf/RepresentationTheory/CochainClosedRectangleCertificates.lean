module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Data.PNat.Defs
import Mathlib.Topology.ClopenBox
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! # Closed finite-field rectangle certificates for parameter cochains

Source: the agent-formulated scalar analytic input attached to paragraph (3) of
literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md. The blueprint supplies application
context, not this auxiliary theorem. The argument uses Stacks Tags 08ZU and 0CQN.
(blueprint: lem-sfb-cochain-closed-rectangle-certificates)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open Topology
open scoped Pointwise

namespace ContinuousCohomology

/-- A continuous parameter cochain has a countable closed parameter cover certified by
finite-field values on right-coset rectangles. The displayed formula substitutes
successive differences into z, so it is exactly f_z, without a cocycle hypothesis.
The normed algebra structure means that the norm on Ω extends the p-adic norm.

Source: agent-formulated scalar analytic input for paragraph (3) of the blueprint's
sk-thm-sf-ctf-stability-direct-images.proof.md; Stacks Tags 08ZU and 0CQN
(blueprint: lem-sfb-cochain-closed-rectangle-certificates).

Proof:
1. Every open subgroup is clopen, because its complement is the union of its other
   open cosets. Compactness makes its coset cover finite, giving finite index.
   Translate the assumed open-normal identity basis to obtain a clopen basis.
   Such cosets separate distinct points, so G is totally disconnected.
2. By lem-sfb-compact-metrizable-second-countable, G is second countable. Apply
   lem-sfb-profinite-countable-clopens to count its clopens. The clopen basis and
   open subgroups are countable. Each open normal subgroup has finitely many cosets,
   so finitely many (n+1)-tuples of cosets; their rectangles form a countable set.
   Choose one subgroup-and-centres presentation for each distinct rectangle.
3. The successive-difference formula is continuous. Fix s and put
   E_N = {y | f_z(s;y) belongs to F_N}. These sets are closed and cover G^(n+1).
   By lem-weil-pbc-tychonoff-product-quasi-compact the product is compact. It is
   nonempty (the identity tuple), Hausdorff and locally compact. Apply
   lem-sfb-baire-closed-cover-interior with the whole product as subspace:
   some E_N contains a nonempty open product with centres a_i. Choose an open
   normal subgroup inside each U_i a_i^(-1), and intersect the finitely many
   subgroups to get H. Then every H a_i lies inside U_i, giving a rectangle in E_N.
4. For each rectangle R and N, the certificate set A(R,N) is the intersection,
   over y in R, of the closed preimages {s | f_z(s;y) belongs to F_N}. Thus it is
   closed. Step 3 proves these sets cover S. Discard exactly the empty ones.
   The remaining countable index set is nonempty since S is nonempty. Enumerate
   it by positive integers, repeating entries if it is finite. The chosen
   presentations give H_j, a_j and N_j, with all the asserted properties.
-/
theorem exists_cochain_closed_rectangle_certificates
    (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (F : ℕ → IntermediateField (Padic ℓ) Ω) (hFmono : Monotone F)
    (hFfinite : ∀ N : ℕ, FiniteDimensional (Padic ℓ) (F N))
    (hFclosed : ∀ N : ℕ, IsClosed (F N : Set Ω))
    (hFcover : (⋃ N : ℕ, (F N : Set Ω)) = Set.univ)
    (S : Type v) [TopologicalSpace S] [Nonempty S] [CompactSpace S]
    [TopologicalSpace.MetrizableSpace S] [T2Space S] [TotallyDisconnectedSpace S]
    (G : Type w) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TopologicalSpace.MetrizableSpace G] [T2Space G]
    (hG : ∀ U ∈ nhds (1 : G), ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ U)
    (n : ℕ) (hn : 1 ≤ n) (z : C(S × (Fin n → G), Ω)) :
    (∃ (H : ℕ+ → OpenNormalSubgroup G) (a : ℕ+ → Fin (n + 1) → G)
        (N : ℕ+ → ℕ) (A : ℕ+ → Set S),
      (∀ j : ℕ+, A j = {s : S | ∀ y ∈ Set.pi Set.univ
          (fun i : Fin (n + 1) ↦ MulOpposite.op (a j i) • (H j : Set G)),
        z (s, fun i : Fin n ↦ (y i.castSucc)⁻¹ * y i.succ) ∈ F (N j)}) ∧
      (∀ j : ℕ+, (A j).Nonempty ∧ IsClosed (A j) ∧ Finite (G ⧸ (H j).toSubgroup)) ∧
      (⋃ j : ℕ+, A j) = Set.univ) ∧
    (∃ B : Set (Set G), B.Countable ∧ TopologicalSpace.IsTopologicalBasis B ∧
      ∀ U ∈ B, IsClopen U) ∧
    Countable (TopologicalSpace.Clopens G) ∧ Countable (OpenSubgroup G) ∧
    {R : Set (Fin (n + 1) → G) | ∃ H : OpenNormalSubgroup G,
      ∃ a : Fin (n + 1) → G,
        R = Set.pi Set.univ (fun i ↦ MulOpposite.op (a i) • (H : Set G))}.Countable := by
  classical
  have _ := hFmono
  have _ := hFfinite
  have _ := hn
  have hcoset (H : OpenNormalSubgroup G) (a : G) :
      IsClopen (MulOpposite.op a • (H : Set G)) := by
    have heq : MulOpposite.op a • (H : Set G) =
        (fun x : G ↦ x * a⁻¹) ⁻¹' (H : Set G) := by
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem, MulOpposite.smul_eq_mul_unop]
    rw [heq]
    exact H.toOpenSubgroup.isClopen.preimage (continuous_id.mul continuous_const)
  have hbasis : TopologicalSpace.IsTopologicalBasis {U : Set G | IsClopen U} := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun U hU ↦ hU.isOpen)
    intro x U hx hU
    have hneigh : (fun y : G ↦ y * x) ⁻¹' U ∈ nhds (1 : G) := by
      have hc : Continuous (fun y : G ↦ y * x) := continuous_id.mul continuous_const
      exact (hU.preimage hc).mem_nhds (by simpa using hx)
    obtain ⟨H, hH⟩ := hG _ hneigh
    refine ⟨MulOpposite.op x • (H : Set G), hcoset H x, ?_, ?_⟩
    · simpa [MulOpposite.smul_eq_mul_unop] using
        (Set.smul_mem_smul_set_iff (a := MulOpposite.op x) (x := (1 : G))
          (s := (H : Set G))).2 H.one_mem
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := Set.mem_smul_set.mp hy
      exact hH ht
  have : TotallySeparatedSpace G := totallySeparatedSpace_of_t0_of_basis_clopen hbasis
  have : Countable (TopologicalSpace.Clopens G) :=
    TopologicalSpace.Clopens.countable_iff_secondCountable.mpr inferInstance
  have hsubgroups : Countable (OpenSubgroup G) := by
    let f : OpenSubgroup G → TopologicalSpace.Clopens G := fun H ↦ ⟨H, H.isClopen⟩
    apply Function.Injective.countable (f := f)
    intro H K h
    apply SetLike.coe_injective
    exact congrArg (fun U : TopologicalSpace.Clopens G ↦ (U : Set G)) h
  let rect (H : OpenNormalSubgroup G) (a : Fin (n + 1) → G) :=
    Set.pi Set.univ (fun i ↦ MulOpposite.op (a i) • (H : Set G))
  let rectangles : Set (Set (Fin (n + 1) → G)) :=
    {R | ∃ H : OpenNormalSubgroup G, ∃ a, R = rect H a}
  have hrectclopen : ∀ R ∈ rectangles, IsClopen R := by
    rintro R ⟨H, a, rfl⟩
    exact ⟨isClosed_set_pi (fun i _ ↦ (hcoset H (a i)).isClosed),
      isOpen_set_pi Set.finite_univ (fun i _ ↦ (hcoset H (a i)).isOpen)⟩
  have : Countable (TopologicalSpace.Clopens (Fin (n + 1) → G)) :=
    TopologicalSpace.Clopens.countable_iff_secondCountable.mpr inferInstance
  have hrectcount : rectangles.Countable := by
    let f : rectangles → TopologicalSpace.Clopens (Fin (n + 1) → G) :=
      fun R ↦ ⟨R, hrectclopen R R.property⟩
    apply Function.Injective.countable (f := f)
    intro R T h
    apply Subtype.ext
    exact congrArg (fun U : TopologicalSpace.Clopens (Fin (n + 1) → G) ↦
      (U : Set (Fin (n + 1) → G))) h
  let f : S → (Fin (n + 1) → G) → Ω :=
    fun s y ↦ z (s, fun i : Fin n ↦ (y i.castSucc)⁻¹ * y i.succ)
  have hf (s : S) : Continuous (f s) := by
    apply z.continuous.comp
    exact continuous_const.prodMk (continuous_pi fun i ↦
      (continuous_apply i.castSucc).inv.mul (continuous_apply i.succ))
  have hlocal (s : S) : ∃ H a N, ∀ y ∈ rect H a, f s y ∈ F N := by
    have hcover : (⋃ N : ℕ, (f s) ⁻¹' (F N : Set Ω)) = Set.univ := by
      rw [← Set.preimage_iUnion, hFcover, Set.preimage_univ]
    obtain ⟨N, a, ha⟩ := nonempty_interior_of_iUnion_of_closed
      (fun N ↦ (hFclosed N).preimage (hf s)) hcover
    obtain ⟨U, hU, hUa⟩ := isOpen_pi_iff'.mp isOpen_interior a ha
    have hneigh : (⋂ i : Fin (n + 1), (fun t : G ↦ t * a i) ⁻¹' U i) ∈
        nhds (1 : G) := by
      apply Filter.iInter_mem.mpr
      intro i
      exact (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds
        (by simpa using (hU i).1.mem_nhds (hU i).2)
    obtain ⟨H, hH⟩ := hG _ hneigh
    refine ⟨H, a, N, ?_⟩
    intro y hy
    change y ∈ (f s) ⁻¹' (F N : Set Ω)
    apply interior_subset
    apply hUa
    intro i _
    obtain ⟨t, ht, hty⟩ := Set.mem_smul_set.mp (hy i (Set.mem_univ i))
    have htU := Set.mem_iInter.mp (hH ht) i
    change t * a i ∈ U i at htU
    simpa [← hty, MulOpposite.smul_eq_mul_unop] using htU
  let cert (R : Set (Fin (n + 1) → G)) (N : ℕ) : Set S :=
    {s | ∀ y ∈ R, f s y ∈ F N}
  have hclosed (R : Set (Fin (n + 1) → G)) (N : ℕ) : IsClosed (cert R N) := by
    have heq : cert R N = ⋂ y ∈ R, (fun s ↦ f s y) ⁻¹' (F N : Set Ω) := by
      ext s
      simp [cert]
    rw [heq]
    apply isClosed_biInter
    intro y hy
    exact (hFclosed N).preimage (z.continuous.comp (continuous_id.prodMk continuous_const))
  have : Countable rectangles := hrectcount
  let J := {p : rectangles × ℕ // (cert p.1.1 p.2).Nonempty}
  have hcovered (s : S) : ∃ j : J, s ∈ cert j.val.1.1 j.val.2 := by
    obtain ⟨H, a, N, h⟩ := hlocal s
    exact ⟨⟨(⟨rect H a, H, a, rfl⟩, N), s, h⟩, h⟩
  have : Nonempty J := by
    obtain ⟨s⟩ := ‹Nonempty S›
    obtain ⟨j, _⟩ := hcovered s
    exact ⟨j⟩
  obtain ⟨e, he⟩ := exists_surjective_nat J
  have hpresent (j : J) : ∃ H a, j.val.1.1 = rect H a := j.val.1.property
  choose H a hHa using hpresent
  let epos (j : ℕ+) := e (j.val - 1)
  have hepos : Function.Surjective epos := by
    intro j
    obtain ⟨k, hk⟩ := he j
    exact ⟨⟨k + 1, Nat.zero_lt_succ k⟩, by simpa [epos] using hk⟩
  refine ⟨?_, ?_, inferInstance, hsubgroups, hrectcount⟩
  · refine ⟨(fun j ↦ H (epos j)), (fun j ↦ a (epos j)),
      (fun j ↦ (epos j).val.2),
      (fun j ↦ cert (epos j).val.1.1 (epos j).val.2), ?_, ?_, ?_⟩
    · intro j
      change cert _ _ = cert (rect _ _) _
      rw [hHa]
    · intro j
      exact ⟨(epos j).property, hclosed _ _,
        Subgroup.quotient_finite_of_isOpen _ (H (epos j)).toOpenSubgroup.isOpen⟩
    · apply Set.eq_univ_of_forall
      intro s
      obtain ⟨j, hj⟩ := hcovered s
      obtain ⟨k, rfl⟩ := hepos j
      exact Set.mem_iUnion.mpr ⟨k, hj⟩
  · refine ⟨{U : Set G | IsClopen U}, ?_, hbasis, fun U hU ↦ hU⟩
    let f : {U : Set G | IsClopen U} → TopologicalSpace.Clopens G := fun U ↦ ⟨U, U.property⟩
    apply Function.Injective.countable (f := f)
    intro U V h
    apply Subtype.ext
    exact congrArg (fun U : TopologicalSpace.Clopens G ↦ (U : Set G)) h

end ContinuousCohomology
