/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProfiniteIntegerDefinition
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.GroupTheory.OrderOfElement

/-! # Continuous profinite integer powers

Source: Stacks Project, Tag 0BR1, `topology-lemma-profinite-group`, consequence of the
finite-quotient presentation for integer powers (blueprint: lem-sf-profinite-integer-powers).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

-- The finite-cylinder argument also handles the empty cylinder (product modulus one).
private theorem integer_dense :
    DenseRange (fun m : ℤ ↦
      (profiniteIntegerInt m : Multiplicative profiniteIntegerLimit)) := by
  classical
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨a, ha⟩
  rw [← hsv] at ha
  obtain ⟨J, V, hV, hsub⟩ := isOpen_pi_iff.mp hsO a.1 ha
  let n : ℕ := ∏ i ∈ J, i.1
  have hn : 0 < n := Finset.prod_pos (fun i _ ↦ i.2)
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective (a.1 ⟨n, hn⟩)
  refine ⟨profiniteIntegerInt m, ?_, m, rfl⟩
  rw [← hsv]
  apply hsub
  intro i hi
  have hdiv : i.1 ∣ n := Finset.dvd_prod_of_mem (fun i : profiniteIntegerIndex ↦ i.1) hi
  have he : (m : ZMod i.1) = a.1 i := by
    calc
      (m : ZMod i.1) = ZMod.castHom hdiv (ZMod i.1) (m : ZMod n) := by simp
      _ = ZMod.castHom hdiv (ZMod i.1) (a.1 ⟨n, hn⟩) := congrArg _ hm
      _ = a.1 i := a.2 i ⟨n, hn⟩ hdiv
  change (m : ZMod i.1) ∈ V i
  rw [he]
  exact (hV i hi).2

private theorem integer_compact : CompactSpace (Multiplicative profiniteIntegerLimit) := by
  let (n : profiniteIntegerIndex) : NeZero n.1 := ⟨Nat.ne_of_gt n.2⟩
  have hclosed : IsClosed
      (profiniteIntegerLimit : Set (∀ n : profiniteIntegerIndex, ZMod n.1)) := by
    change IsClosed {a : ∀ n : profiniteIntegerIndex, ZMod n.1 |
      ∀ (m n : profiniteIntegerIndex) (h : m.1 ∣ n.1),
      ZMod.castHom h (ZMod m.1) (a n) = a m}
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun h ↦ ?_
    exact isClosed_eq
      ((continuous_of_discreteTopology : Continuous (ZMod.castHom h (ZMod m.1))).comp
        (continuous_apply n)) (continuous_apply m)
  exact isCompact_iff_compactSpace.mp hclosed.isCompact

private theorem finite_power {F : Type u} [Group F] [TopologicalSpace F] [Finite F]
    (g : F) : ∃ q : Multiplicative profiniteIntegerLimit →ₜ* F,
      ∀ m : ℤ, q (profiniteIntegerInt m) = g ^ m := by
  let n := Nat.card F
  have hn : 0 < n := Nat.card_pos
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let f : ZMod n →+ Additive F := ZMod.lift n
    ⟨(zpowersHom F g).toAdditiveRight, by
      change g ^ (n : ℤ) = 1
      simpa only [zpow_natCast] using (pow_card_eq_one' (x := g))⟩
  let ev : profiniteIntegerLimit →+ ZMod n :=
    { toFun := fun a ↦ a.1 ⟨n, hn⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let q : Multiplicative profiniteIntegerLimit →ₜ* F :=
    { (f.comp ev).toMultiplicativeLeft with
      continuous_toFun := by
        change Continuous (fun a : profiniteIntegerLimit ↦ f (a.1 ⟨n, hn⟩))
        exact (continuous_of_discreteTopology : Continuous f).comp
          ((continuous_apply (⟨n, hn⟩ : profiniteIntegerIndex)).comp continuous_subtype_val) }
  refine ⟨q, fun m ↦ ?_⟩
  change f (m : ZMod n) = Additive.ofMul (g ^ m)
  exact ZMod.lift_coe n _ m

/-- Every element of a compact Hausdorff totally disconnected topological group has a unique
continuous profinite-integer power parametrization, whose image is the closure of its integer
powers.

Source: Stacks Project, Tag 0BR1, topology-lemma-profinite-group: consequence for integer
powers (blueprint: lem-sf-profinite-integer-powers).

`Multiplicative` regards addition in the displayed residue limit as multiplication, so the
homomorphism has the same additive-domain/multiplicative-codomain meaning as in the node.
Uniqueness is among all continuous homomorphisms with the prescribed integer values.

Proof:
1. A basic open cylinder fixes finitely many coordinates. Their product is a positive
   common modulus; an integer representing that coordinate gives a diagonal point of the
   cylinder. Thus the diagonal integers are dense, without the full CRT identification.
2. The compatibility equations are closed equalizers in the compact product of finite
   discrete residue rings. Their intersection, the displayed limit, is compact.
3. For a finite group F, integer powers of g kill |F|. `ZMod.lift` descends this
   homomorphism to Z/|F|; evaluation at that residue coordinate is continuous.
4. Apply these coordinate maps to the finite quotients of P. Each transition identity
   holds on the dense diagonal integers, so it holds everywhere by the Hausdorff
   equalizer principle. The resulting compatible family is a continuous homomorphism
   into the finite-quotient limit. Compose with the inverse reconstruction isomorphism
   of lem-sf-profinite-group-finite-quotients to obtain q and its integer values.
5. Compactness makes the range of q closed. It contains the integer powers, hence their
   closure; continuity and density give the reverse inclusion.
6. Two continuous maps with the prescribed integer values agree on the dense diagonal
   integers and therefore agree everywhere.
-/
theorem existsUnique_profiniteIntegerPowerHom
    (P : Type u) [TopologicalSpace P] [Group P] [CompactSpace P] [T2Space P]
    [TotallyDisconnectedSpace P] [IsTopologicalGroup P] (h : P) :
    ∃ q : Multiplicative profiniteIntegerLimit →ₜ* P,
      (∀ m : ℤ, q (profiniteIntegerInt m) = h ^ m) ∧
        Set.range q = closure (Set.range fun m : ℤ => h ^ m) ∧
        ∀ q' : Multiplicative profiniteIntegerLimit →ₜ* P,
          (∀ m : ℤ, q' (profiniteIntegerInt m) = h ^ m) → q' = q := by
  classical
  let : CompactSpace (Multiplicative profiniteIntegerLimit) := integer_compact
  let Q := ProfiniteGrp.of P
  let F := ProfiniteGrp.diagram Q
  have hex (N : OpenNormalSubgroup Q) :
      ∃ q : Multiplicative profiniteIntegerLimit →ₜ* F.obj N,
        ∀ m : ℤ, q (profiniteIntegerInt m) = (QuotientGroup.mk h : F.obj N) ^ m := by
    let : Finite (F.obj N) := inferInstanceAs (Finite (Q ⧸ N.toSubgroup))
    exact finite_power (F := F.obj N) (QuotientGroup.mk h)
  choose q hq using hex
  have compat {N M : OpenNormalSubgroup Q} (f : N ⟶ M) :
      ∀ a, F.map f (q N a) = q M a := by
    have he := integer_dense.equalizer
      ((F.map f).hom.continuous.comp (q N).continuous) (q M).continuous
      (by
        funext m
        change F.map f (q N (profiniteIntegerInt m)) = q M (profiniteIntegerInt m)
        rw [hq N m, hq M m, map_zpow]
        rfl)
    exact congrFun he
  let r : Multiplicative profiniteIntegerLimit →ₜ* ProfiniteGrp.limit F :=
    { toFun := fun a ↦ ⟨fun N ↦ q N a, fun _ _ f ↦ compat f a⟩
      map_one' := by
        apply Subtype.ext
        funext N
        exact map_one (q N)
      map_mul' := by
        intro a b
        apply Subtype.ext
        funext N
        exact map_mul (q N) a b
      continuous_toFun := continuous_induced_rng.mpr
        (continuous_pi fun N ↦ (q N).continuous) }
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor Q
  let power : Multiplicative profiniteIntegerLimit →ₜ* P :=
    { e.symm.toMonoidHom.comp r.toMonoidHom with
      continuous_toFun := e.symm.continuous.comp r.continuous }
  have hp (m : ℤ) : power (profiniteIntegerInt m) = h ^ m := by
    apply e.injective
    change e (e.symm (r (profiniteIntegerInt m))) = e (h ^ m)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    funext N
    change q N (profiniteIntegerInt m) = QuotientGroup.mk (h ^ m)
    rw [hq N m]
    exact (map_zpow (QuotientGroup.mk' N.toSubgroup) h m).symm
  refine ⟨power, hp, ?_, ?_⟩
  · have he : power '' Set.range
        (fun m : ℤ ↦ (profiniteIntegerInt m : Multiplicative profiniteIntegerLimit)) =
        Set.range (fun m : ℤ ↦ h ^ m) := by
      rw [← Set.range_comp]
      congr 1
      funext m
      exact hp m
    apply Set.Subset.antisymm
    · have hc : Continuous (fun a ↦ power a) := power.continuous
      have hi := hc.range_subset_closure_image_dense integer_dense
      rw [he] at hi
      exact hi
    · apply closure_minimal _ power.continuous.isClosedMap.isClosed_range
      rintro _ ⟨m, rfl⟩
      exact ⟨profiniteIntegerInt m, hp m⟩
  · intro q' hq'
    apply DFunLike.ext'
    apply integer_dense.equalizer q'.continuous power.continuous
    funext m
    exact (hq' m).trans (hp m).symm

end
