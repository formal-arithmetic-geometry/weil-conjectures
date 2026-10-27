module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Topology.Defs.Induced

/-! # Reconstruction from shrinking open additive subgroups

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.2(1),
continuous-function inverse-limit identity and its general complete metric-group argument
(blueprint: lem-sfb-complete-metric-group-quotients).

The index `n : ℕ` denotes the paper's index `n + 1`. Quotients carry Mathlib's quotient
topology, which is discrete for an open additive subgroup. The compatible subgroup carries
the subtype topology of the product of these discrete quotients.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace CompleteMetricGroupQuotients

open Filter Topology

/-- The canonical transition between adjacent open-subgroup quotients.
Source: Bhatt--Scholze 6.8.2(1), general metric-group reconstruction
(blueprint: lem-sfb-complete-metric-group-quotients). -/
def transition {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    (U : ℕ → OpenAddSubgroup G)
    (hU : ∀ n : ℕ, (U (n + 1)).toAddSubgroup ≤ (U n).toAddSubgroup) (n : ℕ) :
    G ⧸ (U (n + 1)).toAddSubgroup →+ G ⧸ (U n).toAddSubgroup :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id G) (hU n)

/-- Compatible quotient families, with inherited coordinatewise group operations and the
subtype topology of the product. Source: Bhatt--Scholze 6.8.2(1), general reconstruction
(blueprint: lem-sfb-complete-metric-group-quotients). -/
def compatibleSubgroup {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    (U : ℕ → OpenAddSubgroup G)
    (hU : ∀ n : ℕ, (U (n + 1)).toAddSubgroup ≤ (U n).toAddSubgroup) :
    AddSubgroup (∀ n : ℕ, G ⧸ (U n).toAddSubgroup) :=
  ⨅ n : ℕ, AddMonoidHom.eqLocus
    ((transition U hU n).comp (Pi.evalAddMonoidHom _ (n + 1)))
    (Pi.evalAddMonoidHom _ n)

/-- Compatible continuous quotient-valued maps: evaluation at each point belongs to the
compatible subgroup. Operations are pointwise. Source: Bhatt--Scholze 6.8.2(1), general
continuous-function reconstruction (blueprint: lem-sfb-complete-metric-group-quotients). -/
def continuousCompatibleSubgroup {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (U : ℕ → OpenAddSubgroup G)
    (hU : ∀ n : ℕ, (U (n + 1)).toAddSubgroup ≤ (U n).toAddSubgroup)
    (S : Type v) [TopologicalSpace S] :
    AddSubgroup (∀ n : ℕ, C(S, G ⧸ (U n).toAddSubgroup)) :=
  ⨅ s : S, (compatibleSubgroup U hU).comap
    (AddMonoidHom.pi fun n : ℕ =>
      ((Pi.evalAddMonoidHom _ s).comp ContinuousMap.coeFnAddMonoidHom).comp
        (Pi.evalAddMonoidHom (fun k : ℕ => C(S, G ⧸ (U k).toAddSubgroup)) n))

private theorem mem_compatible_iff {G : Type u} [AddCommGroup G]
    [TopologicalSpace G] (U : ℕ → OpenAddSubgroup G)
    (hU : ∀ n : ℕ, (U (n + 1)).toAddSubgroup ≤ (U n).toAddSubgroup)
    (a : ∀ n : ℕ, G ⧸ (U n).toAddSubgroup) :
    a ∈ compatibleSubgroup U hU ↔ ∀ n, transition U hU n (a (n + 1)) = a n := by
  simp only [compatibleSubgroup, AddSubgroup.mem_iInf]
  rfl

private theorem mem_continuousCompatible_iff {G : Type u} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] (U : ℕ → OpenAddSubgroup G)
    (hU : ∀ n : ℕ, (U (n + 1)).toAddSubgroup ≤ (U n).toAddSubgroup)
    {S : Type v} [TopologicalSpace S]
    (a : ∀ n : ℕ, C(S, G ⧸ (U n).toAddSubgroup)) :
    a ∈ continuousCompatibleSubgroup U hU S ↔
      ∀ s : S, (fun n ↦ a n s) ∈ compatibleSubgroup U hU := by
  simp only [continuousCompatibleSubgroup, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

private def quotientHom {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    (U : ℕ → OpenAddSubgroup G)
    (hU : ∀ n : ℕ, (U (n + 1)).toAddSubgroup ≤ (U n).toAddSubgroup) :
    G →+ compatibleSubgroup U hU where
  toFun x := ⟨fun n ↦ QuotientAddGroup.mk' (U n).toAddSubgroup x,
    (mem_compatible_iff U hU _).mpr (fun _ ↦ rfl)⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero _
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add _ x y

private noncomputable def functionEquiv {G : Type u} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] (U : ℕ → OpenAddSubgroup G)
    (hU : ∀ n : ℕ, (U (n + 1)).toAddSubgroup ≤ (U n).toAddSubgroup)
    (e : G ≃ₜ+ compatibleSubgroup U hU)
    (he : ∀ (x : G) (n : ℕ), (e x).val n = QuotientAddGroup.mk' (U n).toAddSubgroup x)
    (S : Type v) [TopologicalSpace S] :
    C(S, G) ≃+ continuousCompatibleSubgroup U hU S where
  toFun f := ⟨fun n ↦ ⟨fun s ↦ QuotientAddGroup.mk' (U n).toAddSubgroup (f s),
      QuotientAddGroup.continuous_mk.comp f.continuous⟩,
    (mem_continuousCompatible_iff U hU _).mpr fun s ↦ by
      exact (quotientHom U hU (f s)).property⟩
  invFun a := ⟨fun s ↦ e.symm ⟨fun n ↦ a.val n s,
      (mem_continuousCompatible_iff U hU _).mp a.property s⟩,
    e.symm.continuous.comp
      ((continuous_pi fun n ↦ (a.val n).continuous).subtype_mk _)⟩
  left_inv f := by
    apply ContinuousMap.ext
    intro s
    apply e.injective
    change e (e.symm _) = e (f s)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    funext n
    exact (he (f s) n).symm
  right_inv a := by
    apply Subtype.ext
    funext n
    apply ContinuousMap.ext
    intro s
    exact (he _ n).symm.trans
      (congrArg (fun b : compatibleSubgroup U hU ↦ b.val n) (e.apply_symm_apply _))
  map_add' f g := by
    apply Subtype.ext
    funext n
    apply ContinuousMap.ext
    intro s
    exact (QuotientAddGroup.mk' (U n).toAddSubgroup).map_add (f s) (g s)

/-- A complete translation-invariant metric group is its shrinking open-subgroup limit,
and continuous functions into it are compatible continuous quotient functions, naturally
under all precompositions and all quotient projections.
Source: Bhatt--Scholze 6.8.2(1), general metric-group reconstruction underlying its
continuous-function identity (blueprint: lem-sfb-complete-metric-group-quotients).

Proof:
1. Quotient transitions are additive, so their equalizers form the displayed subgroup.
   Quotient projections are compatible and additive, giving the canonical map into it.
2. Equal coordinates imply x-y belongs to every U_n. Shrinking and translation
   invariance force dist x y < epsilon for every positive epsilon, hence x = y.
3. Choose representatives x_n of a compatible family. Iterating adjacent compatibility
   shows x_m-x_n belongs to U_n whenever m is at least n.
4. For m,k at least N, x_m-x_k belongs to U_N. Shrinking and translation invariance
   make the representatives Cauchy. Completeness supplies their limit x.
5. Openness of U_n gives a ball about zero inside it. Convergence and step 3 imply
   x-x_n belongs to U_n. Thus x realizes the family, uniquely by step 2.
6. Each coset of U_n is open by translation invariance. The quotient is discrete and
   each quotient projection is continuous. Product and subtype continuity make the
   canonical map continuous (def-kun-subspace-topology).
7. For epsilon > 0 choose a shrinking U_N. The open cylinder fixing coordinate N
   maps under the inverse into the epsilon ball. Thus the inverse is continuous.
8. A compatible family of continuous quotient functions defines a continuous map to
   the product subtype, by coordinatewise continuity. Compose with the inverse of
   step 7. This inverts the quotient-function map for every space, including empty ones.
9. Continuity of addition and negation gives the pointwise groups. Quotient additivity
   makes the bijections additive. Associativity of composition gives the displayed
   precomposition identities; uniqueness gives these identities for the inverses too.
No compactness or finiteness enters any step. -/
theorem reconstruction {G : Type u} [AddCommGroup G] [MetricSpace G]
    [CompleteSpace G] [IsTopologicalAddGroup G]
    (htranslation : ∀ x y z : G, dist (x + z) (y + z) = dist x y)
    (U : ℕ → OpenAddSubgroup G)
    (hU : ∀ n : ℕ, (U (n + 1)).toAddSubgroup ≤ (U n).toAddSubgroup)
    (hshrink : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ x : G, x ∈ U N → dist x 0 < ε)
    (S : Type v) [TopologicalSpace S] (S' : Type w) [TopologicalSpace S'] :
    ∃ e : G ≃ₜ+ compatibleSubgroup U hU,
      (∀ (x : G) (n : ℕ), (e x).val n = QuotientAddGroup.mk' (U n).toAddSubgroup x) ∧
      ∃ E : C(S, G) ≃+ continuousCompatibleSubgroup U hU S,
        ∃ E' : C(S', G) ≃+ continuousCompatibleSubgroup U hU S',
          (∀ (f : C(S, G)) (n : ℕ) (s : S),
            (E f).val n s = QuotientAddGroup.mk' (U n).toAddSubgroup (f s)) ∧
          (∀ (f : C(S', G)) (n : ℕ) (s : S'),
            (E' f).val n s = QuotientAddGroup.mk' (U n).toAddSubgroup (f s)) ∧
          (∀ (a : C(S', S)) (f : C(S, G)) (n : ℕ),
            (E' (f.comp a)).val n = ((E f).val n).comp a) := by
  classical
  let q := quotientHom U hU
  have hdist (x y : G) : dist (x - y) 0 = dist x y := by
    simpa only [sub_add_cancel, zero_add] using (htranslation (x - y) 0 y).symm
  have hinj : Function.Injective q := by
    intro x y hxy
    apply eq_of_dist_eq_zero
    apply le_antisymm _ dist_nonneg
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨N, hN⟩ := hshrink ε hε
    have hcoord := congrArg (fun a : compatibleSubgroup U hU ↦ a.val N) hxy
    have hmem : x - y ∈ (U N).toAddSubgroup :=
      QuotientAddGroup.eq_iff_sub_mem.mp hcoord
    simpa only [zero_add, hdist] using hN (x - y) hmem
  have hsurj : Function.Surjective q := by
    intro a
    choose x hx using fun n ↦ QuotientAddGroup.mk'_surjective (U n).toAddSubgroup (a.val n)
    have ha := (mem_compatible_iff U hU _).mp a.property
    have hmono : Antitone (fun n ↦ (U n).toAddSubgroup) := antitone_nat_of_succ_le hU
    have hstep (n : ℕ) : x (n + 1) - x n ∈ (U n).toAddSubgroup := by
      apply QuotientAddGroup.eq_iff_sub_mem.mp
      calc
        QuotientAddGroup.mk' (U n).toAddSubgroup (x (n + 1)) =
            transition U hU n (a.val (n + 1)) := by rw [← hx]; rfl
        _ = a.val n := ha n
        _ = QuotientAddGroup.mk' (U n).toAddSubgroup (x n) := (hx n).symm
    have htail (n m : ℕ) (hnm : n ≤ m) : x m - x n ∈ (U n).toAddSubgroup := by
      induction m, hnm using Nat.le_induction with
      | base => simp
      | succ m hnm ih =>
        have hh := (U n).sub_mem (hmono hnm (hstep m)) ((U n).neg_mem ih)
        simpa only [sub_neg_eq_add, sub_add_sub_cancel] using hh
    have hc : CauchySeq x := by
      apply Metric.cauchySeq_iff.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := hshrink ε hε
      refine ⟨N, fun m hm k hk ↦ ?_⟩
      have hh := (U N).sub_mem (htail N m hm) (htail N k hk)
      have hm : x m - x k ∈ U N := by
        simpa only [sub_sub_sub_cancel_right, OpenAddSubgroup.mem_toAddSubgroup] using hh
      simpa only [hdist] using hN (x m - x k) hm
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨z, ?_⟩
    apply Subtype.ext
    funext n
    have hqn : Continuous (fun y : G ↦ QuotientAddGroup.mk' (U n).toAddSubgroup y) :=
      QuotientAddGroup.continuous_mk
    have hevent : ∀ᶠ m in Filter.atTop,
        QuotientAddGroup.mk' (U n).toAddSubgroup (x m) = a.val n := by
      filter_upwards [Filter.eventually_ge_atTop n] with m hm
      exact (QuotientAddGroup.eq_iff_sub_mem.mpr (htail n m hm)).trans (hx n)
    exact tendsto_nhds_unique_of_eventuallyEq (hqn.tendsto z |>.comp hz)
      tendsto_const_nhds hevent
  let e₀ : G ≃+ compatibleSubgroup U hU := AddEquiv.ofBijective q ⟨hinj, hsurj⟩
  have he₀ (x : G) (n : ℕ) :
      (e₀ x).val n = QuotientAddGroup.mk' (U n).toAddSubgroup x := rfl
  have hcont : Continuous e₀ := by
    exact (continuous_pi fun _ ↦ QuotientAddGroup.continuous_mk).subtype_mk _
  have hinv : Continuous e₀.symm := by
    apply Metric.continuous_iff'.mpr
    intro a ε hε
    obtain ⟨N, hN⟩ := hshrink ε hε
    have hcoord : Continuous (fun b : compatibleSubgroup U hU ↦ b.val N) :=
      (continuous_apply N).comp continuous_subtype_val
    have hevent : ∀ᶠ b in 𝓝 a, b.val N = a.val N :=
      hcoord.continuousAt.eventually ((isOpen_discrete _).mem_nhds (Set.mem_singleton _))
    filter_upwards [hevent] with b hb
    have hsame : QuotientAddGroup.mk' (U N).toAddSubgroup (e₀.symm b) =
        QuotientAddGroup.mk' (U N).toAddSubgroup (e₀.symm a) := by
      rw [← he₀, ← he₀, e₀.apply_symm_apply, e₀.apply_symm_apply]
      exact hb
    simpa only [hdist] using hN _ (QuotientAddGroup.eq_iff_sub_mem.mp hsame)
  let e : G ≃ₜ+ compatibleSubgroup U hU :=
    { e₀ with continuous_toFun := hcont, continuous_invFun := hinv }
  refine ⟨e, he₀, functionEquiv U hU e he₀ S, functionEquiv U hU e he₀ S', ?_, ?_, ?_⟩
  · intros
    rfl
  · intros
    rfl
  · intro a f n
    apply ContinuousMap.ext
    intro s
    rfl

end CompleteMetricGroupQuotients
