/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.Analysis.FiniteQuotientContractiveAverage
import Sheaf.Analysis.InvariantAverageCochainIdentity
import Mathlib.Tactic.Ring

/-! # Parametrized scalar cocycle averaging primitives

Source: main-20261015 six-functors direct-image stability proof, paragraph (3),
agent-formulated analytic expansion, exact analytic reference WANTED
(blueprint: lem-sfb-scalar-cochain-averaging-primitives).

The differential is the trivial-action inhomogeneous differential in section coordinates.
The finite primitive is specified by its finite sum. The complete primitive is specified
by its last-variable integral, for any normalized integral supplied by the dependency.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

namespace WeilConjectures

/-- The section-coordinate differential on parametrized scalar cochains with trivial
coefficients. `Fin.contractNth` includes the final face, which drops the last coordinate.
In degree zero the two terms cancel, giving d⁰ = 0. This is the displayed differential
of the agent analytic expansion of paragraph (3) of the direct-image stability proof
(blueprint: lem-sfb-scalar-cochain-averaging-primitives). -/
def scalarCochainDifferential {P : Type w} {G : Type u} {V : Type v}
    [Group G] [Ring V] (r : ℕ) (c : P × (Fin r → G) → V)
    (s : P) (g : Fin (r + 1) → G) : V :=
  c (s, fun j ↦ g j.succ) +
    ∑ j : Fin (r + 1), (-1 : V) ^ (j.val + 1) *
      c (s, Fin.contractNth j (· * ·) g)

/-- Appending one group argument gives a continuous last-variable slice of a cochain.
Source: paragraph (3), signed last-variable averaging formula
(blueprint: lem-sfb-scalar-cochain-averaging-primitives). -/
def scalarCochainLastSlice {P : Type w} {G : Type u} {V : Type v}
    [TopologicalSpace P] [TopologicalSpace G] [TopologicalSpace V]
    (n : ℕ) (c : C(P × (Fin (n + 1) → G), V)) (s : P) (g : Fin n → G) : C(G, V) :=
  c.comp ⟨fun h ↦ (s, Fin.snoc g h), continuous_const.prodMk
    (continuous_pi fun j ↦ by
      unfold Fin.snoc
      split
      · exact continuous_const
      · exact continuous_id)⟩

private def scalarSliceFamily {P : Type w} {G : Type u} {V : Type v}
    [TopologicalSpace P] [TopologicalSpace G] [TopologicalSpace V]
    (n : ℕ) (c : C(P × (Fin (n + 1) → G), V)) :
    C(P × (Fin n → G), C(G, V)) :=
  (c.comp ⟨fun x ↦ (x.1.1, Fin.snoc x.1.2 x.2),
    (continuous_fst.fst).prodMk (continuous_pi fun j ↦ by
      unfold Fin.snoc
      split
      · exact (continuous_apply _).comp continuous_fst.snd
      · exact continuous_snd)⟩).curry

private def scalarAverageMap {P : Type w} {G : Type u} {V : Type v}
    [TopologicalSpace P] [TopologicalSpace G] [CompactSpace G] [NormedField V]
    (I : C(G, V) →L[V] V) (n : ℕ) :
    C(P × (Fin (n + 1) → G), V) →ₗ[V] C(P × (Fin n → G), V) where
  toFun c := (-1 : V) ^ (n + 1) •
    ((⟨I, I.continuous⟩ : C(C(G, V), V)).comp (scalarSliceFamily n c))
  map_add' c d := by
    ext x
    change (-1 : V) ^ (n + 1) * I _ =
      (-1 : V) ^ (n + 1) * I _ + (-1 : V) ^ (n + 1) * I _
    rw [← mul_add, ← map_add]
    congr 2
  map_smul' a c := by
    ext x
    change (-1 : V) ^ (n + 1) * I _ = a * ((-1 : V) ^ (n + 1) * I _)
    have hs : scalarSliceFamily n (a • c) x = a • scalarSliceFamily n c x := by
      ext h
      rfl
    rw [hs, map_smul]
    simp only [smul_eq_mul]
    ring

private theorem scalarAverageMap_apply {P : Type w} {G : Type u} {V : Type v}
    [TopologicalSpace P] [TopologicalSpace G] [CompactSpace G] [NormedField V]
    (I : C(G, V) →L[V] V) (n : ℕ) (c : C(P × (Fin (n + 1) → G), V))
    (s : P) (g : Fin n → G) :
    scalarAverageMap I n c (s, g) =
      (-1 : V) ^ (n + 1) * I (scalarCochainLastSlice n c s g) := by
  rfl

private def scalarContinuousEval {G : Type u} {V : Type v}
    [TopologicalSpace G] [NormedField V] : C(G, V) →ₗ[V] (G → V) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Finite-quotient averaging requires no completeness. Complete coefficients admit
contractive linear averaging in every degree, continuous in every profinite parameter,
linear over its continuous scalar functions, and natural under parameter changes.
The last-variable formula specifies the map also for a point parameter. Its cocycle
identity includes degree one; its norm bounds include empty parameter spaces.

Source: paragraph (3) of the main-20261015 direct-image stability proof, agent analytic
expansion, exact norm-topological reference WANTED
(blueprint: lem-sfb-scalar-cochain-averaging-primitives).

Proof plan:
1. Apply lem-sfb-finite-quotient-contractive-average to each last-variable slice.
   The descended cochain is continuous since its quotient is finite discrete: choose
   lifts of its finitely many group tuples and restrict the original continuous family.
   Its signed finite sum is continuous and factors through the same quotient. The
   ultrametric finite-average estimate gives the supremum bound without completeness.
2. For complete V use lem-sfb-prime-to-ell-complete-scalar-integral with B=V, K=G.
   Apply its parameter clause to P times G^n. Multiplication by (-1)^(n+1) gives
   the displayed maps. Slice evaluation proves V-linearity, C(P,V)-linearity and
   precomposition naturality; taking the supremum gives the contraction estimate.
3. In degree n+1 >= 2, average the cocycle equation in the last variable. Left
   invariance replaces the term with g_last*h by the untranslated slice, and
   normalization fixes the constant final term. The result is d(Tc)=(-1)^(n+1)c,
   so the stated signed primitive has differential c. The finite argument stays
   inside the common finite quotient throughout.
4. In degree one the averaged equation c(h)-c(gh)+c(g)=0 gives c(g)=0; hence
   d^0=0 gives the primitive identity. Empty P has just the zero continuous cochain,
   so every identity, continuity assertion, and bound still holds. -/
theorem scalar_cochain_averaging_primitives
    (ell : ℕ) [Fact ell.Prime]
    (V : Type v) [NormedField V]
    (iota : Padic ell →+* V) (hiota : Isometry iota)
    (hultra : ∀ x y : V, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (hbasis : ∀ W : Set G, IsOpen W → (1 : G) ∈ W →
      ∃ U : OpenNormalSubgroup G, (U : Set G) ⊆ W)
    (hprime : ∀ U : OpenNormalSubgroup G, Nat.Coprime (Nat.card (G ⧸ U.toSubgroup)) ell) :
    (∀ (n : ℕ) (P : Profinite.{w})
      (c : C(P × (Fin (n + 1) → G), V))
      (U : OpenNormalSubgroup G)
      (cbar : C(P × (Fin (n + 1) → G ⧸ U.toSubgroup), V)),
      (∀ (s : P) (g : Fin (n + 1) → G),
        c (s, g) = cbar (s, fun j ↦ QuotientGroup.mk (g j))) →
      (∀ (s : P) (g : Fin (n + 2) → G),
        scalarCochainDifferential (n + 1) c s g = 0) →
      ∃ (b : C(P × (Fin n → G), V))
        (bbar : C(P × (Fin n → G ⧸ U.toSubgroup), V)),
        (∀ (s : P) (g : Fin n → G ⧸ U.toSubgroup),
          bbar (s, g) = (-1 : V) ^ (n + 1) *
            (Nat.card (G ⧸ U.toSubgroup) : V)⁻¹ *
              ∑' h, cbar (s, Fin.snoc g h)) ∧
        (∀ (s : P) (g : Fin n → G),
          b (s, g) = bbar (s, fun j ↦ QuotientGroup.mk (g j))) ∧
        (∀ (s : P) (g : Fin (n + 1) → G),
          scalarCochainDifferential n b s g = c (s, g)) ∧
        ‖b‖ ≤ ‖c‖) ∧
    (∀ [CompleteSpace V] (I : C(G, V) →L[V] V),
      (∀ f : C(G, V), ‖I f‖ ≤ ‖f‖) → I 1 = 1 →
      (∀ (a : G) (f : C(G, V)),
        I (f.comp ⟨fun h ↦ a * h, continuous_const.mul continuous_id⟩) = I f ∧
        I (f.comp ⟨fun h ↦ h * a, continuous_id.mul continuous_const⟩) = I f) →
      (∀ (U : OpenNormalSubgroup G) (g : G ⧸ U.toSubgroup → V) (f : C(G, V)),
        (∀ h : G, f h = g (QuotientGroup.mk h)) →
        I f = (Nat.card (G ⧸ U.toSubgroup) : V)⁻¹ * ∑' q, g q) →
      ∃ H : (n : ℕ) → (P : Profinite.{w}) →
        C(P × (Fin (n + 1) → G), V) →ₗ[V] C(P × (Fin n → G), V),
        (∀ (n : ℕ) (P : Profinite.{w}) (c : C(P × (Fin (n + 1) → G), V))
          (s : P) (g : Fin n → G),
          H n P c (s, g) = (-1 : V) ^ (n + 1) * I (scalarCochainLastSlice n c s g)) ∧
        (∀ (n : ℕ) (P : Profinite.{w}) (c : C(P × (Fin (n + 1) → G), V)),
          ‖H n P c‖ ≤ ‖c‖) ∧
        (∀ (n : ℕ) (P : Profinite.{w}) (a : C(P, V))
          (c : C(P × (Fin (n + 1) → G), V)),
          H n P ((a.comp ContinuousMap.fst) * c) =
            (a.comp ContinuousMap.fst) * H n P c) ∧
        (∀ (n : ℕ) (P P' : Profinite.{w}) (a : C(P', P))
          (c : C(P × (Fin (n + 1) → G), V)),
          H n P' (c.comp (a.prodMap (ContinuousMap.id (Fin (n + 1) → G)))) =
            (H n P c).comp (a.prodMap (ContinuousMap.id (Fin n → G)))) ∧
        (∀ (n : ℕ) (P : Profinite.{w}) (c : C(P × (Fin (n + 1) → G), V)),
          (∀ (s : P) (g : Fin (n + 2) → G),
            scalarCochainDifferential (n + 1) c s g = 0) →
          ∀ (s : P) (g : Fin (n + 1) → G),
            scalarCochainDifferential n (H n P c) s g = c (s, g))) := by
  classical
  constructor
  · let : NormedAlgebra (Padic ell) V :=
      { iota.toAlgebra with
        norm_smul_le := fun a x ↦ by
          change ‖iota a * x‖ ≤ ‖a‖ * ‖x‖
          rw [norm_mul, hiota.norm_map_of_map_zero iota.map_zero] }
    obtain ⟨hquot, D, hD, hconst, A, hA, _hrefine, hnorm, hone, htrans⟩ :=
      ContinuousMap.exists_finiteQuotientContractiveAverage ell V hultra G hbasis hprime
    intro n P c U cbar hfactor hc
    let Q := G ⧸ U.toSubgroup
    let : Finite Q := (hquot U).1
    let : Fintype Q := Fintype.ofFinite Q
    let bbar : C(P × (Fin n → Q), V) :=
      (-1 : V) ^ (n + 1) • (Nat.card Q : V)⁻¹ •
        ∑ h : Q, cbar.comp ⟨fun x ↦ (x.1, Fin.snoc x.2 h),
          continuous_fst.prodMk (continuous_pi fun j ↦ by
            unfold Fin.snoc
            split
            · exact (continuous_apply _).comp continuous_snd
            · exact continuous_const)⟩
    let b : C(P × (Fin n → G), V) :=
      bbar.comp ⟨fun x ↦ (x.1, fun j ↦ QuotientGroup.mk (x.2 j)),
        continuous_fst.prodMk (continuous_pi fun j ↦
          QuotientGroup.continuous_mk.comp ((continuous_apply j).comp continuous_snd))⟩
    have hbbar (s : P) (g : Fin n → Q) :
        bbar (s, g) = (-1 : V) ^ (n + 1) * (Nat.card Q : V)⁻¹ *
          ∑' h : Q, cbar (s, Fin.snoc g h) := by
      simp [bbar, tsum_fintype, mul_assoc]
    have hslices (s : P) (g : Fin n → G) : scalarCochainLastSlice n c s g ∈ D := by
      apply (hD _).2
      refine ⟨U, fun h ↦ cbar (s, Fin.snoc (fun j ↦ QuotientGroup.mk (g j)) h), ?_⟩
      intro h
      change c (s, Fin.snoc g h) = _
      rw [hfactor]
      congr 2
      exact Fin.comp_snoc QuotientGroup.mk g h
    let t : P → (Fin n → G) → D :=
      fun s g ↦ ⟨scalarCochainLastSlice n c s g, hslices s g⟩
    have hval (s : P) (g : Fin n → G) :
        b (s, g) = (-1 : V) ^ (n + 1) * A (t s g) := by
      change bbar _ = _
      rw [hbbar]
      have havg := hA (t s g) U
        (fun h ↦ cbar (s, Fin.snoc (fun j ↦ QuotientGroup.mk (g j)) h))
        (fun h ↦ by
          change c (s, Fin.snoc g h) = _
          rw [hfactor]
          congr 2
          exact Fin.comp_snoc QuotientGroup.mk g h)
      rw [havg]
      simp [Q, tsum_fintype, finsum_eq_sum_of_fintype, mul_assoc]
    refine ⟨b, bbar, hbbar, (fun _ _ ↦ rfl), ?_, ?_⟩
    · let ev : D →ₗ[V] (G → V) := scalarContinuousEval.comp D.subtype
      have hev : Function.Injective ev := by
        intro f f' h
        apply Subtype.ext
        exact ContinuousMap.ext (congrFun h)
      have hleft : ∀ (a : G) (f : D), ∃ f' : D,
          ev f' = (fun h ↦ ev f (a * h)) ∧ A f' = A f := by
        intro a f
        obtain ⟨fL, fR, hL, _hR, hAL, _hAR⟩ := htrans a f
        exact ⟨fL, funext hL, hAL⟩
      have hunit : ev ⟨ContinuousMap.const G 1, hconst 1⟩ = 1 := rfl
      have hAunit := hone ⟨ContinuousMap.const G 1, hconst 1⟩ rfl
      intro s g
      have hid := invariant_average_cochain_identity ev hev A _ hunit hAunit
        hleft n c t (fun _ _ _ ↦ rfl) hc s g
      simpa only [scalarCochainDifferential, hval] using hid
    · apply (ContinuousMap.norm_le _ (norm_nonneg c)).2
      rintro ⟨s, g⟩
      rw [hval, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      apply (hnorm (t s g)).trans
      apply (ContinuousMap.norm_le _ (norm_nonneg c)).2
      intro h
      exact ContinuousMap.norm_coe_le_norm c (s, Fin.snoc g h)
  · intro _ I hnorm hone htrans _hfinite
    let H := fun (n : ℕ) (P : Profinite.{w}) ↦
      scalarAverageMap (P := P) I n
    refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
    · intro n P c s g
      simpa [H] using scalarAverageMap_apply I n c s g
    · intro n P c
      apply (ContinuousMap.norm_le _ (norm_nonneg c)).2
      rintro ⟨s, g⟩
      dsimp [H, scalarAverageMap, scalarSliceFamily]
      change ‖(-1 : V) ^ (n + 1) * I (scalarCochainLastSlice n c s g)‖ ≤ ‖c‖
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      apply (hnorm _).trans
      apply (ContinuousMap.norm_le _ (norm_nonneg c)).2
      intro h
      exact ContinuousMap.norm_coe_le_norm c (s, Fin.snoc g h)
    · intro n P a c
      ext ⟨s, g⟩
      change (-1 : V) ^ (n + 1) *
          I (scalarSliceFamily n ((a.comp ContinuousMap.fst) * c) (s, g)) =
        a s * ((-1 : V) ^ (n + 1) * I (scalarSliceFamily n c (s, g)))
      have hs : scalarSliceFamily n ((a.comp ContinuousMap.fst) * c) (s, g) =
          a s • scalarSliceFamily n c (s, g) := by
        ext h
        rfl
      rw [hs, map_smul]
      simp only [smul_eq_mul]
      ring
    · intro n P P' a c
      ext ⟨s, g⟩
      dsimp [H, scalarAverageMap, scalarSliceFamily]
      change (-1 : V) ^ (n + 1) * I _ = (-1 : V) ^ (n + 1) * I _
      congr 2
    · intro n P c hc s g
      have hleft : ∀ (a : G) (f : C(G, V)), ∃ f' : C(G, V),
          scalarContinuousEval f' = (fun h ↦ scalarContinuousEval f (a * h)) ∧
            I.toLinearMap f' = I.toLinearMap f := by
        intro a f
        exact ⟨f.comp ⟨fun h ↦ a * h, continuous_const.mul continuous_id⟩,
          rfl, (htrans a f).1⟩
      have hid := invariant_average_cochain_identity scalarContinuousEval
        (fun f f' h ↦ ContinuousMap.ext (congrFun h)) I.toLinearMap 1 rfl hone
        hleft n c (fun s g ↦ scalarCochainLastSlice n c s g)
        (fun _ _ _ ↦ rfl) hc s g
      change scalarCochainDifferential n (scalarAverageMap I n c) s g = c (s, g)
      simpa only [scalarCochainDifferential, scalarAverageMap_apply,
        ContinuousLinearMap.coe_coe] using hid

end WeilConjectures
