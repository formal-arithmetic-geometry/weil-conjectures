/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkExact
public import WeilConjectures.LinearAlgebra.TraceLongExactSequence
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.CohomologyShift
public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.TraceFunction

/-!
# Additivity of the two sides of the Grothendieck–Lefschetz formula

For a Weil complex `K` on a separated `k₀`-scheme `X` of finite type, both sides of the
Grothendieck–Lefschetz trace formula,

* the global side `∑ᵢ (-1)ⁱ Tr(Fᵐ | H_cⁱ(X ⊗ k̄, K))`, and
* the local side, the trace function `t_K(y) = ∑ⱼ (-1)ʲ Tr(F_y | 𝓗ʲ(K)_ȳ)`,

are additive in distinguished triangles: both come from long exact sequences of finite-dimensional
spaces with compatible Frobenius endomorphisms (the long exact sequence of compactly supported
cohomology, resp. the stalks of the long exact sequence of cohomology sheaves), along which the
alternating sum of traces is additive
(`LinearMap.sum_negOnePow_smul_trace_sub_trace_sub_trace_eq_zero`). The global side moreover
changes by `(-1)ᵃ` under the shift `[a]` and is invariant under isomorphisms.

## Main results

- `LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact`: additivity of alternating sums of
  traces along a bounded cohomological long exact sequence.
- `AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq_add_of_distTriang`:
  the global side is additive in distinguished triangles.
- `AlgebraicGeometry.WeilComplex.traceFunction_eq_add_of_distTriang`: the trace function is
  additive in distinguished triangles.
- `AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_shift`: the global side
  of `K[a]` is `(-1)ᵃ` times that of `K`.
- `AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_congr`: the global side
  is invariant under isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated
open scoped Pointwise

namespace LinearMap

variable {K : Type*} [Field K]

/-- An alternating sum of traces over `ℤ`, supported on a finite set `s`, is the corresponding
finite sum over `-s` with the indices negated. -/
theorem finsum_negOnePow_smul_trace_eq_sum_neg (D : ℤ → Type*) [∀ n, AddCommGroup (D n)]
    [∀ n, Module K (D n)] [∀ n, FiniteDimensional K (D n)] (d : ∀ n, D n →ₗ[K] D n)
    (s : Finset ℤ) (hD : ∀ n ∉ s, Subsingleton (D n)) :
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • trace K (D n) (d n) =
      ∑ n ∈ -s, (n.negOnePow : ℤ) • trace K (D (-n)) (d (-n)) := by
  rw [← finsum_comp_equiv (Equiv.neg ℤ)]
  refine (finsum_eq_sum_of_support_subset _ fun n hn ↦ ?_).trans
    (Finset.sum_congr rfl fun n _ ↦ by rw [Equiv.neg_apply, Int.negOnePow_neg])
  rw [Finset.mem_coe, Finset.mem_neg']
  by_contra h
  have := hD _ h
  refine hn ?_
  beta_reduce
  rw [Equiv.neg_apply, trace_eq_zero_of_subsingleton, smul_zero]

variable (A B C : ℤ → Type*) [∀ n, AddCommGroup (A n)]
  [∀ n, Module K (A n)] [∀ n, FiniteDimensional K (A n)] [∀ n, AddCommGroup (B n)]
  [∀ n, Module K (B n)] [∀ n, FiniteDimensional K (B n)] [∀ n, AddCommGroup (C n)]
  [∀ n, Module K (C n)] [∀ n, FiniteDimensional K (C n)]

/-- **Alternating sums of traces along a cohomological long exact sequence.** Let
`f n : A n → B n`, `g n : B n → C n` and `δ n n' : C n → A n'` (for `n + 1 = n'`) form an exact
sequence `⋯ → A n → B n → C n → A (n + 1) → ⋯` of finite-dimensional vector spaces, zero outside a
finite set of indices, and let `a n`, `b n`, `c n` be endomorphisms compatible with the maps. Then
`∑ₙ (-1)ⁿ tr (b n) = ∑ₙ (-1)ⁿ tr (a n) + ∑ₙ (-1)ⁿ tr (c n)`. -/
theorem finsum_negOnePow_smul_trace_eq_add_of_exact
    (f : ∀ n, A n →ₗ[K] B n) (g : ∀ n, B n →ₗ[K] C n)
    (δ : ∀ n n', n + 1 = n' → C n →ₗ[K] A n')
    (hfg : ∀ n, Function.Exact (f n) (g n))
    (hgδ : ∀ n n' (h : n + 1 = n'), Function.Exact (g n) (δ n n' h))
    (hδf : ∀ n n' (h : n + 1 = n'), Function.Exact (δ n n' h) (f n'))
    (a : ∀ n, A n →ₗ[K] A n) (b : ∀ n, B n →ₗ[K] B n) (c : ∀ n, C n →ₗ[K] C n)
    (ha : ∀ n, b n ∘ₗ f n = f n ∘ₗ a n) (hb : ∀ n, c n ∘ₗ g n = g n ∘ₗ b n)
    (hc : ∀ n n' (h : n + 1 = n'), a n' ∘ₗ δ n n' h = δ n n' h ∘ₗ c n) (s : Finset ℤ)
    (hA : ∀ n ∉ s, Subsingleton (A n)) (hB : ∀ n ∉ s, Subsingleton (B n))
    (hC : ∀ n ∉ s, Subsingleton (C n)) :
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • trace K (B n) (b n) =
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • trace K (A n) (a n) +
        ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • trace K (C n) (c n) := by
  have key := sum_negOnePow_smul_trace_sub_trace_sub_trace_eq_zero (K := K)
    (fun n ↦ A (-n)) (fun n ↦ B (-n)) (fun n ↦ C (-n)) (fun n ↦ f (-n)) (fun n ↦ g (-n))
    (fun n ↦ δ (-n) (-(n - 1)) (by omega)) (fun n ↦ hfg (-n)) (fun n ↦ hgδ _ _ _)
    (fun n ↦ hδf _ _ _) (fun n ↦ a (-n)) (fun n ↦ b (-n)) (fun n ↦ c (-n)) (fun n ↦ ha (-n))
    (fun n ↦ hb (-n)) (fun n ↦ hc _ _ _) (-s)
    (fun n hn ↦ hA _ (by rwa [Finset.mem_neg'] at hn))
    (fun n hn ↦ hC _ (by rwa [Finset.mem_neg'] at hn))
  rw [finsum_negOnePow_smul_trace_eq_sum_neg A a s hA,
    finsum_negOnePow_smul_trace_eq_sum_neg B b s hB,
    finsum_negOnePow_smul_trace_eq_sum_neg C c s hC, ← Finset.sum_add_distrib, ← sub_eq_zero,
    ← Finset.sum_sub_distrib, ← key]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [smul_sub, smul_sub, sub_sub]

end LinearMap

namespace FrobeniusModule

variable {K : Type*} [Field K]

/-- A linear map between Frobenius modules commuting with the Frobenius commutes with its
powers. -/
theorem frobeniusEnd_pow_comp {M N : FrobeniusModule K} (f : M.carrier →ₗ[K] N.carrier)
    (hf : ∀ x, f (M.frobenius x) = N.frobenius (f x)) (m : ℕ) :
    (N.frobeniusEnd ^ m) ∘ₗ f = f ∘ₗ M.frobeniusEnd ^ m :=
  Module.End.commute_pow_left_of_commute (LinearMap.ext fun x ↦ (hf x).symm) m

end FrobeniusModule

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section Global

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The compactly supported cohomology of a Weil complex vanishes outside a finite set of
degrees. -/
theorem exists_finset_subsingleton_compactlySupportedCohomology (K : WeilComplex k₀ l X) :
    ∃ s : Finset ℤ, ∀ r ∉ s, Subsingleton (K.compactlySupportedCohomology r).carrier := by
  obtain ⟨a, b, h⟩ := exists_subsingleton_compactlySupportedCohomology K
  refine ⟨Finset.Icc a b, fun r hr ↦ h r ?_⟩
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
  exact hr

/-- **Additivity of the global side of the Grothendieck–Lefschetz formula.** For a distinguished
triangle `K₁ → K₂ → K₃ → K₁[1]` of Weil complexes, the alternating sum of the traces of `Fᵐ` on
compactly supported cohomology is additive, by the long exact sequence of compactly supported
cohomology. -/
theorem finsum_trace_compactlySupportedCohomology_eq_add_of_distTriang
    (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _) (m : ℕ) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((T.obj₂.compactlySupportedCohomology i).frobeniusEnd ^ m) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((T.obj₁.compactlySupportedCohomology i).frobeniusEnd ^ m) +
        ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((T.obj₃.compactlySupportedCohomology i).frobeniusEnd ^ m) := by
  obtain ⟨s₁, h₁⟩ := exists_finset_subsingleton_compactlySupportedCohomology T.obj₁
  obtain ⟨s₂, h₂⟩ := exists_finset_subsingleton_compactlySupportedCohomology T.obj₂
  obtain ⟨s₃, h₃⟩ := exists_finset_subsingleton_compactlySupportedCohomology T.obj₃
  exact LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact
    (fun i ↦ (T.obj₁.compactlySupportedCohomology i).carrier)
    (fun i ↦ (T.obj₂.compactlySupportedCohomology i).carrier)
    (fun i ↦ (T.obj₃.compactlySupportedCohomology i).carrier)
    (fun i ↦ compactlySupportedCohomologyMap T.mor₁ i)
    (fun i ↦ compactlySupportedCohomologyMap T.mor₂ i)
    (compactlySupportedCohomologyδ T)
    (fun i ↦ exact_compactlySupportedCohomologyMap T i hT)
    (fun i i' h ↦ exact_compactlySupportedCohomologyδ_left T i i' h hT)
    (fun i i' h ↦ exact_compactlySupportedCohomologyδ_right T i i' h hT)
    _ _ _
    (fun i ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (compactlySupportedCohomologyMap_frobenius T.mor₁ i) m)
    (fun i ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (compactlySupportedCohomologyMap_frobenius T.mor₂ i) m)
    (fun i i' h ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (compactlySupportedCohomologyδ_frobenius T i i' h) m)
    (s₁ ∪ s₂ ∪ s₃)
    (fun i hi ↦ h₁ i fun h ↦ hi (by simp [h]))
    (fun i hi ↦ h₂ i fun h ↦ hi (by simp [h]))
    (fun i hi ↦ h₃ i fun h ↦ hi (by simp [h]))

/-- **The global side of the Grothendieck–Lefschetz formula under shifts.** The alternating sum
of the traces of `Fᵐ` on the compactly supported cohomology of `K[a]` is `(-1)ᵃ` times that of
`K`, since `H_cⁱ(K[a]) ≅ H_c^{a+i}(K)`. -/
theorem finsum_trace_compactlySupportedCohomology_shift (K : WeilComplex k₀ l X) (a : ℤ)
    (m : ℕ) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        (((K⟦a⟧).compactlySupportedCohomology i).frobeniusEnd ^ m) =
      (a.negOnePow : ℤ) • ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ m) := by
  conv_rhs => rw [← finsum_comp_equiv (Equiv.addLeft a)]
  rw [smul_finsum]
  refine finsum_congr fun i ↦ ?_
  rw [← (compactlySupportedCohomologyShiftEquiv K a i (Equiv.addLeft a i)
    rfl).trace_frobeniusEnd_pow, smul_smul, ← Units.val_mul, Equiv.coe_addLeft,
    ← Int.negOnePow_add, ← add_assoc, ← two_mul, Int.negOnePow_add, Int.negOnePow_two_mul,
    one_mul]

/-- **The global side of the Grothendieck–Lefschetz formula is invariant under isomorphisms.** -/
theorem finsum_trace_compactlySupportedCohomology_congr {K L : WeilComplex k₀ l X} (e : K ≅ L)
    (m : ℕ) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ m) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((L.compactlySupportedCohomology i).frobeniusEnd ^ m) :=
  finsum_congr fun i ↦ by
    rw [(compactlySupportedCohomologyEquivOfIso e i).trace_frobeniusEnd_pow]

end Global

section Local

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- For a distinguished triangle `K₁ → K₂ → K₃ → K₁[1]` of Weil complexes and a closed point `x`,
the alternating sum over `j` of the traces of a power of the local Frobenius on the stalks
`𝓗ʲ(Kᵢ)_x̄` is additive, by the stalks of the long exact sequence of cohomology sheaves. -/
theorem finsum_trace_stalk_homologySheaf_eq_add_of_distTriang
    (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _) (x : X.finitePoints) (p : ℕ) :
    ∑ᶠ j : ℤ, (j.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((((homologySheaf j).obj T.obj₂).stalk x).frobeniusEnd ^ p) =
      ∑ᶠ j : ℤ, (j.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((((homologySheaf j).obj T.obj₁).stalk x).frobeniusEnd ^ p) +
        ∑ᶠ j : ℤ, (j.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((((homologySheaf j).obj T.obj₃).stalk x).frobeniusEnd ^ p) := by
  obtain ⟨s₁, h₁⟩ := T.obj₁.exists_finset_isZero_homologySheaf
  obtain ⟨s₂, h₂⟩ := T.obj₂.exists_finset_isZero_homologySheaf
  obtain ⟨s₃, h₃⟩ := T.obj₃.exists_finset_isZero_homologySheaf
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x
  exact LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact
    (fun j ↦ (((homologySheaf j).obj T.obj₁).stalk x).carrier)
    (fun j ↦ (((homologySheaf j).obj T.obj₂).stalk x).carrier)
    (fun j ↦ (((homologySheaf j).obj T.obj₃).stalk x).carrier)
    (fun j ↦ WeilSheaf.stalkAtMap _ _ hs ((homologySheaf j).map T.mor₁))
    (fun j ↦ WeilSheaf.stalkAtMap _ _ hs ((homologySheaf j).map T.mor₂))
    (fun j j' h ↦ WeilSheaf.stalkAtMap _ _ hs (homologySheafδ T j j' h))
    (fun j ↦ LinearMap.exact_iff.2 (WeilSheaf.range_stalkAtMap_eq_ker
      (homologySheaf_exact₂ T j hT) _ _ hs).symm)
    (fun j j' h ↦ LinearMap.exact_iff.2 (WeilSheaf.range_stalkAtMap_eq_ker
      (homologySheaf_exact₃ T j j' hT h) _ _ hs).symm)
    (fun j j' h ↦ LinearMap.exact_iff.2 (WeilSheaf.range_stalkAtMap_eq_ker
      (homologySheaf_exact₁ T j j' hT h) _ _ hs).symm)
    _ _ _
    (fun j ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (WeilSheaf.stalkAtMap_frobenius _ _ hs ((homologySheaf j).map T.mor₁)) p)
    (fun j ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (WeilSheaf.stalkAtMap_frobenius _ _ hs ((homologySheaf j).map T.mor₂)) p)
    (fun j j' h ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (WeilSheaf.stalkAtMap_frobenius _ _ hs (homologySheafδ T j j' h)) p)
    (s₁ ∪ s₂ ∪ s₃)
    (fun j hj ↦ WeilSheaf.subsingleton_stalk_of_isZero (h₁ j fun h ↦ hj (by simp [h])) x)
    (fun j hj ↦ WeilSheaf.subsingleton_stalk_of_isZero (h₂ j fun h ↦ hj (by simp [h])) x)
    (fun j hj ↦ WeilSheaf.subsingleton_stalk_of_isZero (h₃ j fun h ↦ hj (by simp [h])) x)

/-- **Additivity of the trace function in distinguished triangles.** For a distinguished triangle
`K₁ → K₂ → K₃ → K₁[1]` of Weil complexes, `t_{K₂} = t_{K₁} + t_{K₃}`. -/
theorem traceFunction_eq_add_of_distTriang (T : Triangle (WeilComplex k₀ l X))
    (hT : T ∈ distTriang _) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    T.obj₂.traceFunction n y = T.obj₁.traceFunction n y + T.obj₃.traceFunction n y := by
  simp only [traceFunction, WeilSheaf.traceFunction_eq_trace]
  exact finsum_trace_stalk_homologySheaf_eq_add_of_distTriang T hT _ _

end Local

end AlgebraicGeometry.WeilComplex
