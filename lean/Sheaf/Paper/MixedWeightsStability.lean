/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.WeilSheaf.Triangle
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.Category
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import Sheaf.LinearAlgebra.FrobeniusPunctualBoundMixed
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact
import Sheaf.LinearAlgebra.FrobeniusModuleExtensionBounds

/-! # Stability of mixed upper weight bounds

Source: Weil-conjectures blueprint, sec-deligne-laumon-general/sk-d-dl-general-weights,
main-20261015, lemma lem-a1-mixed-direct-summand, order 3155
(blueprint: lem-a1-mixed-direct-summand).

## Main statements

- The imported sheaf `of_mono`, `of_epi`, `of_shortExact`, and `of_retract` give
  subobjects, quotients, extensions, and direct summands.
- `FrobeniusModule.mixedOfWeightsAtMost_stability`: the analogous assertions for the
  recorded finite stable-filtration definition of mixed Frobenius modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u₁ u₂ u₃ v

namespace FrobeniusModule

private theorem mixed_eigenvalue_bound
    (p a ell : ℕ) [Fact p.Prime] (ha : 1 ≤ a)
    [Fact ell.Prime] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra ℚ_[ell] Qlb] (hQ : IsAlgClosure ℚ_[ell] Qlb)
    (iota : Qlb ≃+* ℂ) (M : FrobeniusModule.{u₁, v} Qlb) (w : ℝ)
    (hM : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota M w) :
    M.HasWeightsAtMost iota.toRingHom (p ^ a) w := by
  obtain ⟨m, V, hzero, hwhole, hinc, hstable, hpure⟩ := hM
  have step : ∀ (j : ℕ) (hj : j ≤ m) (α : Qlb) (x : M.carrier),
      x ∈ V ⟨j, by omega⟩ → M.frobenius x = α • x → x ≠ 0 →
      ‖iota α‖ ≤ ((p ^ a : ℕ) : ℝ) ^ (w / 2) := by
    intro j
    induction j with
    | zero =>
      intro hj α x hx _ hx0
      exact (hx0 (by simpa [hzero] using hx)).elim
    | succ j ih =>
      intro hj α x hx hFx hx0
      let r : Fin m := ⟨j, by omega⟩
      by_cases hxprev : x ∈ V r.castSucc
      · exact ih (by omega) α x hxprev hFx hx0
      · obtain ⟨wr, G, hwr, hG, hp⟩ := hpure r
        let U := (V r.castSucc).comap (V r.succ).subtype
        let y : V r.succ := ⟨x, hx⟩
        have hFy : M.frobenius x ∈ V r.succ := by
          rw [hFx]
          exact (V r.succ).smul_mem α hx
        have hα : (FrobeniusModule.frobeniusEnd
            { carrier := V r.succ ⧸ U, frobenius := G }).HasEigenvalue α := by
          apply Module.End.hasEigenvalue_of_hasEigenvector
            (x := (Submodule.Quotient.mk y : V r.succ ⧸ U))
          rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
          constructor
          · change G (Submodule.Quotient.mk y) = α • Submodule.Quotient.mk y
            rw [hG y hFy, ← Submodule.Quotient.mk_smul]
            congr 1
            exact Subtype.ext hFx
          · intro hy
            apply hxprev
            exact (Submodule.Quotient.mk_eq_zero U).mp hy
        have hq : (1 : ℕ) ≤ p ^ a := one_le_pow₀ (Fact.out : p.Prime).one_le
        exact (IsPureOfWeight.hasWeightsAtMost hp).mono hq hwr α hα
  intro α hα
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  exact step m le_rfl α x (by rw [hwhole]; trivial) hx.1 hx.2

/-- The same four stability assertions for finite-dimensional Frobenius modules,
using mixedness defined by a finite stable filtration, with no semisimplicity assumption.
An equivariant split inclusion and projection express a direct summand.

Source: blueprint main-20261015, sec-deligne-laumon-general/sk-d-dl-general-weights,
lemma lem-a1-mixed-direct-summand, final paragraph
(blueprint: lem-a1-mixed-direct-summand).

Proof: for an injective equivariant map identify its source with the stable image,
and use lem-a1-subquotient-extension-bounds. For a surjective equivariant map identify
its target with the quotient by the stable kernel, and apply the same lemma. Given
an exact sequence, concatenate the image of a mixed filtration of the first term
with inverse images of a mixed filtration of the last term; exactness identifies
the successive quotients. This is lem-a1-extension-bounds. Finally a split inclusion
is injective, so the subobject assertion applies. Equivalently all three filtration
arguments for Weil sheaves apply directly to stable vector subspaces. They cover the
zero module, empty filtrations, repeated filtration terms, and nonsemisimple Frobenius.
-/
theorem mixedOfWeightsAtMost_stability
    (p a ell : ℕ) [Fact p.Prime] (ha : 1 ≤ a)
    [Fact ell.Prime] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra ℚ_[ell] Qlb] (hQ : IsAlgClosure ℚ_[ell] Qlb)
    (iota : Qlb ≃+* ℂ) (w : ℝ) :
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (f : A.carrier →ₗ[Qlb] B.carrier),
      (∀ x : A.carrier, f (A.frobenius x) = B.frobenius (f x)) →
      Function.Injective f →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w) ∧
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (g : A.carrier →ₗ[Qlb] B.carrier),
      (∀ x : A.carrier, g (A.frobenius x) = B.frobenius (g x)) →
      Function.Surjective g →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w) ∧
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (C : FrobeniusModule.{u₃, v} Qlb)
      (f : A.carrier →ₗ[Qlb] B.carrier) (g : B.carrier →ₗ[Qlb] C.carrier),
      (∀ x : A.carrier, f (A.frobenius x) = B.frobenius (f x)) →
      (∀ x : B.carrier, g (B.frobenius x) = C.frobenius (g x)) →
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota C w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w) ∧
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (i : A.carrier →ₗ[Qlb] B.carrier) (r : B.carrier →ₗ[Qlb] A.carrier),
      (∀ x : A.carrier, i (A.frobenius x) = B.frobenius (i x)) →
      (∀ x : B.carrier, r (B.frobenius x) = A.frobenius (r x)) →
      r.comp i = LinearMap.id →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w) := by
  have sub : ∀ (A : FrobeniusModule.{u₁, v} Qlb)
      (B : FrobeniusModule.{u₂, v} Qlb) (f : A.carrier →ₗ[Qlb] B.carrier),
      (∀ x, f (A.frobenius x) = B.frobenius (f x)) → Function.Injective f →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w := by
    intro A B f hf hinj hB
    apply isMixedOfWeightsAtMost_of_forall_hasEigenvalue p a ell ha hellp Qlb hQ iota A w
    intro α hα
    obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    apply mixed_eigenvalue_bound p a ell ha hellp Qlb hQ iota B w hB α
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := f x)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, (map_ne_zero_iff _ hinj).2 hx.2⟩
    change B.frobenius (f x) = α • f x
    rw [← hf, ← map_smul]
    exact congrArg f hx.1
  refine ⟨sub, ?_, ?_, ?_⟩
  · intro A B g hg hsurj hA
    apply isMixedOfWeightsAtMost_of_forall_hasEigenvalue p a ell ha hellp Qlb hQ iota B w
    intro α hα
    obtain ⟨y, hy⟩ := hα.exists_hasEigenvector
    exact mixed_eigenvalue_bound p a ell ha hellp Qlb hQ iota A w hA α
      (hasEigenvalue_of_hasEigenvector_mem_range g hg hy (hsurj y))
  · intro A B C f g hf hg hinj hexact hsurj hA hC
    exact IsMixedOfWeightsAtMost.of_shortExact p a ell ha hellp Qlb hQ iota
      A B C f g hf hg hinj hexact hsurj w hA hC
  · intro A B i r hi _ hri hB
    apply sub A B i hi _ hB
    intro x y hxy
    have hleft (z : A.carrier) : r (i z) = z := LinearMap.congr_fun hri z
    exact (hleft x).symm.trans ((congrArg r hxy).trans (hleft y))

end FrobeniusModule
