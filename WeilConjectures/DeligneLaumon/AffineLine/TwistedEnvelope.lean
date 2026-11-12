/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.TraceReality
public import WeilConjectures.WeilSheaf.StalkComparison
public import WeilConjectures.WeilSheaf.StalkExtensionByZero
public import WeilConjectures.WeilSheaf.StalkTensorTrace
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TracePow

/-!
# Twisting and adding the dual

Let `A` be a lisse Weil sheaf, punctually `ι`-pure of weight zero, and let `L` be a lisse Weil
sheaf whose local Frobenius eigenvalues are of finite order. The *twisted envelope*

`(A ⊗ L) ⊕ (A^∨ ⊗ L^∨)`

is `ι`-real and punctually `ι`-pure of weight zero, and its extension by zero along an open
immersion is `ι`-real as well. For `L` of rank one, `L^∨ = L⁻¹`, which is the form of the
blueprint; the rank plays no role in the proof.

The local eigenvalues of `L` are roots of unity, so `L` is punctually pure of weight zero, and
so is `A ⊗ L`. On the dual of a module pure of weight zero the traces of the powers of the
Frobenius are the complex conjugates of those on the module
(`FrobeniusModule.IsPureOfWeight.map_trace_frobeniusEnd_dual_pow`), and the traces on a tensor
product are the products of the traces
(`AlgebraicGeometry.WeilSheaf.trace_stalk_tensorObj_frobeniusEnd_pow`). So at every closed point
the traces of the two summands are mutually conjugate, which makes the sum real
(`FrobeniusModule.isReal_prod_of_map_trace_frobeniusEnd_pow`).
The extension by zero of a real sheaf is real: its stalks are those of the sheaf on the open and
zero outside, where the local polynomial is `1`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.twistedEnvelope`: the sheaf `(A ⊗ L) ⊕ (A^∨ ⊗ L^∨)`.
- `AlgebraicGeometry.WeilSheaf.IsReal.extensionByZero`: the extension by zero of a real sheaf is
  real.
- `AlgebraicGeometry.WeilSheaf.isReal_twistedEnvelope_and_isPunctuallyPureOfWeight`
  (`lemma-twisted-envelope`): the twisted envelope is real and pure of weight zero, and its
  extension by zero along an open immersion is real.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- A Weil sheaf whose local Frobenius eigenvalues are all of finite order is punctually
`ι`-pure of weight zero: the images under `ι` of its eigenvalues are roots of unity. -/
theorem isPunctuallyPureOfWeight_zero_of_isOfFinOrder (ι : PadicAlgCl l →+* ℂ)
    {L : WeilSheaf k₀ l X}
    (hL : ∀ (x : X.finitePoints) (α : PadicAlgCl l),
      (L.stalk x).frobeniusEnd.HasEigenvalue α → IsOfFinOrder α) :
    L.IsPunctuallyPureOfWeight ι 0 := fun x α hα ↦ by
  rw [zero_div, Real.rpow_zero]
  exact (ι.toMonoidHom.isOfFinOrder (hL x α hα)).norm_eq_one

/-- On the dual of a lisse Weil sheaf punctually `ι`-pure of weight zero, the images under `ι`
of the traces of the powers of the local Frobenius are the complex conjugates of those on the
sheaf. -/
theorem IsPunctuallyPureOfWeight.map_trace_frobeniusEnd_pow_stalk_dual {ι : PadicAlgCl l →+* ℂ}
    {F : WeilSheaf k₀ l X} (hF : F.IsLisse) (h : F.IsPunctuallyPureOfWeight ι 0)
    (x : X.finitePoints) (n : ℕ) :
    ι (LinearMap.trace (PadicAlgCl l) _ (((F.dual hF).stalk x).frobeniusEnd ^ n)) =
      starRingEnd ℂ (ι (LinearMap.trace (PadicAlgCl l) _ ((F.stalk x).frobeniusEnd ^ n))) := by
  obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF x
  rw [← e.trace_frobeniusEnd_pow]
  exact (h x).map_trace_frobeniusEnd_dual_pow n

section ExtensionByZero

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

/-- **The extension by zero of a real sheaf is real.** At a closed point of the open the stalk
of `j₀!G` is that of `G`, and at a closed point outside the open it vanishes, so that its local
polynomial is `1`. -/
theorem IsReal.extensionByZero {ι : PadicAlgCl l →+* ℂ} {G : WeilSheaf k₀ l U}
    (hG : G.IsReal ι) : ((WeilSheaf.extensionByZero j).obj G).IsReal ι := by
  intro x
  by_cases hx : x.1 ∈ Set.range j.base
  · obtain ⟨z, hz⟩ := hx
    have hz' : z ∈ U.finitePoints :=
      (Scheme.Hom.mem_finitePoints_iff_of_isIso j z).1 (hz ▸ x.2)
    obtain rfl : x = ⟨j.base z, (Scheme.Hom.mem_finitePoints_iff_of_isIso j z).2 hz'⟩ :=
      Subtype.ext hz.symm
    obtain ⟨e⟩ := nonempty_equiv_stalk_extensionByZero j G ⟨z, hz'⟩
    exact (hG ⟨z, hz'⟩).of_localPolynomial_eq e.localPolynomial_eq
  · have := subsingleton_stalk_extensionByZero j G x hx
    exact FrobeniusModule.isReal_of_subsingleton ι _

end ExtensionByZero

/-- The *twisted envelope* `(A ⊗ L) ⊕ (A^∨ ⊗ L^∨)` of a lisse Weil sheaf `A` by a lisse Weil
sheaf `L`. For `L` of rank one, `L^∨ = L⁻¹`. (blueprint: `lemma-twisted-envelope`) -/
noncomputable def twistedEnvelope (A L : WeilSheaf k₀ l X) (hA : A.IsLisse) (hL : L.IsLisse) :
    WeilSheaf k₀ l X :=
  A.tensorObj L hA ⊞ (A.dual hA).tensorObj (L.dual hL) hA.dual

variable {ι : PadicAlgCl l →+* ℂ} {A L : WeilSheaf k₀ l X} (hA : A.IsLisse) (hL : L.IsLisse)

/-- The twisted envelope of lisse sheaves is lisse. -/
theorem IsLisse.twistedEnvelope : (twistedEnvelope A L hA hL).IsLisse :=
  (hA.tensorObj hL).biprod (hA.dual.tensorObj hL.dual)

/-- **The twisted envelope is real.** If `A` and `L` are lisse and punctually `ι`-pure of weight
zero, then at every closed point the traces of the powers of the local Frobenius on
`A^∨ ⊗ L^∨` are the complex conjugates of those on `A ⊗ L`, so that the twisted envelope
`(A ⊗ L) ⊕ (A^∨ ⊗ L^∨)` is `ι`-real. -/
theorem isReal_twistedEnvelope (hA₀ : A.IsPunctuallyPureOfWeight ι 0)
    (hL₀ : L.IsPunctuallyPureOfWeight ι 0) : (twistedEnvelope A L hA hL).IsReal ι := by
  intro x
  obtain ⟨e⟩ := nonempty_equiv_stalk_biprod (A.tensorObj L hA)
    ((A.dual hA).tensorObj (L.dual hL) hA.dual) x
  refine FrobeniusModule.IsReal.of_localPolynomial_eq
    (FrobeniusModule.isReal_prod_of_map_trace_frobeniusEnd_pow fun n ↦ ?_) e.localPolynomial_eq
  rw [trace_stalk_tensorObj_frobeniusEnd_pow, trace_stalk_tensorObj_frobeniusEnd_pow, map_mul,
    map_mul, map_mul, hL₀.map_trace_frobeniusEnd_pow_stalk_dual hL,
    hA₀.map_trace_frobeniusEnd_pow_stalk_dual hA]

/-- **The twisted envelope is pure of weight zero**, if `A` and `L` are: `A ⊗ L` is of weight
`0 + 0`, and `A^∨ ⊗ L^∨` of weight `-0 + -0`. -/
theorem isPunctuallyPureOfWeight_twistedEnvelope (hA₀ : A.IsPunctuallyPureOfWeight ι 0)
    (hL₀ : L.IsPunctuallyPureOfWeight ι 0) :
    (twistedEnvelope A L hA hL).IsPunctuallyPureOfWeight ι 0 := by
  have hdual {F : WeilSheaf k₀ l X} (hF : F.IsLisse) (h : F.IsPunctuallyPureOfWeight ι 0) :
      (F.dual hF).IsPunctuallyPureOfWeight ι 0 := fun x ↦ by
    obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF x
    simpa using ((h x).dual).of_equiv e
  have h₁ := hA₀.tensorObj hA hL₀
  have h₂ := (hdual hA hA₀).tensorObj hA.dual (hdual hL hL₀)
  rw [add_zero] at h₁ h₂
  intro x
  obtain ⟨e⟩ := nonempty_equiv_stalk_biprod (A.tensorObj L hA)
    ((A.dual hA).tensorObj (L.dual hL) hA.dual) x
  exact ((h₁ x).prod (h₂ x)).of_equiv e

/-- **Twisting and adding the dual.** Let `A` be lisse and punctually `ι`-pure of weight zero,
and let `L` be lisse with local Frobenius eigenvalues of finite order. Then the twisted envelope
`(A ⊗ L) ⊕ (A^∨ ⊗ L^∨)` is `ι`-real and punctually `ι`-pure of weight zero, and its extension by
zero along any (quasi-compact) open immersion `j : X ⟶ Y` is `ι`-real as well.

For `L` of rank one, `L^∨ = L⁻¹`, which is the statement of the blueprint; the rank is not used.
(blueprint: `lemma-twisted-envelope`, `lemma-twisted-envelope--1`) -/
theorem isReal_twistedEnvelope_and_isPunctuallyPureOfWeight
    (hA₀ : A.IsPunctuallyPureOfWeight ι 0)
    (hLfin : ∀ (x : X.finitePoints) (α : PadicAlgCl l),
      (L.stalk x).frobeniusEnd.HasEigenvalue α → IsOfFinOrder α) :
    (twistedEnvelope A L hA hL).IsReal ι ∧
      (twistedEnvelope A L hA hL).IsPunctuallyPureOfWeight ι 0 ∧
      ∀ {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))] (j : X ⟶ Y) [IsOpenImmersion j]
        [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))],
        ((extensionByZero j).obj (twistedEnvelope A L hA hL)).IsReal ι := by
  have hL₀ := isPunctuallyPureOfWeight_zero_of_isOfFinOrder ι hLfin
  have hR := isReal_twistedEnvelope hA hL hA₀ hL₀
  exact ⟨hR, isPunctuallyPureOfWeight_twistedEnvelope hA hL hA₀ hL₀,
    fun j _ _ _ ↦ hR.extensionByZero j⟩

end AlgebraicGeometry.WeilSheaf
