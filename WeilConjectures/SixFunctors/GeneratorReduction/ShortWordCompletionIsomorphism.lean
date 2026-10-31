/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionData
import WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveCompletionEffectivity
import WeilConjectures.SixFunctors.GeneratorReduction.ShortWordIntegralDomain
/-! # Invertibility of short-word completion transport

Source: blueprint fix-prop-coherence, basic structural maps
(blueprint: lem-sf-generator-reduction-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)

/-- The recursive completion transport is invertible on the short-word domain.
Source: blueprint coherence proof, steps 1--3
(blueprint: lem-sf-generator-reduction-coherence).

Proof: induction through at most three primitive vertices. Inputs and units have
identity maps. The representative-normalized pull and tensor completion maps are
invertible on the complete constructible finite-Tor domain, by the corresponding
operation reduction and completion comparisons. For proper image apply the actual
right-adjoint-conjugate limit comparison after the reconstruction unit; the input
unit is invertible on complete objects. Open extension applies an exact functor
to the child comparison. Functors and the binary tensor preserve isomorphisms.
The assumed bounds and compatible origins apply at precisely each intermediate. -/
theorem completionMap_isIso (o : Operations l E)
    {a : S} (B : Word W location a)
    (_hLength : B.length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (_hIntermediate : Word.admissible l E W location o K lo hi torLo torHi B) :
    IsIso (B.completionMap l E W location o K) := by
  revert _hLength _hIntermediate
  induction B with
  | input k =>
    intro _ _
    dsimp only [Word.completionMap]
    infer_instance
  | unit a =>
    intro _ _
    dsimp only [Word.completionMap]
    infer_instance
  | tensor B C ihB ihC =>
    intro _hLength _hIntermediate
    obtain ⟨hB, hC⟩ := _hIntermediate.2
    have hlenB : B.length ≤ 2 := by simp only [Word.length] at _hLength; omega
    have hlenC : C.length ≤ 2 := by simp only [Word.length] at _hLength; omega
    have := ihB (by omega) hB
    have := ihC (by omega) hC
    have := (primitiveCompletionEffectivity l E o).1 _ _ _
      (shortWordIntegralDomain l E W location o B hlenB K lo hi torLo torHi _hAdm hB)
      (shortWordIntegralDomain l E W location o C hlenC K lo hi torLo torHi _hAdm hC)
    have : IsIso (Prod.mkHom (B.completionMap l E W location o K)
        (C.completionMap l E W location o K)) := by
      exact (Iso.prod (asIso (B.completionMap l E W location o K))
        (asIso (C.completionMap l E W location o K))).isIso_hom
    dsimp only [Word.completionMap]
    infer_instance
  | pull f hs ht hq B ih =>
    intro _hLength _hIntermediate
    have hB := _hIntermediate.2
    have hlen : B.length ≤ 2 := by simp only [Word.length] at _hLength; omega
    have := ih (by omega) hB
    have := (primitiveCompletionEffectivity l E o).2.1 f hs ht hq _
      (shortWordIntegralDomain l E W location o B hlen K lo hi torLo torHi _hAdm hB)
    dsimp only [Word.completionMap]
    infer_instance
  | push f hs ht hq hp B ih =>
    intro _hLength _hIntermediate
    have hB := _hIntermediate.2
    have hlen : B.length ≤ 2 := by simp only [Word.length] at _hLength; omega
    have := ih (by omega) hB
    have := (primitiveCompletionEffectivity l E o).2.2 _ _
      (shortWordIntegralDomain l E W location o B hlen K lo hi torLo torHi _hAdm hB)
    dsimp only [Word.completionMap]
    infer_instance
  | «open» j hj hq B ih =>
    intro _hLength _hIntermediate
    let := hj
    have hB := _hIntermediate.2
    have hlen : B.length ≤ 3 := by simp only [Word.length] at _hLength; omega
    have := ih hlen hB
    dsimp only [Word.completionMap]
    infer_instance


end WeilConjectures.GeneratorReduction
