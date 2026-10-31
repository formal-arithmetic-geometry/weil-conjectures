/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneratorReductionData
import WeilConjectures.SixFunctors.PrimitiveCompletionEffectivity
import all WeilConjectures.SixFunctors.ShortWordIntegralDomain

/-! # Completion transport for arbitrary admissible finite words

Source: current blueprint fix-prop-coherence, recursive structural substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u s i
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)

/-- Recursive completion transport is invertible for every admissible finite word.
Source: current blueprint fix-prop-coherence, recursive structural substitution.
(blueprint: lem-sf-structural-pull-push-unit-completion)

Proof: normalized reconstruction identifies each integral child with the limit of
its actual system. The system's given bounds therefore make that child complete,
constructible and of finite Tor amplitude. Induct on the finite word. Inputs and
units have identity completion maps. Primitive completion effectivity makes the
tensor and pull completion units invertible on these children. Proper image uses
the invertible reconstruction unit followed by the specified limit comparison.
Open extension applies a functor to the child's completion. Functors, products
and composition preserve all these isomorphisms. No length bound is needed. -/
theorem structuralPullPushUnitCompletion_isIso (o : Operations l E)
    {a : S} (B : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (_hIntermediate : Word.admissible l E W location o K lo hi torLo torHi B) :
    IsIso (B.completionMap l E W location o K) := by
  have domain {a : S} (C : Word W location a)
      (hC : C.admissible l E W location o K lo hi torLo torHi) :
      finiteTorConstructibleIntegral l E (W a) (C.integralValue l E W location o K) ∨
        C.integralValue l E W location o K =
          (IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit := by
    obtain ⟨e⟩ := word_realization l E W location o K lo hi torLo torHi _hAdm C hC
    have hsys := word_system_admissible l E W location o K lo hi torLo torHi C hC
    exact Or.inl (domain_of_realization l E (W a) _ lo hi torLo torHi hsys _ e)
  revert _hIntermediate
  induction B with
  | input k =>
    intro _
    dsimp only [Word.completionMap]
    infer_instance
  | unit a =>
    intro _
    dsimp only [Word.completionMap]
    infer_instance
  | tensor B C ihB ihC =>
    intro _hIntermediate
    obtain ⟨hB, hC⟩ := _hIntermediate.2
    have := ihB hB
    have := ihC hC
    have := (primitiveCompletionEffectivity l E o).1 _ _ _ (domain B hB) (domain C hC)
    have : IsIso (Prod.mkHom (B.completionMap l E W location o K)
        (C.completionMap l E W location o K)) := by
      exact (Iso.prod (asIso (B.completionMap l E W location o K))
        (asIso (C.completionMap l E W location o K))).isIso_hom
    dsimp only [Word.completionMap]
    infer_instance
  | pull f hs ht hq B ih =>
    intro _hIntermediate
    have hB := _hIntermediate.2
    have := ih hB
    have := (primitiveCompletionEffectivity l E o).2.1 f hs ht hq _
      (domain B hB)
    dsimp only [Word.completionMap]
    infer_instance
  | push f hs ht hq hp B ih =>
    intro _hIntermediate
    have hB := _hIntermediate.2
    have := ih hB
    have := (primitiveCompletionEffectivity l E o).2.2 _ _
      (domain B hB)
    dsimp only [Word.completionMap]
    infer_instance
  | «open» j hj hq B ih =>
    intro _hIntermediate
    let := hj
    have hB := _hIntermediate.2
    have := ih hB
    dsimp only [Word.completionMap]
    infer_instance

end WeilConjectures.GeneratorReduction
