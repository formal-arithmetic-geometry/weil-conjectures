/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionData
import WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveCompletionEffectivity
import all WeilConjectures.SixFunctors.GeneratorReduction.ShortWordIntegralDomain
/-! # Invertibility of admissible finite-word completion transport

Source: blueprint fix-prop-coherence, basic structural maps
(blueprint: lem-sf-generator-reduction-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u s i v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)

private theorem integral_domain
    {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)
    (o : Operations l E) {a : S} (B : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (ha : B.admissible l E W location o K lo hi torLo torHi) :
    finiteTorConstructibleIntegral l E (W a) (B.integralValue l E W location o K) := by
  obtain ⟨e⟩ := word_realization l E W location o K lo hi torLo torHi hAdm B ha
  have hsys := word_system_admissible l E W location o K lo hi torLo torHi B ha
  exact domain_of_realization l E (W a) _ lo hi torLo torHi hsys _ e

/-- Completion transport is invertible for any finite word on its recursive domain.
Source: current blueprint fix-prop-coherence, maps-used sentence and structural substitution.
(blueprint: lem-sf-unbounded-word-completion-isomorphism)

Proof: the existing realization induction has no length hypothesis. It identifies each
integral vertex with the total limit of its normalized admissible system. Reconstruction
therefore gives the complete constructible finite-Tor domain at every vertex. Induct on
words: input and scalar-unit maps are identities; tensor and pullback use primitive
completion effectivity on their integral children; proper image uses its reconstruction
unit and the specified push comparison; open extension applies a functor to the child map.
Functors and the two tensor slots preserve isomorphisms. No bound on word length is used.
-/
theorem unboundedCompletionMap_isIso (o : Operations l E)
    {a : S} (B : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (_hIntermediate : Word.admissible l E W location o K lo hi torLo torHi B) :
    IsIso (B.completionMap l E W location o K) := by
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
    have := (primitiveCompletionEffectivity l E o).1 _ _ _
      (Or.inl (integral_domain l E W location o B K lo hi torLo torHi _hAdm hB))
      (Or.inl (integral_domain l E W location o C K lo hi torLo torHi _hAdm hC))
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
      (Or.inl (integral_domain l E W location o B K lo hi torLo torHi _hAdm hB))
    dsimp only [Word.completionMap]
    infer_instance
  | push f hs ht hq hp B ih =>
    intro _hIntermediate
    have hB := _hIntermediate.2
    have := ih hB
    have := (primitiveCompletionEffectivity l E o).2.2 _ _
      (Or.inl (integral_domain l E W location o B K lo hi torLo torHi _hAdm hB))
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
