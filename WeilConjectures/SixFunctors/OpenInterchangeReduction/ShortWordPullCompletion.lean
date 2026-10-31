/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.ProperOpenLambdaOrdinarySquare
import WeilConjectures.SixFunctors.OpenInterchangeReduction.ProperOpenLambdaCompletionTransport
import WeilConjectures.SixFunctors.GeneratorReduction.ShortWordCompletionIsomorphism
import WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveCompletionEffectivity
import all WeilConjectures.SixFunctors.GeneratorReduction.ShortWordIntegralDomain

/-! # One further pullback of an admissible short word

Source: the recursive completion comparison in the coefficient coherence proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction

private theorem completion_inverse_eq_inv {C : Type*} [Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [IsIso f] :
    inverseOrZero f = inv f := by
  simp only [inverseOrZero, dif_pos (inferInstance : IsIso f)]

/-- Completion transport and effectivity for one pullback of a short admissible word.
The outer pullback is allowed to produce a word of length four.
Source: blueprint `fix-prop-coherence.proof.md`, completion transport of the
proper/open restriction factor (blueprint: lem-sf-short-word-pull-completion).

Proof: normalized reconstruction identifies the integral value of the child with
its normalized admissible system's limit. Its finite reductions inherit the given
constructibility and Tor bounds, so primitive pull completion is invertible there.
The child's completion map is invertible by short-word effectivity. Their composite
is the pull word's completion map. After reduction, cancel the primitive completion
unit against its inverse in pullR. Naturality of reductionPull moves the remaining
child completion map through the ordinary pull comparison. The child's completion
transport identifies the resulting composite with the ordinary recursive map.
No admissibility or length bound on the outer pullback is needed. -/
theorem shortWordPullCompletion
    {D : FiniteFieldDatum.{u}} (Cf : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic Cf.l) E]
    [FiniteDimensional (Padic Cf.l) E] (o : Operations Cf.l E)
    {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)
    {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
    (ht : LocallyOfFiniteType f) (hq : QuasiCompact f)
    (B : Word W location b) (hLength : B.length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource Cf.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hInputs : ∀ k : I, Admissible Cf.l E
      (IntegralSystemRealization.calculus Cf.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (hB : Word.admissible Cf.l E W location o K lo hi torLo torHi B) :
    IsIso ((Word.pull f hs ht hq B).completionMap Cf.l E W location o K) ∧
      (IntegralSystemRealization.calculus Cf.l E (W a)).reduction.map
          ((Word.pull f hs ht hq B).completionMap Cf.l E W location o K) ≫
        (Word.pull f hs ht hq B).r Cf.l E W location o K =
        properOpenOrdinaryR Cf.l E location o K (Word.pull f hs ht hq B) := by
  obtain ⟨e⟩ := word_realization Cf.l E W location o K lo hi torLo torHi hInputs B hB
  have hsys := word_system_admissible Cf.l E W location o K lo hi torLo torHi B hB
  have hdom := domain_of_realization Cf.l E (W b) _ lo hi torLo torHi hsys _ e
  have hu := (primitiveCompletionEffectivity Cf.l E o).2.1 f hs ht hq _ (Or.inl hdom)
  have hc := completionMap_isIso Cf.l E W location o B hLength K lo hi torLo torHi
    hInputs hB
  have htB := properOpenLambdaCompletionTransport Cf E o W location B hLength K
    lo hi torLo torHi hInputs hB
  constructor
  · dsimp only [Word.completionMap]
    infer_instance
  · dsimp only [Word.completionMap, Word.r, pullR, properOpenOrdinaryR]
    simp only [Functor.map_comp, Category.assoc]
    rw [completion_inverse_eq_inv]
    simp only [IsIso.hom_inv_id_assoc]
    have hn := (o.realization.reductionPull f).hom.naturality
      (B.completionMap Cf.l E W location o K)
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, htB]

end WeilConjectures.OpenInterchangeReduction
