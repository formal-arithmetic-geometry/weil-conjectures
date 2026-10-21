/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T5
-/
module

public import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence

/-! # The reflector for the integral quotient Roos unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual quotient augmentation is the reflector unit, at independent site and
coefficient universes. Source: Stacks 099B, 099M and 0A0E;
(blueprint: lem-sf-integral-roos-reflector).

Proof: replace the pro-etale site by a small equivalent site in the universe containing
both its objects and the coefficient ring. Transport the completed ring, its uniformizer
section and the strict finite quotient diagram. The ringed Koszul reflector applies to
the one-element generating list. Its completion and unit are represented by the signed
product fiber and (u,0). The completed Koszul-to-quotient comparison and strict Roos
comparison identify this unit with the quotient augmentation on flat-term K-flat
representatives. Descent identifies the resulting functor and unit with IntegralOnSlice's
specified ones. Transport complete output and the Hom bijection through this normalized
isomorphism. Finally the exact Koszul tensor tower and exact countable
products preserve quasi-isomorphisms on all complexes, so its unit-isomorphism condition
is independent of an arbitrary representative, including representatives that are not
K-flat. Thus the universal quantification in the final condition is equivalent to the
condition on a flat-term K-flat representative. -/
theorem integralRoosReflector
    (T : Scheme.{t})
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) :
    (∀ H : IntegralOnSlice.D l E T none,
      ∀ (C : IntegralOnSlice.Cx l E T none)
        (rC : DerivedCategory.Q.obj C ≅ (IntegralOnSlice.completion l E T none).obj H),
        IsIso (integralKoszulIntrinsicUnit l E T _ C rC)) ∧
    (∀ H L : IntegralOnSlice.D l E T none,
      (∀ (C : IntegralOnSlice.Cx l E T none) (rC : DerivedCategory.Q.obj C ≅ L),
        IsIso (integralKoszulIntrinsicUnit l E T L C rC)) →
      Function.Bijective (fun f : (IntegralOnSlice.completion l E T none).obj H ⟶ L ↦
        (IntegralOnSlice.completionUnit l E T none).app H ≫ f)) ∧
    (∀ H : IntegralOnSlice.D l E T none,
      IsIso ((IntegralOnSlice.completionUnit l E T none).app H) ↔
        ∀ (C : IntegralOnSlice.Cx l E T none) (rC : DerivedCategory.Q.obj C ≅ H),
          IsIso (integralKoszulIntrinsicUnit l E T H C rC)) := by
  sorry

end WeilConjectures
