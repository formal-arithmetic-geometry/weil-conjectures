/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeKunnethStatement
public import WeilConjectures.AlgebraicGeometry.Picard.RelativeKunnethCoherence.RelativeKunnethCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
import WeilConjectures.AlgebraicGeometry.RelativeKunnethInverseWord
import WeilConjectures.SmoothPurity.ProjectionFormulaCoherence
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.LeftCoefficientProjectionAction
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons

/-! # One compatibility of the relative product -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.RelativeKunnethCoherence

/-- Associativity of the specified relative product on a common triple-product realization.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, clause (ii)
(blueprint: lem-sf-relative-kunneth-associativity).

Proof: expand the two inverse iterates with
relativeKunnethIsoOfIsPullback_inverse_word. Use naturality to move the inner product
inside the last compact-support functor. Apply the projection/base-change square twice,
once for the middle factor and once for the first product projection. The exchanged
base-change maps combine to the maps for the pasted Cartesian rectangles. The projection
composition pentagon and its coefficient-variable action equation combine the two
successive projections into the right-associated word. In the action equation, the
proper case is the counit-defined projection action, and the open case is determined by
restriction using the invertible open-extension unit. The compact-support composition
pentagon identifies the two final compositors. Monoidality of pullback and the derived
tensor associator identify exactly s.externalAssoc and s.targetAssoc. Invert the equality
of inverse words to obtain the displayed equality of the original forward iterates.
-/
theorem relativeKunneth_associativity
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k]
    [HasTateTwist Λ] [HasInvertibleExponent Λ (Spec (.of k))]
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    [HasCompactification aB] :
    (∀ (s : Triple B)
      [HasCompactification (s.xy.f ≫ aB)] [HasCompactification (s.xy.g ≫ aB)]
      [HasCompactification (s.h ≫ aB)]
      (_Sf : SixFunctorDatum Λ k s.xy.f aB)
      (_Sg : SixFunctorDatum Λ k s.xy.g aB) (_Sh : SixFunctorDatum Λ k s.h aB)
      (K : DerivedCategoryModule Λ s.xy.X) (L : DerivedCategoryModule Λ s.xy.Y)
      (M : DerivedCategoryModule Λ s.W)
      (_hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) s.xy.X K)
      (_hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) s.xy.Y L)
      (_hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) s.W M),
      (s.sourceAssoc K L M).hom ≫ (s.rightKappa K L M).hom =
        (s.leftKappa K L M).hom ≫ (s.targetAssoc K L M).hom) := by sorry

end WeilConjectures.RelativeKunnethCoherence
