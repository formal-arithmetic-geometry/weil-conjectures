/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeKunnethStatement
public import WeilConjectures.AlgebraicGeometry.Picard.RelativeKunnethCoherence.RelativeKunnethCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
import WeilConjectures.AlgebraicGeometry.RelativeKunnethProperSymmetry
import WeilConjectures.AlgebraicGeometry.RelativeKunnethInverseWord
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube
import WeilConjectures.SmoothPurity.CompactificationProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-! # One compatibility of the relative product -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.RelativeKunnethCoherence

/-- Symmetry of the specified relative product for arbitrary compactifiable factors.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, clause (i)
(blueprint: lem-sf-relative-kunneth-symmetry).

Proof: choose compactifications of f and g. Use their product compactification, whose
proper part is the product of the two proper maps and whose open part is the product
of the opens. Expand the inverse word using relativeKunnethIsoOfIsPullback_inverse_word.
The proper/open exchange cube and projection-composition identity identify this word
with the proper product of the two extended inputs followed by the open tensor-product
comparison. The proper square commutes by
relativeKunnethIsoOfIsPullback_proper_symmetry. The two open-product comparisons agree
after restriction, since both restrict to the signed tensor symmetry. The derived open
extension has invertible unit, so this restriction determines their maps. Paste the proper
and open squares and cancel the canonical compactification comparisons. Refinement
coherence identifies those comparisons with the originally chosen compactifications.
This is equality for the given kappa, with no new choice of product map.
-/
theorem relativeKunneth_symmetry
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k]
    [HasTateTwist Λ] [HasInvertibleExponent Λ (Spec (.of k))]
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    [HasCompactification aB] :
    (∀ (d : Pair B)
      [HasCompactification (d.f ≫ aB)] [HasCompactification (d.g ≫ aB)]
      (_Sf : SixFunctorDatum Λ k d.f aB) (_Sg : SixFunctorDatum Λ k d.g aB)
      (K : DerivedCategoryModule Λ d.X) (L : DerivedCategoryModule Λ d.Y)
      (_hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) d.X K)
      (_hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) d.Y L),
      (d.sourceSwap K L).hom ≫ (d.swap.kappa L K).hom =
        (d.kappa K L).hom ≫ (d.targetSwap K L).hom) := by sorry

end WeilConjectures.RelativeKunnethCoherence
