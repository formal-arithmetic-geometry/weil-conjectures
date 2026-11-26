/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralCtfTriangulated
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

/-!
# Finite coefficient extension preserves the uniform Tor interval

Ordinary derived coefficient extension preserves the finite-Tor domain.

## Implementation details

The comparison between completed scalar extension and reduction is obtained from the defining
residue equation of `completedCoefficientMap`, which identifies the composites `R → S → C` and
`R → A → C`, together with the composition of derived reductions.

## References

* [Stacks Project, Tags 06YY and 0G7E]
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard

universe d u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Ordinary completed scalar extension commutes with reduction at the same positive
exponent. This comparison requires neither constructibility nor derived completeness.
The integer inclusion sends the source uniformizer into the target maximal ideal,
so the same exponent is always sufficient, even for ramified extensions. -/
private theorem completedScalarReductionComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) (n : ℕ) :
    Nonempty (completedDerivedScalarExtension l E L ι W ⋙
        scalarReductionDerivedExtension l L W n ≅
      scalarReductionDerivedExtension l E W n ⋙
        ProEtale.scalarExtensionFunctor (integralScalarQuotientMap l E L ι n) W) := by
  let φ := completedCoefficientMap l E L ι W
  let ψ := completedIntegralCommRingProjectionUnrestricted l L W n
  let α := completedIntegralCommRingProjectionUnrestricted l E W n
  let β := integralScalarQuotientSheafMap l E L ι W n
  have hs : φ ≫ ψ = α ≫ β :=
    (completedCoefficientMap_existsUnique l E L ι W).exists.choose_spec n
  obtain ⟨f, hf, _⟩ := AlgebraicGeometry.Scheme.derivedReductionComposition
    W φ ψ (α ≫ β) hs
  obtain ⟨g, hg, _⟩ := AlgebraicGeometry.Scheme.derivedReductionComposition
    W α β (α ≫ β) rfl
  have := hf.1
  have := hg.1
  exact ⟨asIso f ≪≫ (asIso g).symm⟩

end WeilConjectures
