/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefScalarReductionExchange
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralScalarQuotientTransitionTranspose

/-! # Scalar tensor quotient transition compatibility

Source: current blueprint lem-coef-integral-finite-extension, paragraphs 3--4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
attribute [local irreducible] scalarReductionDerivedExtension
  integralScalarExtensionOfUniverses quotient normalizedDVRReductionTransition
  scalarReductionExchange

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The completed tensor quotient comparison respects the actual normalized
reduction transitions, through the canonical mixed scalar/quotient map.
Source: lem-coef-integral-finite-extension, first paragraph and the quotient
compatibility in the third paragraph; Stacks Tag 06YY.
(blueprint: lem-sf-integral-scalar-quotient-transition)

Proof: First conjugate by completion at each level. The normalized reduction
transition is natural in the integral input, so these two factors move to the
same side. Expand quotient into finiteReductionIso, tensorSquare, and the source
finiteReductionIso. Transpose both sides under the target scalar adjunction at m.
Use the defining unit equation of scalarReductionExchange, which is the mate of
scalarRestrictionSquare. The scalar composition isomorphisms in tensorSquare are
leftAdjointUniq isomorphisms and therefore carry the iterated unit to the direct
unit. The scalarReductionDerivedExtension adjunction is normalized on K-flat
representatives by that same ordinary tensor unit. Thus both transposes take x
to 1 tensor x at level n, transported by the single coefficient restriction
square. The coefficient square holds on quotient representatives; the two ways
of pasting its restriction identifications are identity on underlying sections.
Sheafification, passage to complexes, and exact restriction localization preserve
this identity. Hom-adjunction injectivity yields the required equality. No
flatness of the individual quotient or ramification-divisibility hypothesis is
used. When m=n the same calculation is the scalar unit triangle identity; at
level zero it is the exponent-one quotient. -/
theorem quotient_reduction_transition
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K)
    {m n : ℕ} (h : n ≤ m) :
    (quotient l E L ι X m K hK).hom ≫
        (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
          (normalizedDVRReductionTransition l E X D hl h K) ≫
        (scalarReductionExchange l E L ι X h).app
          ((scalarReductionDerivedExtension l E X n).obj K) =
      normalizedDVRReductionTransition l L X D hl h
          ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≫
        (normalizedDVRRes l L X h).map (quotient l E L ι X n K hK).hom := by
  apply Equiv.injective ((normalizedDVRIntegralAdjunction l L X m).homEquiv _ _)
  exact quotient_reduction_transition_transpose l E L ι X D hl K hK h

end WeilConjectures.IntegralFiniteExtension
