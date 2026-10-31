/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefScalarReductionExchange
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralScalarQuotientTransitionTransposeCore

/-! # Transpose calculation for scalar quotient transitions

Source: current blueprint, lem-sf-integral-scalar-quotient-transition, proof step 2.
(blueprint: lem-sf-integral-scalar-quotient-transition-transpose)
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

/-- The two morphisms in the scalar quotient transition square have the same
transpose under the target scalar adjunction at level `m`.

The transpose is the map obtained by applying the hom equivalence of
`normalizedDVRIntegralAdjunction` to the displayed morphism. This is the mate
calculation in the proof of the quotient transition theorem: after expanding
the quotient comparison and the mixed scalar/quotient mate, both sides reduce
to the same coefficient restriction square. The assertion is about the
transposed maps; equality of the original maps is obtained by injectivity of
that hom equivalence.

Source: lem-sf-integral-scalar-quotient-transition, proof step 2.
(blueprint: lem-sf-integral-scalar-quotient-transition-transpose)
-/
theorem quotient_reduction_transition_transpose
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K)
    {m n : ℕ} (h : n ≤ m) :
    (normalizedDVRIntegralAdjunction l L X m).homEquiv _ _
        ((quotient l E L ι X m K hK).hom ≫
          (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
            (normalizedDVRReductionTransition l E X D hl h K) ≫
          (scalarReductionExchange l E L ι X h).app
            ((scalarReductionDerivedExtension l E X n).obj K)) =
      (normalizedDVRIntegralAdjunction l L X m).homEquiv _ _
        (normalizedDVRReductionTransition l L X D hl h
            ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≫
          (normalizedDVRRes l L X h).map
            (quotient l E L ι X n K hK).hom) := by
  simp only [normalizedDVRReductionTransition, scalarReductionExchange, quotient,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [Adjunction.homEquiv_naturality_left]
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  simp only [Category.assoc]
  rw [Adjunction.homEquiv_naturality_left]
  simpa only [normalizedDVRReductionTransition, scalarReductionExchange, quotientResidual,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Functor.comp_obj,
    Functor.comp_map, Functor.map_comp, Adjunction.homEquiv_counit, Category.assoc] using
    (quotient_reduction_transition_transpose_core l E L ι X D hl K hK h)

end WeilConjectures.IntegralFiniteExtension
