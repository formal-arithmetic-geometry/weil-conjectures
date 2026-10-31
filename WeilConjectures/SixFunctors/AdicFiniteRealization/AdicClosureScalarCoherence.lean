/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.InternalTensorCompositionUnitNormalization

/-! # Scalar coherence after extension to the native closure ring

Source: BS Proposition 6.8.14(2); balanced tensor associativity.
(blueprint: lem-sf-adic-closure-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicFiniteRealization
variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]

/-- Further extension along the actual coefficient cocone preserves the scalar equations.
Source: finite realization node, step 6, final assertion
(blueprint: lem-sf-adic-closure-scalar-coherence).

Proof:
1. Expand closureComparison into scalarComparison followed by the normalized
composition comparison for extension of scalars. Functoriality of extension to R
sends the finite tower equality in H.tower to an equality over R.
2. Naturality moves each inner scalar comparison past the outer composition
comparison. The remaining two composites of extension comparisons are equal by
uniqueness of left adjoints to the same restriction functor, or by their common
K-flat tensor formula r tensor (g tensor (f tensor x)) maps to rgf tensor x.
The coefficient equalities used are H.coefficient_comp and R.cocone; proof
irrelevance identifies the resulting equality witnesses. Cancel the common
invertible comparison to obtain the displayed closure tower equation.
3. Apply the same argument to H.identity. H.unit_normalization identifies the
finite identity comparison with actual multiplication, whose composite with the
extension-composition comparison is the extension unitor. Cancelling it gives
closure_identity. The calculation includes equal adjacent fields and rank zero;
it requires no constructibility statement beyond the supplied raw realization. -/
theorem adic_closure_scalar_coherence (C : Core l T) (B : ScalarData l T C)
    (H : Coherence l T C B) (R : ClosureData l T C B) :
    (∀ {E F G : Padic.FiniteCoefficientFields l (PadicAlgCl l)}
      (h : E ≤ F) (k : F ≤ G)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E),
    (pbcDerivedExtend (R.leg G)).map
        ((finiteFunctor l T C G).map
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).assoc
            h k).hom.app K)) ≫
        (closureComparison l T C B R (h.trans k)).hom.app K =
      (closureComparison l T C B R k).hom.app
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).T h).obj
            K) ≫ (closureComparison l T C B R h).hom.app K) ∧
    (∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E),
    HEq ((closureComparison l T C B R (le_refl E)).hom.app K)
      ((pbcDerivedExtend (R.leg E)).map
        ((finiteFunctor l T C E).map
          ((GeneralAlgebraicallyClosedCoefficients.unitor l (PadicAlgCl l) T E).hom.app K))))
      := by sorry

end WeilConjectures.AdicFiniteRealization
