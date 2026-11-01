/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectReductionHomEquiv
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement

/-! # Homotopy-level counit coherence for the perfect reduction tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Homotopy-level specialization of the scalar-extension counit composition square.

Source: `lem-pe-internal-scalar-extension-counit-composition` together with the
comparison definition `def-pe-internal-perfect-reduction-hom-equiv`.
(blueprint: lem-pe-internal-perfect-reduction-counit-coherence).

Proof: unfold the ordinary reduction step and the derived reduction comparison,
then apply the generic counit composition identity to the two quotient maps.
The remaining conversion from the chain quotient to the homotopy quotient is the
canonical quotient comparison naturality. This statement is strictly below the
homotopy comparison theorem: it contains no endomorphism or localization data. -/
theorem internalPerfectReduction_counit_coherence
    (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) (n : ℕ) :
    let F := Mod.extendScalars (AdicCompletion.transition l E W n)
    let T := internalPerfectScalarModel l E W P
    let α := AdicCompletion.reductionComp l E W n
    let γ := internalPerfectReductionOrdinaryIso l E W P a b ha hb hfree
    let ε := F.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (internalPerfectOrdinaryReduction l E W P (n + 1)))
    let H := HomotopyCategory.quotient
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (AdicCompletion.finiteRing l E W n)) (.up ℤ)
    let a₀ := internalPerfectOrdinaryReductionStep l E W P n
    let δ := ε ≫ DerivedCategory.Qh.map (H.map a₀.hom)
    α.hom.app T ≫ (γ n).hom = F.leftDerivedFunctor.map (γ (n + 1)).hom ≫ δ := by
  sorry

end AlgebraicGeometry.ProEtale
