/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientAction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProperCompactIntegralComparisons
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Intermediate comparisons for proper compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The proper comparison at this coefficient level.
Source: literature/blueprint/latest/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.proof.md, first paragraph
(blueprint: lem-weil-proper-compact-rational-functor-comparison).

Proof: Use the quotient-compatible common-refinement comparison of the two integral
compact-support functors. Tensor each component and its inverse with one in the raw
localized Hom module. Naturality on pure tensors is integral naturality multiplied by
the scalar; bilinearity extends it to finite sums of pure tensors. The integral inverse
equations remain inverse equations after localization, giving a natural isomorphism.
No idempotent completion or choice of integral representative is needed. This also
covers zero objects, the identity compactification and the first positive quotient.
-/
theorem properCompactRationalFunctorComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsProper (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    letI : (Spec (CommRingCat.of D.k)).Over (Spec (CommRingCat.of D.k)) := ⟨𝟙 _⟩
    Nonempty (sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c E ≅ sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsProper (Y ↘ Spec (.of D.k))) E) := by
  classical
  let : (Spec (CommRingCat.of D.k)).Over (Spec (CommRingCat.of D.k)) := ⟨𝟙 _⟩
  let d := Compactification.ofIsProper (Y ↘ Spec (.of D.k))
  obtain ⟨ec⟩ := (properCompactIntegralComparisons D l hl Y c E).1
  obtain ⟨ed⟩ := (properCompactIntegralComparisons D l hl Y d E).1
  let e := ec ≪≫ ed.symm
  let a : sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
      c E ≅ sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
      d E := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ (e.app K))
    (fun f ↦ ObjectProperty.hom_ext _ (e.hom.naturality f))
  let Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  refine ⟨NatIso.ofComponents (fun K ↦ Q.mapIso (a.app K.obj)) ?_⟩
  intro K L f
  let Fc := sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c E
  let Fd := sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) d E
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (finiteFieldDatumPrimeUnit D l hl) c E).1
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (finiteFieldDatumPrimeUnit D l hl) c E).2
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (finiteFieldDatumPrimeUnit D l hl) d E).1
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (finiteFieldDatumPrimeUnit D l hl) d E).2
  change ScalarLocalization.composition _ _ _ _ _ _
      ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E)) ⊗ₜ a.hom.app L.obj)
      ((Fc.mapLinearMap _).baseChange _ f) =
    ScalarLocalization.composition _ _ _ _ _ _
      ((Fd.mapLinearMap _).baseChange _ f)
      ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E)) ⊗ₜ a.hom.app K.obj)
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul r f =>
    simp only [LinearMap.baseChange_tmul, Functor.mapLinearMap,
      ScalarLocalization.composition_tmul, one_mul, mul_one]
    exact congrArg (fun z ↦ r ⊗ₜ z) (a.hom.naturality f)
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]

end WeilConjectures
