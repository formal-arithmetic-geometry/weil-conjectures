/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierExceptional
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierCore
import WeilConjectures.SixFunctors.RationalOperations.RationalDualizingIdentification

/-! # The exceptional origin of the descended dualizing object

Source: blueprint thm-coef-qbar-verdier, proof step 9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] WeilConjectures.CoefQbarTensor
  WeilConjectures.CoefQbarPullback

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition associator unitor)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The descended dualizing object is the exceptional image of the actual
coefficient unit at the structure morphism, with the same finite normalizations.
Source: blueprint thm-coef-qbar-verdier, proof step 9
(blueprint: lem-coef-qbar-verdier-dualizing-descent).

Proof: use the finite exceptional system at the canonical structure-morphism
compactification. RationalOperations identifies each finite dualizing presentation
with its exceptional image of the finite coefficient unit. The normalized finite
coefficient-unit comparisons and the canonical dualizing u maps commute with scalar
extension. The finite isomorphisms and their inverses therefore give mutually inverse
maps on the common-stage category. The base coefficient stage represents the actual
coefficientUnit in the statement. Descend the finite exceptional functors and their
adjunction as in exceptional_descent. Their right functor at this object is thus
isomorphic to B.omega, and their system is precisely the one occurring in each
finite DualizingIdentification. The construction uses the same B.omegaComparison
and the same exceptional scalar comparisons, so no unrelated dualizing object or
exceptional system is introduced. -/
theorem dualizing_descent (B : Duality D l hl Ω X) : Dualizing D l hl Ω X B := by
  obtain ⟨C, hC⟩ := core_descent D l hl Ω (Spec (.of D.k))
  obtain ⟨A, _⟩ := exceptional_descent D l hl Ω X (X ↘ Spec (.of D.k)) B
    (completeCore D l hl Ω (Spec (.of D.k)) C hC) (integralDualizingCompactification D X)
  have finite (E : Index l Ω) := RationalOperations.rationalDualizing_identification
    D l hl X (AuxiliaryClosure.{u} l) A.system (fieldStage l Ω E) (B.finite.omega E)
  refine ⟨A, ?_, finite⟩
  let E := Padic.finiteCoefficientBase l Ω
  obtain ⟨e⟩ := finite E
  exact ⟨(B.omegaComparison E).symm ≪≫ (inclusion E).mapIso e ≪≫
    (A.rightComparison E).app
      (RationalOperations.coefficientUnit l (Coefficient.{u} l Ω E) (Spec (.of D.k)) D hl)⟩

end WeilConjectures.CoefQbarVerdier
