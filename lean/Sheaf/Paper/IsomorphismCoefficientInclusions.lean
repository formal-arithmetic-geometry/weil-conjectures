/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Coefficient inclusions with explicit field-induced structures -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients
  (Index Coefficient coefficientInclusion coefficientInclusion_laws)

/-- Cache the existing coefficient inclusion with field-induced semiring structures.
Source: the finite-coefficient models of the current blueprint automorphism pullback;
`AlgebraicallyClosedCoefficients.coefficientInclusion` is used verbatim.
(blueprint: def-pod-isomorphism-coefficient-inclusions). -/
def isomorphismCoefficientInclusion
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E L : Index l Ω) (h : E ≤ L) :
    @AlgHom ℚ_[l] (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      inferInstance
      (show Field (Coefficient.{u} l Ω E) from inferInstance).toSemiring
      (show Field (Coefficient.{u} l Ω L) from inferInstance).toSemiring
      inferInstance inferInstance := coefficientInclusion l Ω E L h

/-- Identity and composition for the same field-structured inclusions.
Source: the existing coefficient-inclusion laws. Proof: apply those laws directly;
the map and algebra structures are definitionally equal presentations of the same data.
(blueprint: def-pod-isomorphism-coefficient-inclusions). -/
theorem isomorphismCoefficientInclusion_laws
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    (∀ E : Index l Ω, isomorphismCoefficientInclusion.{u} l Ω E E le_rfl =
      AlgHom.id ℚ_[l] (Coefficient.{u} l Ω E)) ∧
    (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M),
      (isomorphismCoefficientInclusion.{u} l Ω L M k).comp
        (isomorphismCoefficientInclusion.{u} l Ω E L h) =
      isomorphismCoefficientInclusion.{u} l Ω E M (h.trans k)) := by
  exact coefficientInclusion_laws.{u} l Ω

section
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The integral balancing associator, conjugated by the existing completion comparison
and the actual equality of the small coefficient inclusions. It introduces no new map.
Source: blueprint scalar-tower clause; prop-weil-pbc-scalar-extension
(blueprint: def-pod-isomorphism-coefficient-inclusions). -/
def isomorphismCoefficientIntegralAssociator (W : Scheme.{u})
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E L h ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W L M k ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E M (h.trans k) :=
  sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (isomorphismCoefficientInclusion l Ω E L h) W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω M) (isomorphismCoefficientInclusion l Ω L M k) ≪≫
    eqToIso (congrArg
      (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω M) · W)
      ((isomorphismCoefficientInclusion_laws.{u} l Ω).2 E L M h k))

/-- Identity scalar extension with its existing completion-unit normalization.
Source: blueprint identity-extension clause; lem-weil-scalar-extension-composition
(blueprint: def-pod-isomorphism-coefficient-inclusions). -/
def isomorphismCoefficientIntegralUnitor (W : Scheme.{u}) (E : Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E E le_rfl ≅
      𝟭 (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W) :=
  eqToIso (congrArg
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω E) · W)
    ((isomorphismCoefficientInclusion_laws.{u} l Ω).1 E)) ≪≫
  sfIntegralScalarUnit l (Coefficient.{u} l Ω E) W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime))

end

end WeilConjectures
