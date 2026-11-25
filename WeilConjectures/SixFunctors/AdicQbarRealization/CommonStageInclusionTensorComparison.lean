/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

/-! # Canonical common-stage inclusion tensor comparison

## Main definitions and statements

- `stageTensor_existsUnique`: normalization by the existing common-stage comparison.
- `stageTensor`: that uniquely specified inclusion tensorator.

## Implementation details

The normalization `stageTensorFormula` is stated as a `HEq` to a fixed composite, which retains
the literal pair-object transports instead of asking elaboration to expand them. Since every
factor of the composite is canonical, the same `HEq` gives both existence and uniqueness, so
the choice in `stageTensor` introduces no unspecified comparison map.

## References

- BS, Remark 6.8.15 (common-stage tensor convention).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.all false

universe u w
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.AdicQbarRealization

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The normalization of the inclusion tensorator at `E`: it is the inverse of the
common-stage comparison at `E`, followed by the normalized scalar unitor on both inputs. -/
def stageTensorFormula (Ω : Type w) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] [∀ x : X, Invertible (l : X.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K L : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X)
    (candidate : (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E).obj
        ((rationalDerivedTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X).obj (K, L)) ≅
      (commonStageDerivedTensor l Ω X).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E).obj K,
         (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := X) E).obj L)) : Prop :=
  HEq candidate (
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E
    let P := I.obj K
    let Q := I.obj L
    let h : (commonStageTensorObject l Ω X P Q).stage ≤ E := by
      change E.val ⊔ E.val ≤ E.val
      exact sup_le le_rfl le_rfl
    let e := (operationStageTransitionIso l Ω X E E le_rfl) ≪≫
      GeneralAlgebraicallyClosedCoefficients.unitor l Ω X E
    ((eqToIso ((commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 P Q)) ≪≫
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).isoToStage
        (commonStageTensorObject l Ω X P Q) h ≪≫
      I.mapIso ((commonStageTensorComparison l Ω X P Q E h) ≪≫
        (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X).mapIso
          (Iso.prod (e.app K) (e.app L)))).symm
)

/-- There is a unique tensorator satisfying the normalization `stageTensorFormula`. -/
theorem stageTensor_existsUnique (Ω : Type w) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] [∀ x : X, Invertible (l : X.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K L : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X) :
    ∃! e : (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E).obj
        ((rationalDerivedTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X).obj (K, L)) ≅
      (commonStageDerivedTensor l Ω X).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E).obj K,
         (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := X) E).obj L), stageTensorFormula l X Ω E K L e := by
  unfold stageTensorFormula
  refine ⟨_, HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- The common-stage inclusion tensorator, the unique isomorphism satisfying
`stageTensorFormula`. -/
def stageTensor (Ω : Type w) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] [∀ x : X, Invertible (l : X.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K L : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E).obj
        ((rationalDerivedTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X).obj (K, L)) ≅
      (commonStageDerivedTensor l Ω X).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E).obj K,
         (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := X) E).obj L) :=
  (stageTensor_existsUnique l X Ω E K L).exists.choose

end WeilConjectures.AdicQbarRealization
