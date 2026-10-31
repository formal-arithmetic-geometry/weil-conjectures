/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagram.FiniteAdjunctionDiagramData

/-! The dual formula as an actual map of derived coefficient systems. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
variable {l E D hl f c}

variable (l E D hl f c)

variable (SX : CoefficientDerivedSystemCalculus l E X)
  (SZ : CoefficientDerivedSystemCalculus l E c.Z)
  (SY : CoefficientDerivedSystemCalculus l E Y)
  (SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k)))
/-- The system dual formula, with its absolute structural trace and finite pairing.
Source: realization node steps 10--13; blueprint finite exceptional proof
(blueprint: lem-sf-finite-adjunction-system-duality).
Proof: finite Verdier preservation and its quotient tensor-Hom comparison show
that internal dual preserves normalized finite-Tor systems. Pullback has the
same normalization and levelwise preservation. Compose proper/open system
functors to obtain the compact-support compositor for structure maps. Its
finite values are the canonical compositors, so it is invertible. Form the
structural trace by the absolute counit. Projection, the exceptional counit,
and tensor-Hom transposition now define the dual-formula map on systems.
Its evaluated map is the finite dual-formula transpose, because every arrow
is the prescribed projection, evaluation, or counit. Finite biduality and
internal adjunction make those values invertible; evaluation conservativity
makes the system map invertible. The defining uncurry equation is the pairing
field, before evaluation. Evaluation of the compositor and absolute counit
gives finiteTrace, and evaluation of the transpose gives finiteFormula. -/
theorem finiteAdjunctionSystemDuality
    (hX : CoefficientDerivedSystemCoherence l E X SX)
    (hZ : CoefficientDerivedSystemCoherence l E c.Z SZ)
    (hY : CoefficientDerivedSystemCoherence l E Y SY)
    (hS : CoefficientDerivedSystemCoherence l E (Spec (.of D.k)) SS)
    (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
    (tX : RingedDerivedTensorCoherence.{u + 1, u, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X) SX.systemClosed SX.systemTensorModel βX)
    (tY : RingedDerivedTensorCoherence.{u + 1, u, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) SY.systemClosed SY.systemTensorModel βY)
    (r : Realization l E D hl f c SX SZ SY)
    (g : Geometry l E f SX SY)
    (aX : DualizingOperation (D := D) (hl := hl) X SX SS)
    (aY : DualizingOperation (D := D) (hl := hl) Y SY SS) :
    Nonempty (Duality r aX aY βY g) := by
  sorry

end WeilConjectures.FiniteAdjunctionDiagram
