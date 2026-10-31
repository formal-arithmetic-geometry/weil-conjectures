/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OpenWeilCoefficientFibres

/-! # Open Weil extension comparison

Source: blueprint lem-zl-quasi-finite, proof (1) and (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
  {U₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [hUsep : IsSeparated U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hXsep : IsSeparated X₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]

include hUsep hXsep

variable (J : sfCommonStageWeilSheaf D l hl U₀ Qbar ⥤
  sfCommonStageWeilSheaf D l hl X₀ Qbar)
  (a : J ⊣ zlWeilPull D l hl Qbar j₀)

include a

/-- Every eigenvalue of an open Weil extension comes from a closed point of the
open with the same residue-field cardinality. This statement has no weight bound.

Source: latest blueprint lem-zl-quasi-finite.proof.md, proof (2), the two cases
for a closed point of the target.
(blueprint: lem-zl-open-weil-punctual-spectrum).

Proof: represent the output Weil sheaf and a given local eigenvector at a finite
coefficient field. If the target point is outside the open, the normalized empty
fibre formula makes this vector space zero after scalar extension, contradicting
the nonzero eigenvector. Otherwise the open embedding lifts the point uniquely.
Its residue map is an isomorphism. The lifted point is closed, since its residue
field is the same finite field as the target point. Consequently the residue
cardinalities agree. Descend the input Weil structure, inverse, and its comparison
to the given output model to a common finite coefficient enlargement; the finite
Weil-diagram descent theorem supplies this finite model. The normalized open unit
and the residue-compatible local Frobenius comparison give a conjugacy of the
local operators. Apply its inverse to the nonzero eigenvector; scalar extension
and the conjugacy preserve the eigenvalue and nonvanishing. This supplies the
finite-stage witness for SfPunctualEigenvalue of the input. The argument uses no
complex embedding and includes arbitrary eigenvalues, zero sheaves, the empty
open, and the identity immersion. -/
theorem openWeilPunctualSpectrum
    (F : sfCommonStageWeilSheaf D l hl U₀ Qbar)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left}) (α : Qbar)
    (hα : SfPunctualEigenvalue D l hl Qbar X₀ (J.obj F) x α) :
    ∃ z : {z : U₀.left // z ∈ closedPoints U₀.left},
      Nat.card (U₀.left.residueField z.val) = Nat.card (X₀.left.residueField x.val) ∧
      SfPunctualEigenvalue D l hl Qbar U₀ F z α := by sorry

end WeilConjectures
