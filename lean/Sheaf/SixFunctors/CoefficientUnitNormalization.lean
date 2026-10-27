/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData

/-! Normalization of the actual coefficient unit. -/

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

/-- The regular sequence-ring module in degree zero has derived quotient transitions.
Source: Stacks 06YY and 0941; finite adjunction realization proof step 9
(blueprint: lem-sf-coefficient-unit-normalization).
Proof: evaluation of the regular sequence module is the regular finite module.
Its horizontal restriction is the quotient ring homomorphism on every section.
The regular module is flat, so derived extension along this quotient is ordinary
extension, and multiplication identifies it with the target regular module.
The universal extension/restriction adjunction then identifies precomposition by
this actual transition with a bijection into every derived target. These are
exactly the bijections in IsNormalizedCoefficientSequence, for all m >= n,
including the identity quotient. -/
theorem coefficientUnit_normalized (W : Scheme.{u}) :
    IsNormalizedCoefficientSequence l E W (coefficientUnit (l := l) (E := E) W) := by
  sorry

end WeilConjectures.FiniteAdjunctionDiagram
