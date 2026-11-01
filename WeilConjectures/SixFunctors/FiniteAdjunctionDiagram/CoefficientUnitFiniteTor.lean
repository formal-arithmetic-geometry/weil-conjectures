/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagram.FiniteAdjunctionCoefficientUnitData

/-! Finite-Tor constructibility of the coefficient unit at each level. -/

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

/-- Every evaluation of the concrete coefficient unit is finite-Tor constructible.
Source: Stacks 06YY; finite adjunction realization proof step 9
(blueprint: lem-sf-coefficient-unit-finite-tor).
Proof: exact evaluation commutes with the degree-zero single functor. Evaluation
of the regular sequence-ring module is the regular module over the finite
coefficient sheaf, by the identity on sections. This is the constant free module
of rank one. Its only cohomology is in degree zero and is locally constant with
finite stalks; hence it is constructible. Tensoring with this free module is
the identity, so its Tor interval is [0,0]. Transport these predicates through
the evaluation/single comparison. This works on the empty scheme and on every
scheme, with no geometric finiteness hypothesis. -/
theorem coefficientUnit_finiteTor (W : Scheme.{u}) (n : ℕ) :
    FiniteExceptional.domain l E W n
      ((coefficientSequenceDerivedEvaluation l E W n).obj
        (coefficientUnit (l := l) (E := E) W)) := by
  sorry

end WeilConjectures.FiniteAdjunctionDiagram
