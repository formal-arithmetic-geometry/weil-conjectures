/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.RationalWeilPurityNaturalityMate

/-! # Ambient compact-support Frobenius normalization

This is the strict ambient comparison used to remove the constructible wrapper
from the compact-support Frobenius normalization.
(blueprint: lem-pur-frobenius-compact-integral-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Ambient compact-support normalization before the constructible wrapper.

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
`thm-pur-weil-equivariance-of-purity-and-trace.proof.md`, Step 2.

Proof: compare the normalized proper mate and inverse open mate on the whole
quotient system.  The quotient-unit formulas for the completion-to-ordinary
maps identify the two mate factors with the corresponding outer factors in
`RationalWeilPurity.integralExchange`.  The projection-normalized compact
realization identifies the middle realization and its inverse, so they cancel.
Pasting the three equalities gives the displayed ambient component equality;
the constructible inclusion is not used at this stage.  Empty schemes reduce
to the unique zero maps and identity compactifications to the mate triangle
identities.
(blueprint: lem-pur-frobenius-compact-integral-ambient-normalization).

Proof: apply the normalized proper/open mate calculation and projection-normalized
realization cancellation on the whole quotient system, then evaluate at `M`; no
finite-stage replacement is chosen. -/
theorem frobeniusCompactIntegral_ambient_normalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c₀ : Compactification f₀.left)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :
    HEq ((FrobeniusExchange.frobeniusCompactIntegral D l hl E f₀ c₀).app M).hom
      (RationalWeilPurity.integralExchange D l hl f₀ E c₀ M).hom.hom := by
  sorry

end WeilConjectures
