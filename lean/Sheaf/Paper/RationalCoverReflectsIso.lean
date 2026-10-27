/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.CoefficientDualModelTransport

/-! # Detecting rational constructible isomorphisms on the coefficient site -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Ambient rational slice restrictions jointly reflect constructible isomorphisms.
Source: blueprint prop-sf-dualizable-hom, steps 11--13
(blueprint: lem-sf-rational-cover-reflects-iso).

Proof: clear the denominator of f and take the integral constructible cone of
its numerator. Exactness identifies the local cones with its localized slice
restrictions, so the hypothesis makes them zero. Since X is separated and of
finite type, choose a finite affine refinement of this covering. Apply
sfRationalLocalGlobalPowerTorsion to get one power annihilating every cohomology
sheaf of the cone. Its integral constructibility supplies a uniform interval
for the finite reductions. Derived completeness and the Roos long exact
sequence give a finite cohomological interval for the cone itself (with at
most one extra degree). Apply sfRationalBoundedConeTorsion to kill its identity
by a uniformizer power. Its rationalization is zero, so the numerator and f
are invertible. The empty scheme and zero cone are included in the argument;
no infinite supremum of torsion exponents is taken. -/
theorem rationalCover_reflectsIso
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    {K M : sfRationalConstructibleCategory C.l E X.obj.left} (g : K ⟶ M)
    (h : ∀ V : X.obj.left.ProEt, ∃ R : Sieve V,
      R ∈ Scheme.ProEt.topology X.obj.left V ∧
      ∀ (U : X.obj.left.ProEt) (f : U ⟶ V), R f →
        IsIso ((IntegralOnSlice.restrictionRational C.l E X.obj.left
          (U := none) (V := some U) PUnit.unit).map
          ((CoefficientDualModels.stageInclusion C.l E X.obj.left).map g))) :
    IsIso g := by sorry

end WeilConjectures
