/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Norm
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-! The degree-zero comparison needed by the condensed L² dictionary. -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeL2

/-- The alternating trace energy of a degree-zero heart complex is its native
degree-zero trace energy.

Source: current condensed L² dictionary, degree-zero heart reduction
(blueprint: lem-wrp-condensed-degree-zero-energy).
Proof: the heart condition makes all nonzero homology objects zero. The
alternating closed-point trace therefore has only the degree-zero summand, and
the two energy definitions agree term by term. -/
theorem complexL2Weight_eq_l2Weight_of_heart
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsAffine X₀.left] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (G : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (hdegreeZero : DerivedCategory.TStructure.t.heart G.obj.carrier) :
    complexL2Weight D l X₀ ι G =
      l2Weight D l X₀ ι (complexCohomology D l X₀ G 0) := by
  sorry

end WeilConjectures.NativeL2
