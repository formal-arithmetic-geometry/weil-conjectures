/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Growth
import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
import WeilConjectures.AlgebraicGeometry.RealCondensedFibre.RealCondensedFibreFunctoriality
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.GroupTheory.WeilGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Separable
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import Mathlib.CategoryTheory.Filtered.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentLisse
import WeilConjectures.AlgebraicGeometry.LisseFiniteDescent
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealWeights
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2PurityBridge
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2ModulePurityRigidity

/-!
# L² growth and pure weights

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-purity-real-sheaves/sec-weights-and-the-growth-of-squared-traces/
sk-thm-wrp-l2-dictionary/_section.md and sk-thm-wrp-l2-dictionary.proof.md
(blueprint: sk-thm-wrp-l2-dictionary).

A Weil sheaf is a bounded constructible condensed Weil complex concentrated in
degree zero. Its canonical zeroth Weil cohomology module supplies the lissity
and punctual purity predicates. The conclusion uses the released logarithmic
parameter, including its extended-real endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

/-- The growth parameter of a nonzero pure lisse Weil sheaf is its pure weight.

Source: latest blueprint, sk-thm-wrp-l2-dictionary, entire theorem and proof
(blueprint: sk-thm-wrp-l2-dictionary).

Proof: for a degree-zero complex the alternating trace is the ordinary trace,
so its energy is the native module energy and the supremum parameter agrees
with the logarithmic growth parameter. For a real sheaf the tensor-square
Euler product, surviving pole, and radius computation of thm-wf-l2-dictionary
give the equality. For a general pure sheaf, twist by the constant line B_b
with norm(iota b) = q^(-w/2). The twisted sheaf is lisse, nonzero and pure of
weight zero. Its real envelope is lisse, nonzero, real and pure of weight zero,
so its growth parameter is zero by the real case. The twist translates the
parameter by -w. The envelope traces are twice the real parts of the twisted
traces, hence its energies are at most four times the twisted energies.
Inclusion of positive-limsup parameter sets gives a lower bound zero for the
twist. The pure upper bound gives the reverse inequality. Thus the twisted
parameter is zero; translating back by the finite real w proves the equality.
This argument retains the empty parameter set and both infinite endpoints. -/
theorem growthParameter_eq_of_isPunctuallyPureOfWeight
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsAffine X₀.left] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (G : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (hdegreeZero : DerivedCategory.TStructure.t.heart G.obj.carrier)
    (hne : ¬ IsZero (complexCohomology D l X₀ G 0))
    (hlisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (complexCohomology D l X₀ G 0).carrier)
    (w : ℝ) (hpure : Pure D l X₀ (complexCohomology D l X₀ G 0) ι w) :
    growthParameter D l X₀ hl ι G = (w : EReal) := by
  rw [growthParameter_eq_complexL2Weight D l X₀ hl ι G]
  rw [complexL2Weight_eq_l2Weight_of_heart D l X₀ ι G hdegreeZero]
  exact l2Weight_eq_of_isPunctuallyPureOfWeight D l X₀ ι
    (complexCohomology D l X₀ G 0) hne hlisse w hpure

end WeilConjectures.NativeL2
