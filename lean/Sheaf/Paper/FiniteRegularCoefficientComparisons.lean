/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.CanonicalCoefficientPullbackReduction
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.Paper.DerivedPullbackTensorHom

/-! # Finite regular coefficient comparison data

Source: Stacks 03D6 and 0D6D; main-20261015, constant-sheaf clause of
prop-every-iterate-trace (blueprint: def-zl-finite-regular-coefficient-comparisons).

The regular complex and c, kappa and lambda below are transparent aliases of the
published constructions, not new choices or copies. Composition is the prescribed
ringed-site compositor, transported by the published unit-preserving coordinate maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing regular complex A_(m+1)[0], with no new construction.
Source: Stacks 03D6, regular module
(blueprint: def-zl-finite-regular-coefficient-comparisons). -/
abbrev finiteRegularCoefficientComplex (Y : Scheme.{u}) (m : ℕ) :=
  canonicalCoefficientFiniteComplex l E Y m

/-- The existing tensor-unit chain map, sending x to x tensor 1.
Source: Stacks 03D6, canonical tensor-unit comparison
(blueprint: def-zl-finite-regular-coefficient-comparisons). -/
abbrev finiteRegularKappa {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (m : ℕ) :=
  canonicalCoefficientFiniteKappaComplex l E g m

/-- The existing multiplication isomorphism, inverse to kappa.
Source: Stacks 03D6, canonical tensor-unit comparison
(blueprint: def-zl-finite-regular-coefficient-comparisons). -/
abbrev finiteRegularLambda {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (m : ℕ) :=
  canonicalCoefficientLambdaFinite l E g m

/-- The existing coefficient structure isomorphism c on the regular complex.
Source: Stacks 03D6, constant-section coefficient map
(blueprint: def-zl-finite-regular-coefficient-comparisons). -/
abbrev finiteRegularComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (m : ℕ) :=
  canonicalCoefficientFiniteComparison l E g m

/-- The prescribed finite compositor in the intrinsic pullback coordinates.
The middle factor is exactly the specialization of the ringed-site compositor in
lem-weil-pbc-proetale-derived-pullback-composition. The other factors are the uniquely
unit-preserving published change of presentation, descended termwise. In particular
this does not introduce an independently chosen intrinsic compositor.
Source: Stacks 0D6D, canonical termwise pullback composition
(blueprint: def-zl-finite-regular-coefficient-comparisons). -/
@[no_expose]
def finiteCanonicalPullbackComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ) :
    finiteDerivedPullback l E m (f ≫ g) ≅
      finiteDerivedPullback l E m g ⋙ finiteDerivedPullback l E m f :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (m + 1))
      (f ≫ g)).symm ≪≫
    integralFiniteCanonicalPullbackComposition l E f g m ≪≫
    Functor.isoWhiskerRight
      (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (m + 1)) g)
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (m + 1)) f) ≪≫
    Functor.isoWhiskerLeft (finiteDerivedPullback l E m g)
      (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (m + 1)) f)

end WeilConjectures
