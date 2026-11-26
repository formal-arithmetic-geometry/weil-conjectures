/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientPullbackReduction
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

/-! # Finite regular coefficient comparison data

The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` of the derived pullbacks with finite
regular coefficients, used for the constant-sheaf case of the Grothendieck–Lefschetz trace
formula.

## Implementation details

The regular complex and c, kappa and lambda below are transparent aliases of the
published constructions, not new choices or copies. Composition is the prescribed
ringed-site compositor, transported by the published unit-preserving coordinate maps.
The middle factor of the compositor is exactly the specialization of the ringed-site
compositor for pro-étale derived pullbacks; the other factors are the uniquely
unit-preserving change of presentation, descended termwise. In particular this does not
introduce an independently chosen intrinsic compositor.

## References

* [Stacks, Tags 03D6 and 0D6D]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` of the finite derived
pullbacks at level `m`, in the intrinsic pullback coordinates. -/
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
