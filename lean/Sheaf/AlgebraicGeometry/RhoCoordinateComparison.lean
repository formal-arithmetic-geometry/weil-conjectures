module

public import Sheaf.AlgebraicGeometry.RhoSectionModuleData
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData

/-! # Comparison of coordinate scalar structures

Source: Milne, Algebraic Groups, Section 3a: global functions on a scheme over F.
(blueprint: def-sfb-rho-coordinate-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.RhoSection

/-- The two coordinate scalar structures pull back along the same structure map.
Source: Milne, Section 3a (blueprint: def-sfb-rho-coordinate-comparison).

Proof: unfold the relative Gamma functor algΓ. Its scalar ring homomorphism is
S.X.hom.appTop composed with the inverse of ΓSpecIso F. The canonical Hopf
algebra uses the same scalar homomorphism, through Scheme.Over. Unfolding its
underlying algebra gives that same composite. Evaluate both composites at a. -/
theorem coordinateScalarCompatibility {F : Type u} [Field F]
    (S : Grp (Over (Spec (.of F)))) [IsAffine S.X.left] (a : F) :
    algebraMap F (RationalHighestWeight.coordinateAlgebra S) a =
      algebraMap F (Coordinate S.X) a := by
  sorry

/-- The identity on global regular functions, comparing the relative-Gamma and
coordinate-Hopf algebra interfaces. Both scalar maps pull back along S to Spec F.
Source: Milne, Section 3a (blueprint: def-sfb-rho-coordinate-comparison). -/
def coordinateComparison {F : Type u} [Field F]
    (S : Grp (Over (Spec (.of F)))) [IsAffine S.X.left] :
    RationalHighestWeight.coordinateAlgebra S ≃ₐ[F] Coordinate S.X :=
  { RingEquiv.refl _ with commutes' := coordinateScalarCompatibility S }

end AlgebraicGeometry.RhoSection
