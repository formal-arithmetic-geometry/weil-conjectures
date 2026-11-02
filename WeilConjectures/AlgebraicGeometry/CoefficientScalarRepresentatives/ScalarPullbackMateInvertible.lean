/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Invertibility of the canonical inverse scalar/pullback mate

Source: scalar-six pullback proof (1), Stacks 06YY, 07A4 and 0G7E;
orientation base-change factors proof (1)
(blueprint: lem-sfb-proetale-scalar-pullback-mate-invertible).

The restriction squares below are obtained termwise from the ordinary canonical
squares and transported through the exact geometric derived comparisons.
The scalar adjunctions are fixed by CoefficientScalarRepresentatives.adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.CoefficientScalarRepresentatives

/-- The inverse scalar mate on the small pro-etale site is invertible for every ring map.
Source: scalar-six pullback proof (1), Stacks 06YY, 07A4 and 0G7E
(blueprint: lem-sfb-proetale-scalar-pullback-mate-invertible).

Proof: the ordinary restriction/pullback square is conjugate to the sectionwise
coextension/direct-image identity. Iterated mates and the restriction/coextension
triangle identify its inverse scalar mate with the canonical ordinary tensor
comparison, which is invertible. Pullback preserves flat-term K-flat resolutions
by the local relation criterion under representably flat base change. Compute
the derived mate on these resolutions with the ordinary scalar unit used in
representative. The ordinary tensor comparison and the scalar computation arrows
are invertible there. Uniqueness of scalar left adjoints and the exact geometric
derived comparison transport invertibility to the fixed scalar adjunctions
appearing below. Every unbounded object has such a resolution. No coefficient
flatness, finiteness, or boundedness assumption is needed. -/
theorem proEtaleScalarPullbackMate_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (adjunction (Scheme.ProEt.topology Y) a)
      (adjunction (Scheme.ProEt.topology X) a)).symm
      (TwoSquare.mk _ _ _ _
        (ProEtale.leftDerivedUpperStarRestrictScalarsIso a f).hom)).natTrans) := by
  sorry

end AlgebraicGeometry.CoefficientScalarRepresentatives
