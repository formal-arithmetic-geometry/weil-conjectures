/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Sheaf.Paper.IntegralPullbackStrictRoosData

/-! Scalar-restriction normalization of the strict Roos comparison after localization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcIntegralDatum AlgebraicGeometry.Scheme.completedAdicChangeData
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralPullbackStrictRoos
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The normalized scalar cone comparison localizes to the canonical derived-limit
exchange. Source: the integral tensor-pullback proof, comparison paragraph,
strict refinement steps 6--9; Stacks Tags 0941 and 099N.
(blueprint: lem-sfb-integral-roos-scalar-localization).

Proof: the product and cone coordinate formulas uniquely identify epsilon with the
canonical restriction/Roos comparison followed by Roos of theta. The two kappa maps
are fixed by their equations on ordinary-limit inclusions. On a K-injective tower
resolution those inclusions become isomorphisms, so the equation defining the
canonical restriction/derived-limit exchange is exactly the desired equation after
cancelling them. Naturality extends it along the resolution quasi-isomorphism to
all strict tower complexes. Finally naturality of kappaC moves Roos(theta) to derived
limit of theta. No preservation of K-injectives by restriction is required. -/
theorem integralRoosScalarLocalization
    (e : T l E g ⋙ towerRes l E X ≅ V l E g) (ε : EType l E g)
    (κR : kappaType X (R l E X)) (jR : inclusionType X (R l E X))
    (κC : kappaType X (C l E X)) (jC : inclusionType X (C l E X))
    (hε : IsENormalized l E g e ε)
    (hκR : IsUnitNormalized X (R l E X) κR jR)
    (hκC : IsUnitNormalized X (C l E X) κC jC)
    (P : complexesR l E Y) :
    (res l E X).mapDerivedCategory.map (κR.hom.app ((cxT l E g).obj P)) ≫
        (OrderedExchange.lambda (datum l E) X).hom.app
          (DerivedCategory.Q.obj ((cxT l E g).obj P)) ≫
        (completedRlim X (C l E X)).map
          ((towerRes l E X).mapDerivedCategoryFactors.hom.app ((cxT l E g).obj P)) ≫
        (completedRlim X (C l E X)).map
          (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)) =
      (res l E X).mapDerivedCategoryFactors.hom.app
          (roosF.obj ((cxT l E g).obj P)) ≫
        DerivedCategory.Q.map (ε P).hom ≫ κC.hom.app ((cxV l E g).obj P) := by sorry

end WeilConjectures.IntegralPullbackStrictRoos
