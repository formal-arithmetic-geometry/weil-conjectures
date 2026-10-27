module
public import Sheaf.SecSmoothPurity.TransportFiniteEncoding
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-finite-support-encoding). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]

/-- Open extension comparison, the left adjoint mate of the fixed pullback comparison.
Source: Stacks 03CY, 09AF (blueprint: def-pur-transport-finite-support-encoding). -/
def finiteEncodingOpen {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek (Profinite.continuousMapRingObj A) j ⋙
      (finiteEncoding A Y).inverse ≅
    (finiteEncoding A X).inverse ⋙ ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j := by
  let ET := (finiteEncoding A Y).symm
  let EU := (finiteEncoding A X).symm
  let i := (finiteEncodingPull A j).symm
  let k := Iso.isoCompInverse (H := EU) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (Profinite.continuousMapRingObj A) j).comp ET.toAdjunction
  let b := EU.toAdjunction.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- The normalized total direct-image comparison computed on K-injective resolutions.
Source: Stacks 015F (blueprint: def-pur-transport-finite-support-encoding). -/
def finiteEncodingDerivedPush {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (CondensedRing.lowerStar (Profinite.continuousMapRingObj A) f)
    (finiteEncoding A Y).inverse).symm ≪≫
  Functor.rightDerivedFunctorNatIso (finiteEncodingPush A f) ≪≫
  Functor.mapDerivedCategoryCompRightDerivedFunctorIso
    (finiteEncoding A X).inverse
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)

/-- The normalized exact open-extension comparison applied termwise.
Source: Stacks 09AF (blueprint: def-pur-transport-finite-support-encoding). -/
def finiteEncodingDerivedOpen {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  (Functor.mapDerivedCategoryCompIso
    (CondensedRing.openImmersionLowerShriek (Profinite.continuousMapRingObj A) j)
    (finiteEncoding A Y).inverse).symm ≪≫
  Functor.mapDerivedCategoryNatIso (finiteEncodingOpen A j) ≪≫
  Functor.mapDerivedCategoryCompIso (finiteEncoding A X).inverse
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)

/-- The canonical finite encoding comparison of the literal Rp_* j_! composite.
Source: finite section-action realization
(blueprint: def-pur-transport-finite-support-encoding). -/
def finiteEncodingSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (finiteEncodingDerivedPush A c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteEncodingDerivedOpen A c.i) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.ProEtale.PurityTransport
