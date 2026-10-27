module

public import Sheaf.AlgebraicGeometry.StrictLocalSectionCone
public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.BaseChange.Derived

/-! # Module-valued restriction from a geometric stalk to the strict localization

Source: Stacks Project, Tag 03Q9, construction of the restriction map
(blueprint: def-pur-module-strict-local-section-restriction).
The existing abelian interface is retained. The same germ components specify its
module-valued version on the small affine-neighbourhood model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Modules in the coefficient universe have all site-sized limits.
Source: Stacks Tag 03Q9 (blueprint: def-pur-module-strict-local-section-restriction). -/
instance moduleStrictLocalModuleLimits (A : Type (u + 1)) [CommRing A] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} A) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

/-- The existing module stalk is additive.
Source: Stacks Tag 03Q9 (blueprint: def-pur-module-strict-local-section-restriction). -/
instance moduleStrictLocalStalk_additive (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)).Additive :=
  (Scheme.pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} A)

/-- Module sections restrict along the pointed-neighbourhood limit leg, after the
inverse-image unit. Source: Stacks Tag 03Q9
(blueprint: def-pur-module-strict-local-section-restriction). -/
def moduleStrictLocalSectionRestriction (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B)
    (F : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (Scheme.strictHenselizationStructuralMap s)).unit.app F).hom.app
      (op ((Scheme.AffineEtale.Spec B).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)) ≫
    ((upperStar (ModuleCat.{u + 1} A)
      (Scheme.strictHenselizationStructuralMap s)).obj F).obj.map
        (strictLocalNeighbourhoodSection s j).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale
        (Scheme.strictHenselizationScheme s))).inv.app _


end AlgebraicGeometry.Etale
