module

public import Sheaf.AlgebraicGeometry.ModuleStrictLocalRestrictionProperties
public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.BaseChange.Derived

/-! # Module-valued restriction from a geometric stalk to the strict localization

Source: Stacks Project, Tag 03Q9, construction of the restriction map
(blueprint: def-pur-module-strict-local-restriction).
The existing abelian interface is retained. The same germ components specify its
module-valued version on the small affine-neighbourhood model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Install the named exact-stalk proof for the derived functor construction.
Source: Stacks Tag 03Q9 (blueprint: def-pur-module-strict-local-restriction). -/
instance moduleStrictLocalStalk_limits (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :
    PreservesFiniteLimits
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)) :=
  (moduleStrictLocalRestriction_properties A s).1

/-- Install the named exact-section proof for the derived functor construction.
Source: Stacks Tag 03QO (blueprint: def-pur-module-strict-local-restriction). -/
instance moduleStrictLocalSections_exact (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :
    PreservesFiniteColimits
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)) :=
  (moduleStrictLocalRestriction_properties A s).2.1

/-- The uniquely specified module germ restriction; no arbitrary map is chosen.
Source: Stacks Tag 03Q9 (blueprint: def-pur-module-strict-local-restriction). -/
def moduleStrictLocalRestriction (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :=
  Classical.choose ((moduleStrictLocalRestriction_properties A s).2.2)

/-- Derive the specified restriction termwise, using exact stalk and strict-local
sections. Source: Stacks Tag 03Q9
(blueprint: def-pur-module-strict-local-restriction). -/
@[irreducible]
def moduleStrictLocalDerivedRestriction (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :=
  ((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} A)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv ≫
    Functor.rightDerivedFunctorPlusNatTrans (moduleStrictLocalRestriction A s) ≫
    (upperStar (ModuleCat.{u + 1} A) (Scheme.strictHenselizationStructuralMap s) ⋙
      Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom ≫
    (Functor.mapDerivedCategoryPlusCompIso _ _).hom ≫
    Functor.whiskerLeft
      (upperStar (ModuleCat.{u + 1} A)
        (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv

/-- The canonical module strict-local comparison: germ restriction, derived exchange,
Leray, and a specified coefficient identification.
Source: Stacks Tag 03Q9 (blueprint: def-pur-module-strict-local-restriction). -/
@[irreducible]
def moduleStrictLocalTheta (A : Type (u + 1)) [CommRing A]
    {X B : Scheme.{u}} (f : X ⟶ B) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K' : DerivedCategory.Plus
      (Sheaf (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} A)))
    (e : (upperStar (ModuleCat.{u + 1} A)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus.obj
        K ≅ K') :=
  (moduleStrictLocalDerivedRestriction A s).app
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj K) ≫
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback f
            (Scheme.strictHenselizationStructuralMap s)).toCommSq).app K) ≫
    (moduleLerayPlus A (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).hom.app _ ≫
    (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
      (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map e.hom

end AlgebraicGeometry.Etale
