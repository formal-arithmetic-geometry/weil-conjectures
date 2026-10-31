/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleStrictLocalRestrictionProperties
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorStalk
public import WeilConjectures.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import WeilConjectures.SixFunctors.BaseChange.Derived

/-! # Module-valued strict-local derived restriction

Source: blueprint `def-pur-module-strict-local-restriction`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The existing finite-limit structure on module geometric stalks, extracted from the
unique restriction theorem.
Source: Stacks Project, Tags 03Q9 and 03QO; relative Kummer proof, Step 2.
(blueprint: def-pur-module-strict-local-restriction). -/
instance moduleStrictLocalStalk_limits (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :
    PreservesFiniteLimits
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)) :=
  (moduleStrictLocalRestriction_properties A s).1

/-- The existing finite-colimit structure on sections of the small strict-local model,
extracted from the restriction-properties theorem.
Source: Stacks Project, Tags 03Q9 and 03QO; relative Kummer proof, Step 2.
(blueprint: def-pur-module-strict-local-restriction). -/
instance moduleStrictLocalSections_exact (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :
    PreservesFiniteColimits
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)) :=
  (moduleStrictLocalRestriction_properties A s).2.1

/-- The unique module-valued germ restriction with the pointed-neighbourhood section
restrictions. The existence theorem determines the transformation uniquely, so its
choice postpones only a proof, not unspecified data.
Source: Stacks Project, Tags 03Q9 and 03QO; relative Kummer proof, Step 2.
(blueprint: def-pur-module-strict-local-restriction). -/
noncomputable def moduleStrictLocalRestriction (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :
    (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A)
          (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          (ModuleCat.{u + 1} A) :=
  Classical.choose (moduleStrictLocalRestriction_properties A s).2.2

/-- Derive the uniquely specified module germ restriction. Exact stalks and exact
strict-local sections give the canonical exact-functor comparisons; the composition
comparison separates inverse image from derived sections.
Source: Stacks Project, Tags 03Q9 and 03QO; relative Kummer proof, Step 2.
(blueprint: def-pur-module-strict-local-restriction). -/
noncomputable def moduleStrictLocalDerivedRestriction
    (A : Type (u + 1)) [CommRing A] {B : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B) :
    (Scheme.pointSmallEtale s).sheafFiber.mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} A)
          (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus :=
  (Scheme.pointSmallEtale s).sheafFiber.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv ≫
    Functor.rightDerivedFunctorPlusNatTrans (moduleStrictLocalRestriction A s) ≫
    (upperStar (ModuleCat.{u + 1} A)
        (Scheme.strictHenselizationStructuralMap s) ⋙
      Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom ≫
    (Functor.mapDerivedCategoryPlusCompIso _ _).hom ≫
    Functor.whiskerLeft
      (upperStar (ModuleCat.{u + 1} A)
        (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv

/-- Canonical strict-local comparison: derived germ restriction, derived exchange for
the actual pullback square, Leray, and the specified coefficient isomorphism.
No invertibility of this composite is asserted.
Source: Stacks Project, Tags 03Q9 and 03QO; relative Kummer proof, Step 2.
(blueprint: def-pur-module-strict-local-restriction). -/
noncomputable def moduleStrictLocalTheta
    (A : Type (u + 1)) [CommRing A] {X B : Scheme.{u}} (f : X ⟶ B)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B)
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K' : DerivedCategory.Plus
      (Sheaf (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} A)))
    (e : (upperStar (ModuleCat.{u + 1} A)
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus.obj
          K ≅ K') :
    (Scheme.pointSmallEtale s).sheafFiber.mapDerivedCategoryPlus.obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj K) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.obj K' :=
  (moduleStrictLocalDerivedRestriction A s).app
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj K) ≫
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
      ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback f
          (Scheme.strictHenselizationStructuralMap s)).toCommSq).app K) ≫
    (moduleLerayPlus A (pullback.snd f
      (Scheme.strictHenselizationStructuralMap s))).hom.app
      ((upperStar (ModuleCat.{u + 1} A)
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus.obj
          K) ≫
    (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
      (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map e.hom

end AlgebraicGeometry.Etale
