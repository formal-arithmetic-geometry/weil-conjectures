/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels

/-!
# Sheaf support and normalized coordinate germ comparisons

Source: Stacks Project, Tag 09XP, and steps 1, 5, 7 of the relative normal-slice
argument (blueprint: def-pur-etale-coordinate-support).

The sheaf support functor is the kernel of the open-complement adjunction unit.
The supported-stalk and global-to-stalk maps are fixed by their kernel-inclusion
equations; their derived transformations use the published derived base-change API.

## Main declarations

- `Etale.coordinateSupportSheaf`: the sheaf kernel, with its inclusion.
- `Etale.coordinateSupportedStalkDerivationIso`: the stalk of derived support.
- `Etale.coordinateDerivedGlobalToStalk`: the normalized derived global-to-stalk comparison.
- `Etale.coordinateDerivedGlobalToStalk_restriction`: its etale restriction square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

attribute [instance] CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]

/-- The sheaf of sections with closed support, defined by its actual kernel.
Source: Stacks 09XP, subsheaf H_Z (blueprint: def-pur-etale-coordinate-support). -/
def coordinateSupportSheaf (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i.openComplement.ι).unit

/-- The supported-sheaf inclusion is the canonical kernel inclusion.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support). -/
def coordinateSupportInclusion {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    coordinateSupportSheaf A i ⟶ 𝟭 _ :=
  kernel.ι _

/-- Additivity of the support kernel, needed for its derived functor.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support).
Proof: compose the addition equation with the monic kernel inclusion; the remaining
identity is additivity of the identity functor. Cancel that inclusion. -/
@[instance] theorem coordinateSupportSheaf_additive {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] : (coordinateSupportSheaf A i).Additive := by
  sorry

/-- The underived supported stalk, using the recorded geometric fibre functor.
Source: Stacks 09XP and the pointed-neighbourhood colimit definition
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateSupportedStalk {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  coordinateSupportSheaf A i ⋙ ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A))

/-- Additivity of the supported stalk.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support).
Proof: the support kernel is additive and the geometric fibre functor is additive;
their composite is therefore additive. -/
@[instance] theorem coordinateSupportedStalk_additive {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : (coordinateSupportedStalk A i t).Additive := by
  sorry

/-- The supported-sheaf functor preserves injectives.
Source: Stacks 09XP, closed-support adjunction, and DAG step 1
(blueprint: def-pur-etale-coordinate-support).
Proof: the support kernel is `i_* i!`. The closed direct image is exact and is right
adjoint to exact inverse image. Thus both `i!` and `i_*` preserve injectives, by
adjunction to exact functors, and so does their composite. -/
@[instance] theorem coordinateSupportSheaf_preservesInjectives {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (coordinateSupportSheaf A i).PreservesInjectiveObjects := by
  sorry

/-- Deriving the supported stalk is canonically the stalk of derived sheaf support.
Source: Stacks 09XP and DAG step 1
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateSupportedStalkDerivationIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ X) :
    (coordinateSupportedStalk A i t).rightDerivedFunctorPlus ≅
      (coordinateSupportSheaf A i).rightDerivedFunctorPlus ⋙
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).mapDerivedCategoryPlus :=
  Functor.rightDerivedFunctorPlusCompIso (coordinateSupportSheaf A i)
      ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)))

/-- The inclusion of supported germs into all germs.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support). -/
def coordinateSupportedStalkInclusion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ X) :
    coordinateSupportedStalk A i t ⟶
      ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)) :=
  Functor.whiskerRight (coordinateSupportInclusion A i) _

/-- Global supported sections are the already recorded kernel-of-restriction functor.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support). -/
abbrev coordinateGlobalSupport {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  Sheaf.supportedSectionsFunctor X.smallEtaleTopology (ModuleCat.{u + 1} A)
    (supportRestrictionArrow i)

/-- Restriction from global sections to a geometric germ, then the actual pullback-stalk
identification. Source: Stacks 09XP and the geometric stalk colimit
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateGlobalGerm {X T : Scheme.{u}} (f : T ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj
        ((upperStar (ModuleCat.{u + 1} A) f).obj F) :=
  (Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber
      (Scheme.Etale.mk (𝟙 X)) (Over.homMk (t ≫ f) (by simp)) F.obj ≫
    (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f t).inv.app F

/-- Pullback of a supported global section is the unique supported germ with the specified
underlying germ. The support equality is the inverse-image condition on closed pairs.
Source: Stacks 09XP, kernel construction (blueprint: def-pur-etale-coordinate-support).
Proof: pull back the restriction equation to the inverse-image complement. The germ
therefore lies in the support kernel. Exactness of the geometric fibre functor
identifies its kernel with the fibre of the kernel sheaf. The kernel universal property
gives existence, naturality, and uniqueness. -/
theorem coordinateGlobalToStalk_existsUnique {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ∃! m : coordinateGlobalSupport A i ⟶
        upperStar (ModuleCat.{u + 1} A) f ⋙ coordinateSupportedStalk A i' t,
      ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        m.app F ≫ (coordinateSupportedStalkInclusion A i' t).app
            ((upperStar (ModuleCat.{u + 1} A) f).obj F) =
          kernel.ι (F.obj.map (supportRestrictionArrow i).op) ≫
            coordinateGlobalGerm A f t F := by
  sorry

/-- The canonical, kernel-normalized map on supported germs, with no arbitrary isomorphism
chosen. Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support). -/
def coordinateGlobalToStalk {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    coordinateGlobalSupport A i ⟶
      upperStar (ModuleCat.{u + 1} A) f ⋙ coordinateSupportedStalk A i' t :=
  (coordinateGlobalToStalk_existsUnique A i i' f hf t).choose

/-- Derive the canonical pullback-to-supported-germ map using the right-derived base-change
construction. Source: Stacks 09XP and DAG steps 1, 5
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateDerivedGlobalToStalk {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (coordinateGlobalSupport A i).rightDerivedFunctorPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙
        (coordinateSupportedStalk A i' t).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := coordinateGlobalSupport A i) (G' := coordinateSupportedStalk A i' t)
      (β := upperStar (ModuleCat.{u + 1} A) f) (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ coordinateGlobalToStalk A i i' f hf t)

/-- Restriction of a supported germ is uniquely fixed by restriction of the underlying
germ. Source: Stacks 09XP and DAG steps 5, 7
(blueprint: def-pur-etale-coordinate-support).
Proof: the inverse-image support condition identifies the two complement kernels.
Exact stalks preserve this kernel. The pullback-stalk isomorphism carries one inclusion
to the other; factor through the kernel and cancel its monic inclusion for uniqueness. -/
theorem coordinateStalkRestriction_existsUnique {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (e : T ⟶ X) [Etale e]
    (he : Set.range i'.base = e.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ∃! m : coordinateSupportedStalk A i (t ≫ e) ⟶
        upperStar (ModuleCat.{u + 1} A) e ⋙ coordinateSupportedStalk A i' t,
      m ≫ Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) e)
          (coordinateSupportedStalkInclusion A i' t) =
        coordinateSupportedStalkInclusion A i (t ≫ e) ≫
          (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) e t).inv := by
  sorry

/-- The actual restriction map of supported germs, fixed by its inclusion equation.
Source: Stacks 09XP (blueprint: def-pur-etale-coordinate-support). -/
def coordinateStalkRestriction {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (e : T ⟶ X) [Etale e]
    (he : Set.range i'.base = e.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    coordinateSupportedStalk A i (t ≫ e) ⟶
      upperStar (ModuleCat.{u + 1} A) e ⋙ coordinateSupportedStalk A i' t :=
  (coordinateStalkRestriction_existsUnique A i i' e he t).choose

/-- Derive literal etale restriction on supported germs.
Source: Stacks 09XP and DAG step 7
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateDerivedStalkRestriction {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (e : T ⟶ X) [Etale e]
    (he : Set.range i'.base = e.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (coordinateSupportedStalk A i (t ≫ e)).rightDerivedFunctorPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategoryPlus ⋙
        (coordinateSupportedStalk A i' t).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := coordinateSupportedStalk A i (t ≫ e))
      (G' := coordinateSupportedStalk A i' t)
      (β := upperStar (ModuleCat.{u + 1} A) e) (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ coordinateStalkRestriction A i i' e he t)

/-- The exact inverse-image composition isomorphism on bounded-below complexes.
Source: inverse-image composition and DAG step 7
(blueprint: def-pur-etale-coordinate-support). -/
def coordinateDerivedPullbackComp {X T V : Scheme.{u}} (f : T ⟶ X) (e : V ⟶ T) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategoryPlus ≅
      (upperStar (ModuleCat.{u + 1} A) (e ≫ f)).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (upperStar (ModuleCat.{u + 1} A) f) (upperStar (ModuleCat.{u + 1} A) e)).symm ≪≫
    (Functor.mapDerivedCategoryPlusNatIso
      (upperStarComp (ModuleCat.{u + 1} A) e f (e ≫ f) rfl)).symm

/-- The coordinate comparison commutes with every further etale restriction.
The three support equalities just express the three inverse-image closed pairs.
Source: Stacks 09XP and DAG step 7
(blueprint: def-pur-etale-coordinate-support).
Proof: before deriving, both composites have the same underlying global germ by the
composition law for pullback stalks. Uniqueness in the two kernel factorizations gives
the same natural transformation. Derive this equation; the derived composition
isomorphism is the specified exact inverse-image composition, giving this square. -/
theorem coordinateDerivedGlobalToStalk_restriction
    {Z X Z' T Z'' V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (i'' : Z'' ⟶ V) [IsClosedImmersion i'']
    (f : T ⟶ X) (e : V ⟶ T) [Etale e]
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    (he : Set.range i''.base = e.base ⁻¹' Set.range i'.base)
    (hef : Set.range i''.base = (e ≫ f).base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ V) :
    coordinateDerivedGlobalToStalk A i i' f hf (t ≫ e) ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus
        (coordinateDerivedStalkRestriction A i' i'' e he t) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (coordinateDerivedPullbackComp A f e).hom
        (coordinateSupportedStalk A i'' t).rightDerivedFunctorPlus =
      coordinateDerivedGlobalToStalk A i i'' (e ≫ f) hef t := by
  sorry

end AlgebraicGeometry.Etale
