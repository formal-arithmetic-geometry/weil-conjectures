/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportSources
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-compact-support-coordinates). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The existing derived inverse image, with its ambient categories explicit.
This abbreviation retains the published functor and all its canonical maps.
Source: condensed six-functor conventions
(blueprint: def-pur-transport-compact-support-coordinates). -/
abbrev actualPull
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) :=
  (CondensedRing.upperStar R f).leftDerivedFunctor

/-- The existing derived direct image, with its ambient categories explicit.
This abbreviation retains the published functor and all its canonical maps.
Source: condensed six-functor conventions
(blueprint: def-pur-transport-compact-support-coordinates). -/
abbrev actualPush
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) :=
  (CondensedRing.lowerStar R f).rightDerivedFunctor

/-- The existing derived open extension, with its ambient categories explicit.
This abbreviation retains the published functor and all its canonical maps.
Source: condensed six-functor conventions
(blueprint: def-pur-transport-compact-support-coordinates). -/
abbrev actualOpen
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) :=
  (CondensedRing.openImmersionLowerShriek R f).mapDerivedCategory

/-- The existing scalar-unit mate of inverse image is invertible.
Source: scalar-six pullback, clause (1)
(blueprint: def-pur-transport-compact-support-coordinates).
Proof: ordinary restriction of scalars commutes with exact inverse image by the
coefficient naturality square. Its scalar-adjunction mate is the balanced tensor
map. Resolve by flat-term K-flat complexes; inverse image preserves these and
the balanced map is an isomorphism on their tensor representatives. Localization
therefore makes the existing derived mate an isomorphism, without scalar flatness. -/
theorem scalarPull_isIso {R S : CondensedRing.ScalarSixRing.{u}} (a : R ⟶ S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (CondensedRing.scalarSixPullHom a f) := by
  obtain ⟨C⟩ := CondensedRing.scalarSixPullbackData_exists.{u}
  rw [← C.thetaNormalization a f]
  infer_instance

/-- The isomorphism whose hom is the actual published scalar-unit mate.
Source: scalar-six pullback (blueprint: def-pur-transport-compact-support-coordinates). -/
def scalarPullbackIso {R S : CondensedRing.ScalarSixRing.{u}} (a : R ⟶ S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  letI := scalarPull_isIso a f
  asIso (CondensedRing.scalarSixPullHom a f)

/-- The published exact pullback / total direct-image adjunction.
Source: Stacks 015F (blueprint: def-pur-transport-compact-support-coordinates). -/
def exactAdjunction
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStarLowerStarAdjunction R f).mapDerivedCategoryRightDerivedAdjunction

/-- The proper scalar mate, using the fixed normalized scalar/pullback comparison.
Source: scalar-six direct image (blueprint: def-pur-transport-compact-support-coordinates). -/
def scalarDirectMate {R S : CondensedRing.ScalarSixRing.{u}} (a : R ⟶ S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (mateEquiv (exactAdjunction R.X f) (exactAdjunction S.X f)
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso a f).inv)).natTrans

/-- The canonical compact-support scalar arrow, proper mate after the open factor.
Source: scalar-six compact support (blueprint: def-pur-transport-compact-support-coordinates). -/
def scalarSupportMap {R S : CondensedRing.ScalarSixRing.{u}} (a : R ⟶ S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (cf : Compactification f) :=
  Functor.whiskerLeft (CondensedRing.openImmersionLowerShriek R.X cf.i).mapDerivedCategory
      (scalarDirectMate a cf.g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (CondensedRing.derivedOpenImmersionShriekIso (Λ := R.X) (Λ' := S.X)
        a.hom.hom cf.i).hom (CondensedRing.lowerStar S.X cf.g).rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom

/-- The right-adjoint compositor is the mate of the literal exact-pullback compositor.
Source: direct-image composition (blueprint: def-pur-transport-compact-support-coordinates). -/
def lowerComp
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  conjugateIsoEquiv (exactAdjunction R (f ≫ g))
    ((exactAdjunction R g).comp (exactAdjunction R f))
    (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp R f g) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm

/-- The canonical open-extension compositor is fixed by its two adjunctions.
Source: compact-support composition (blueprint: def-pur-transport-compact-support-coordinates). -/
def openComp
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :=
  Adjunction.leftAdjointUniq
    ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R j).comp
      (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R i))
    ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R (j ≫ i)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp R j i) ≪≫
        Functor.mapDerivedCategoryCompIso _ _))

/-- Pointwise proper/open model compositor at a normalized interchange.
Source: compact-support composition (blueprint: def-pur-transport-compact-support-coordinates). -/
def supportComp
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (cf.g ≫ cg.i))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)))
    (m : (CondensedRing.openImmersionLowerShriek R cg.i).mapDerivedCategory.obj
        ((CondensedRing.lowerStar R cf.g).rightDerivedFunctor.obj
          ((CondensedRing.openImmersionLowerShriek R cf.i).mapDerivedCategory.obj K)) ⟶
      (CondensedRing.lowerStar R cr.obj.obj.g).rightDerivedFunctor.obj
        ((CondensedRing.openImmersionLowerShriek R cr.obj.obj.i).mapDerivedCategory.obj
          ((CondensedRing.openImmersionLowerShriek R cf.i).mapDerivedCategory.obj K))) :=
  (CondensedRing.lowerStar R cg.g).rightDerivedFunctor.map m ≫
    (lowerComp R cr.obj.obj.g cg.g).inv.app
      ((CondensedRing.openImmersionLowerShriek R cr.obj.obj.i).mapDerivedCategory.obj
        ((CondensedRing.openImmersionLowerShriek R cf.i).mapDerivedCategory.obj K)) ≫
    (CondensedRing.lowerStar R (cr.obj.obj.g ≫ cg.g)).rightDerivedFunctor.map
      ((openComp R cf.i cr.obj.obj.i).hom.app K)

end AlgebraicGeometry.ProEtale.PurityTransport
