/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows
import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows

/-!
# The intrinsic proper/open comparison on single constant-ring module complexes

Source: Stacks Project, Tags 09AE and 0F7B.
(blueprint: def-cbc-single-proper-open-arrows)

These are the module operations underlying the strict-tower comparison. The
clopen projector is constructed from adjunctions; no finite coefficient origin
or choice of an interchange transformation is used to define it.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The single-level open unit is invertible.
Source: Stacks Tag 09AE (blueprint: def-cbc-single-proper-open-arrows).
Proof: the constant-ring module equivalence identifies the left adjoint with
ordinary extension by zero, which is fully faithful. -/
theorem singleJ_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (moduleJAdj B j).unit := by
  let A := ModuleCat.{u + 1} B
  have : IsIso (openImmersionLowerShriekAdjunction A j).unit :=
    (openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)
  let ff := (openImmersionLowerShriekAdjunction A j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  exact unit_iso_of_comparison (L := moduleJ B j) (R := modulePullback B j)
    (moduleJAdj B j) (fixedRestriction B U) (fixedRestriction B X)
    (openImmersionLowerShriek A j) (fixedOpen B j)

/-- Open base change is invertible for an arbitrary constant coefficient ring.
Source: Stacks Tag 09AE (blueprint: def-cbc-single-proper-open-arrows).
Proof: ordinary open base change puts the target in the essential image of the
fully faithful open extension. Its counit there is invertible, and the prescribed
transpose is that counit composed with the pulled-back invertible open unit. -/
theorem singleBetaInv_isIso_general {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) : IsIso (singleBetaInv B a j' j g h) := by
  have := singleJ_unit_isIso B j
  have := singleJ_unit_isIso B j'
  let ff := (moduleJAdj B j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let d := moduleOpenSquare B a j' j g hsq
  have hi (M : Modules B U) : IsIso ((singleBetaInv B a j' j g h).app M) := by
    have hc : IsIso ((moduleJAdj B j').counit.app
        ((modulePullback B g).obj ((moduleJ B j).obj M))) :=
      (moduleJAdj B j').isIso_counit_app_of_iso (d.app M)
    change IsIso (singleBetaInvApp B a j' j g h M)
    unfold singleBetaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The canonical single-level open-to-direct-image map.
Source: Stacks Tag 09AE (blueprint: def-cbc-single-proper-open-arrows). -/
noncomputable def singleOpenToR {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : moduleJ B j ⟶ moduleDirectImage B j :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (moduleJ B j)
      (Scheme.proEtaleRingModuleAdjunction j (coefficients B X)
        (coefficients B U) (constantRingIso B j)).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (@inv _ _ _ _ (moduleJAdj B j).unit (singleJ_unit_isIso B j))
      (moduleDirectImage B j) ≫ (Functor.leftUnitor _).hom

/-- Clopen extension agrees with direct image under the canonical comparison.
Source: Stacks Tag 09AE (blueprint: def-cbc-single-proper-open-arrows).
Proof: the sectionwise clopen decomposition gives an isomorphism between open
extension and direct image. Direct image is therefore fully faithful. Its unit
on the image of open extension is invertible, as is the inverse open unit. The
canonical comparison is the composite of these two isomorphisms. -/
theorem singleOpenToR_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] : IsIso (singleOpenToR B j) := by
  let d := moduleClopenIso B j
  have := singleJ_unit_isIso B j
  let ff := (moduleJAdj B j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (moduleDirectImage B j).Full := Functor.Full.of_iso d
  have : (moduleDirectImage B j).Faithful := Functor.Faithful.of_iso d
  let a : modulePullback B j ⊣ moduleDirectImage B j :=
    Scheme.proEtaleRingModuleAdjunction j (coefficients B X)
    (coefficients B U) (constantRingIso B j)
  have hi (M : Modules B U) : IsIso ((singleOpenToR B j).app M) := by
    have hu : IsIso (a.unit.app ((moduleJ B j).obj M)) :=
      a.isIso_unit_app_of_iso (d.app M)
    have hv : IsIso ((inv (moduleJAdj B j).unit).app M) := inferInstance
    have hw : IsIso ((moduleDirectImage B j).map
        ((inv (moduleJAdj B j).unit).app M)) := inferInstance
    dsimp only [singleOpenToR, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
      Functor.associator_inv_app, Functor.leftUnitor_hom_app]
    simp only [Category.id_comp]
    exact IsIso.comp_isIso' hu (IsIso.comp_isIso' hw (IsIso.id _))
  exact NatIso.isIso_of_isIso_app _

/-- The actual single-level clopen projector.
Source: Stacks Tag 0F7B (blueprint: def-cbc-single-proper-open-arrows). -/
noncomputable def singlePi {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Modules B X) ⟶ modulePullback B s ⋙ moduleJ B s :=
  (Scheme.proEtaleRingModuleAdjunction s (coefficients B X)
    (coefficients B U) (constantRingIso B s)).unit ≫
    Functor.whiskerLeft (modulePullback B s)
      (@inv _ _ _ _ (singleOpenToR B s) (singleOpenToR_isIso B s))

/-- Unit-normalized composition of single-level open extensions.
Source: Stacks Tag 09AE (blueprint: def-cbc-single-proper-open-arrows). -/
noncomputable def singleJComp {U V X : Scheme.{u}} (k : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    moduleJ B k ⋙ moduleJ B j ≅ moduleJ B (k ≫ j) :=
  Adjunction.leftAdjointCompIso (moduleJAdj B k) (moduleJAdj B j)
    (moduleJAdj B (k ≫ j)) (moduleGComp B k j).symm

/-- Equality of the single-level open extension functors under equality of opens.
Source: equality transport (blueprint: def-cbc-single-proper-open-arrows).
Proof: substitute the equality; the open-immersion instances are proof irrelevant. -/
theorem singleJ_congr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (e : f = g) : moduleJ B f = moduleJ B g := by
  subst g
  rfl

/-- Transport single-level open extension along an equality of open morphisms.
Source: equality transport (blueprint: def-cbc-single-proper-open-arrows). -/
noncomputable def singleJCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (e : f = g) : moduleJ B f ≅ moduleJ B g :=
  eqToIso (singleJ_congr B e)

/-- The sheaf-level intrinsic proper/open inverse-image comparison.
Source: Stacks Tag 0F7B (blueprint: def-cbc-single-proper-open-arrows). -/
noncomputable def singleAlpha {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    moduleJ B i ⋙ modulePullback B p ⟶ modulePullback B r ⋙ moduleJ B k :=
  projectedComparison (moduleJ B i) (modulePullback B p)
    (modulePullback B (pullback.snd p i)) (modulePullback B (squareLift k r p i h))
    (moduleJ B (squareLift k r p i h)) (moduleJ B (pullback.fst p i))
    (moduleJ B (squareLift k r p i h ≫ pullback.fst p i)) (moduleJ B k)
    (modulePullback B r)
    (@asIso _ _ _ _ (singleBetaInv B (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm)
      (singleBetaInv_isIso_general B _ _ _ _ _ (IsPullback.of_hasPullback p i).flip)).inv
    (singlePi B (squareLift k r p i h))
    (singleJComp B (squareLift k r p i h) (pullback.fst p i)).hom
    (singleJCongr B (pullback.lift_fst k r h)).hom
    ((moduleGComp B (squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (modulePullback B) (pullback.lift_snd k r h))).hom)

/-- Exact natural transformations descend by the localization universal property.
Source: exact localization (blueprint: def-cbc-single-proper-open-arrows). -/
noncomputable def singleDerivedNatTrans
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F G : C ⥤ D)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (t : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The exact-localized single-level intrinsic comparison.
Source: Stacks Tag 0F7B (blueprint: def-cbc-single-proper-open-arrows). -/
noncomputable def singleDerivedAlpha {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (moduleJ B i).mapDerivedCategory ⋙ (modulePullback B p).mapDerivedCategory ⟶
      (modulePullback B r).mapDerivedCategory ⋙ (moduleJ B k).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).inv ≫
    singleDerivedNatTrans _ _ (singleAlpha B k r p i h) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom

/-- The single-level proper mate of the intrinsic comparison.
Source: Stacks Tag 0F7B (blueprint: def-cbc-single-proper-open-arrows). -/
noncomputable def singleGamma {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (moduleDirectImage B r).rightDerivedFunctor ⋙ (moduleJ B i).mapDerivedCategory ⟶
      (moduleJ B k).mapDerivedCategory ⋙ (moduleDirectImage B p).rightDerivedFunctor :=
  mateEquiv
    (Scheme.proEtaleRingModuleAdjunction r (coefficients B S)
      (coefficients B V) (constantRingIso B r)).mapDerivedCategoryRightDerivedAdjunction
    (Scheme.proEtaleRingModuleAdjunction p (coefficients B T)
      (coefficients B W) (constantRingIso B p)).mapDerivedCategoryRightDerivedAdjunction
    (singleDerivedAlpha B k r p i h)

end AlgebraicGeometry.ProEtale.StrictTower
