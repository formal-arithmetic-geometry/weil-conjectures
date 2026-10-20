/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NH and J4
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Sheaf.AlgebraicGeometry.EtaleCompactificationGraphMap

/-!
# Constructed graph comparisons for compact supports

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tag 03S6
(blueprint: def-asd-compact-support-graph-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Inclusion of compactly supported sheaf sections into direct image.
Source: SGA 4 XVII 6.2.11
(blueprint: def-asd-compact-support-graph-comparison). -/
noncomputable def compactificationSheafToDirectImage
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} {f : U ⟶ X}
    (c : Compactification f) :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g ⟶ lowerStar (ModuleCat.{u + 1} A) f :=
  Functor.whiskerRight (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i)
      (lowerStar (ModuleCat.{u + 1} A) c.g) ≫
    (lowerStarComp (ModuleCat.{u + 1} A) c.i c.g f c.comm).hom

/-- The specified sum-extension exchange, descended termwise and inverted.
Source: Stacks Project Tag 03S6
(blueprint: def-asd-compact-support-graph-comparison). -/
noncomputable def exactEtaleSumExchange
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (g : X' ⟶ X) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst g f)
          inferInstance).mapDerivedCategory :=
  haveI := isIso_etaleLowerShriekBaseChangeMap A g f
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (etaleLowerShriekBaseChangeMap A g f)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The proper exchange followed by inverse open-extension exchange, using exact derived
inverse image. The transport from `L(g^*)` is the canonical exact-functor comparison.
Source: SGA 4 XVII 5.2.2
(blueprint: def-asd-compact-support-graph-comparison). -/
noncomputable def exactCompactSupportExchange
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    {f : U ⟶ X} (c : Compactification f) (g : X' ⟶ X) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip) :=
  Functor.whiskerLeft (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
    rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback g f).flip c ≫
    Functor.whiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd g f)).hom _

/-- The compact-support exchange as a 2-square, for canonical pasting.
Source: SGA 4 XVII 5.2.2
(blueprint: def-asd-compact-support-graph-comparison). -/
noncomputable def exactCompactSupportExchangeSquare
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    {f : U ⟶ X} (c : Compactification f) (g : X' ⟶ X) :=
  TwoSquare.mk _ _ _ _ (exactCompactSupportExchange A c g)

/-- The specified sum exchange as a 2-square, for the same canonical pasting.
Source: Stacks Project Tag 03S6
(blueprint: def-asd-compact-support-graph-comparison). -/
noncomputable def exactEtaleSumExchangeSquare
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (g : X' ⟶ X) :=
  TwoSquare.mk _ _ _ _ (exactEtaleSumExchange A f g).hom

/-- A termwise sheaf comparison followed by the total-right-derived comparison.
This is a map on homotopy representatives, with no boundedness condition.
Source: SGA 4 XVII 6.2.11
(blueprint: def-asd-compact-support-graph-comparison). -/
noncomputable def compactSupportComparisonOnHomotopy
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory.obj
        (DerivedCategory.Qh.obj K) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (DerivedCategory.Qh.obj K) :=
  (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategoryFactorsh.hom.app K ≫
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (ComplexShape.up ℤ)).app K) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv.app K) ≫
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorUnit.app
      (((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) ≫
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactorsh.inv.app K)

/-- Descend a natural transformation through a localization without choosing any data.
Source: Stacks Project Tag 04VG
(blueprint: def-asd-compact-support-graph-comparison). -/
@[irreducible]
noncomputable def normalizationLocalizationDesc
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G) : F ⟶ G :=
  (Localization.fullyFaithfulWhiskeringLeft L W E).preimage τ

/-- The localization descent recovers the original transformation on every representative.
Source: Stacks Project Tag 04VG
(blueprint: def-asd-compact-support-graph-comparison). -/
theorem normalizationLocalizationDesc_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G) (K : C) :
    (normalizationLocalizationDesc L W τ).app (L.obj K) = τ.app K :=
by
  unfold normalizationLocalizationDesc
  exact congr_app ((Localization.fullyFaithfulWhiskeringLeft L W E).map_preimage τ) K

/-- The normalized comparison on all derived objects, obtained by full faithfulness of
precomposition with the homotopy localization. No isomorphism claim enters this construction.
Source: Stacks Project Tags 04VG and 015F
(blueprint: def-asd-compact-support-graph-comparison). -/
@[irreducible]
noncomputable def compactSupportDerivedComparison
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory ⟶
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  normalizationLocalizationDesc DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (ComplexShape.up ℤ))
    (F := (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory)
    (G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    ((etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight (a.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv
        DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory
          (ComplexShape.up ℤ))
        (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactorsh.inv
        (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom)

/-- The derived comparison has the prescribed value on every homotopy representative.
Source: Stacks Project Tag 04VG
(blueprint: def-asd-compact-support-graph-comparison). -/
theorem compactSupportDerivedComparison_app
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)) :
    (compactSupportDerivedComparison A f c a).app (DerivedCategory.Qh.obj K) =
      compactSupportComparisonOnHomotopy A f c a K := by
  rw [compactSupportDerivedComparison, normalizationLocalizationDesc_app]
  simp only [NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, compactSupportComparisonOnHomotopy]

/-- Regard a proper refinement as a compactification of the coarser open immersion.
Source: SGA 4 XVII 6.2.11
(blueprint: def-asd-compact-support-graph-comparison). -/
def refinementOpenCompactification
    {U X : Scheme.{u}} {f : U ⟶ X} {c d : Compactification f}
    (r : c.Refinement d) : Compactification d.i where
  Z := c.Z
  g := r.hom
  i := c.i
  comm := r.i_hom.symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- Identity normalization: remove the exact derived direct image of the identity.
Source: SGA 4 XVII 6.2.11
(blueprint: def-asd-compact-support-graph-comparison). -/
noncomputable def identityEtaleCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper (𝟙 X)) ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance).mapDerivedCategory :=
  Functor.isoWhiskerLeft
      (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance).mapDerivedCategory
      ((lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫
    Functor.rightUnitor _


/-- Core comparison data: the geometric and degreewise normalization maps.
Source: SGA 4 XVII 5.2.2 and 6.2.11 (blueprint: def-asd-compact-support-graph-comparison). -/
structure EtaleCompactSupportCore (A : Type (u + 1)) [CommRing A] where
  comparison : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f),
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory
  /-- Inverse comparison on sheaves: extend each sheet section by zero off its graph. -/
  sheafComparison : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f),
    etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g
  /-- The sheaf map is the specified graph-extension map inside direct image. -/
  sheaf_normalization : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f) (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
    (sheafComparison f c).app M ≫ (compactificationSheafToDirectImage A c).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M
  /-- On every homotopy representative, descend the preceding sheaf map degreewise and
  then apply the total-right-derived unit. -/
  derived_normalization : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)),
    (comparison f c).inv.app (DerivedCategory.Qh.obj K) =
      compactSupportComparisonOnHomotopy A f c (sheafComparison f c) K


/-- Base-change, refinement and identity equations for normalized core data. -/
structure EtaleCompactSupportCoherence (A : Type (u + 1)) [CommRing A]
    (core : EtaleCompactSupportCore A) : Prop where
  base_change : ∀ {U X X' : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [QuasiCompact f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian X'] [CompactSpace X'] (c : Compactification f) (g : X' ⟶ X),
    exactCompactSupportExchange A c g ≫
        Functor.whiskerLeft
          (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory
          (core.comparison (pullback.fst g f)
            (c.ofIsPullback (IsPullback.of_hasPullback g f).flip)).hom =
      Functor.whiskerRight (core.comparison f c).hom
          (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≫
        (exactEtaleSumExchange A f g).hom
  /-- Under a proper refinement, use the core.comparison for the coarser open immersion,
  normalized by graph extension (hence identity over U), and then compose direct images. -/
  refinement : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c d : Compactification f) (r : c.Refinement d)
    [IsLocallyNoetherian d.Z] [CompactSpace d.Z],
    Functor.whiskerRight (core.comparison d.i (refinementOpenCompactification r)).inv
        (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r.hom)
          (lowerStar (ModuleCat.{u + 1} A) d.g)
          (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)).hom ≫
      (core.comparison f c).hom = (core.comparison f d).hom
  /-- For an identity morphism the normalized core.comparison is the identity after removing
  the identity functor. Refinement compatibility supplies every other compactification. -/
  identity : ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X],
    core.comparison (𝟙 X) (Compactification.ofIsProper (𝟙 X)) =
      identityEtaleCompactSupportComparison A X

end AlgebraicGeometry.Etale
