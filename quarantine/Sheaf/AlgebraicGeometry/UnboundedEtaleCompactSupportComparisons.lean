/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.UnboundedProperOpenInterchange
import Sheaf.Paper.CompactSupportStaircaseExpansion
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Unbounded ordinary etale compact-support comparisons

Source: Stacks Project, Tags 0F7H--0F7L and 0F7B, case (b)
(blueprint: lem-amb-unbounded-compact-support-comparisons).

The candidates, common-refinement comparisons, and proper/open tower isomorphism are the
existing ordinary etale constructions. The definitions below assemble the specified tower
composition and transport the existing exchange to exact, termwise inverse image. The
statements supply coherence and equality with the bounded-below maps, on actual natural
transformations rather than just existence of unrelated isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private lemma mate_ofNatIsoLeft
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (α : TwoSquare G L₁' L₂' H) :
    (mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α).natTrans =
      (mateEquiv adj₁ adj₂ ((α.whiskerRight e₂.hom).whiskerLeft e₁.inv)).natTrans := by
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Category.assoc, ← Functor.map_comp]

private lemma mate_whiskerTop
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : C ⥤ E} {H : D ⥤ F}
    (α : TwoSquare G' L₁ L₂ H) (γ : G ⟶ G') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerTop γ)).app K =
      γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_whiskerBottom
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : C ⥤ E} {H H' : D ⥤ F}
    (α : TwoSquare G L₁ L₂ H) (δ : H ⟶ H') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom δ)).app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, δ.naturality]

set_option backward.isDefEq.respectTransparency false in
private lemma inverse_mates_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {F₁ : C ⥤ E} {U₁ : E ⥤ C} {F₂ : D ⥤ F} {U₂ : F ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)
    (e : L₁ ⋙ F₂ ≅ F₁ ⋙ L₂)
    (α : TwoSquare U₁ L₂ L₁ U₂)
    (hα : ∀ K, adj₄.unit.app (L₁.obj K) ≫ U₂.map (e.hom.app K) =
      L₁.map (adj₃.unit.app K) ≫ α.natTrans.app (F₁.obj K)) (K : D) :
    (adj₃.homEquiv _ _
      ((mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv)).natTrans.app K)) ≫
      (mateEquiv adj₂ adj₁ α).natTrans.app (F₂.obj K) = R₁.map (adj₄.unit.app K) := by
  let γ := (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv)).natTrans
  change (adj₃.homEquiv _ _ (γ.app K)) ≫ _ = _
  simp only [Adjunction.homEquiv_unit, mateEquiv_apply, NatTrans.comp_app,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  change adj₃.unit.app (R₁.obj K) ≫ U₁.map (γ.app K) ≫
    adj₁.unit.app (U₁.obj (R₂.obj (F₂.obj K))) ≫
    R₁.map (α.natTrans.app (R₂.obj (F₂.obj K))) ≫
    R₁.map (U₂.map (adj₂.counit.app (F₂.obj K))) = _
  rw [reassoc_of% (adj₁.unit.naturality (U₁.map (γ.app K)))]
  rw [reassoc_of% (adj₁.unit.naturality (adj₃.unit.app (R₁.obj K)))]
  simp only [← R₁.map_comp]
  rw [reassoc_of% (α.natTrans.naturality (γ.app K))]
  rw [← Category.assoc (L₁.map _) (α.natTrans.app _) _, ← hα]
  rw [Category.assoc]
  rw [← U₂.map_comp (L₂.map (γ.app K)) (adj₂.counit.app (F₂.obj K))]
  rw [mateEquiv_counit]
  simp only [TwoSquare.mk, Functor.map_comp]
  have hc : R₁.map (U₂.map (e.hom.app (R₁.obj K))) ≫
      R₁.map (U₂.map (e.inv.app (R₁.obj K))) = 𝟙 _ := by
    rw [← R₁.map_comp, ← U₂.map_comp, Iso.hom_inv_id_app, U₂.map_id, R₁.map_id]
  rw [reassoc_of% hc]
  rw [← R₁.map_comp, adj₄.unit_naturality]
  rw [R₁.map_comp, adj₁.right_triangle_components_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma exact_exchange_transport
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) :
    Functor.whiskerLeft (rightDerivedLowerStar (ModuleCat.{u + 1} A) f)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
      derivedBaseChangeMap (ModuleCat.{u + 1} A) sq ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g').hom _ =
      exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq := by
  let B := ModuleCat.{u + 1} A
  let α := TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq).hom
  have hs :
      ((((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
        (leftDerivedUpperStarIsoMapDerivedCategory B g').inv).whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory B f').hom).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory B f).inv) =
      TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso B sq).hom := by
    ext M
    simp only [α, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.mk]
    simp only [derivedSquareUpperStarIso, leftDerivedUpperStarComp,
      exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.inv_hom_id_app_assoc]
    rw [← (upperStar B g').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  have hm := mate_ofNatIsoLeft
    (derivedUpperStarLowerStarAdjunction B f) (derivedUpperStarLowerStarAdjunction B f')
    (leftDerivedUpperStarIsoMapDerivedCategory B f)
    (leftDerivedUpperStarIsoMapDerivedCategory B f')
    ((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
      (leftDerivedUpperStarIsoMapDerivedCategory B g').inv)
  rw [← mapDerivedUpperStarLowerStarAdjunction_eq,
    ← mapDerivedUpperStarLowerStarAdjunction_eq, hs] at hm
  change _ = derivedBaseChangeMap B sq at hm
  rw [← hm]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [mate_whiskerBottom, mate_whiskerTop]
  change _ = (mateEquiv (mapDerivedUpperStarLowerStarAdjunction B f)
    (mapDerivedUpperStarLowerStarAdjunction B f') α).app K
  dsimp only [B, rightDerivedLowerStar, Functor.comp_obj]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Assemble the canonical proper/open tower comparison, using the closure compactification
`ofComp`, and compare the input and output with the chosen compactifications. This is the
explicit isomorphism in the proof of the existing unbounded composition theorem.
Source: Stacks Project, Tag 0F7J
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleLowerShriekCompIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  Functor.isoWhiskerRight
      (rightDerivedLowerShriekIso A
        ((HasCompactification.compactification (f ≫ g)).ofComp
          (HasCompactification.compactification g)).restrict).symm _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A
      (HasCompactification.compactification g)
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)) ≪≫
    rightDerivedLowerShriekIso A
      ((HasCompactification.compactification g).comp
        ((HasCompactification.compactification (f ≫ g)).ofComp
          (HasCompactification.compactification g)))

/-- Transport the already defined unbounded exchange from left derived inverse image to
its exact termwise realization. No new choice of exchange map is made.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleCompactSupportBaseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' :=
  Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).inv ≫
    rightDerivedLowerShriekBaseChangeMap A sq ≫
    Functor.whiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v').hom _

/-- The common-refinement comparisons satisfy the identity and cocycle laws. In particular,
passing through any third compactification produces the same map.
Source: Stacks Project, Tag 0F7I
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: use proper/open interchange for each refinement and its vertical pasting identity.
Refine any two common refinements and equalize their parallel arrows. The refinement
composition equations cancel the extra invertible factors. Taking three compactifications
in one common refinement gives the cocycle, and taking two equal ones gives the identity.
These are steps 3 and 4 of the node's proof. -/
theorem unboundedEtaleCompactSupport_comparison_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ c : Compactification f,
      rightDerivedLowerShriekOfCompactificationIso A c c = Iso.refl _) ∧
    (∀ c d e : Compactification f,
      rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
        rightDerivedLowerShriekOfCompactificationIso A d e =
          rightDerivedLowerShriekOfCompactificationIso A c e) := by
  sorry

/-- The graph-normalized comparison for the coarser open of a proper refinement.
The two Noetherian structures on the ambient are consequences of properness over the
Noetherian target, supplied explicitly rather than added as hypotheses.
Source: Stacks Project, Tags 0F7I and 0F7B
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleRefinementOpenComparison
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (N : EtaleCompactSupportNormalization A) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (refinementOpenCompactification r) :=
  letI : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  letI : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  (N.comparison d.i (refinementOpenCompactification r)).symm

/-- Every proper refinement, including a noncartesian one, gives the comparison normalized
as the identity on the source open. The graph-normalized open comparison is the identity
there; applying the ambient direct image and composing direct images gives this formula.
Source: Stacks Project, Tags 0F7I and 0F7B
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: step 3 applies proper/open interchange to the refinement square with left edge the
identity. Its restriction is the open unit. The graph-normalized comparison for that open
has the same adjunct, so adjunction identifies the maps. Apply the ambient direct image
and its composition isomorphism. Step 4 identifies the resulting map with the independent
common-refinement comparison. This works for arbitrary refinements, without density. -/
theorem unboundedEtaleCompactSupport_refinement_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (N : EtaleCompactSupportNormalization A) :
    (rightDerivedLowerShriekOfCompactificationIso A d c).hom =
      Functor.whiskerRight (unboundedEtaleRefinementOpenComparison A r N).hom
        (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r.hom)
          (lowerStar (ModuleCat.{u + 1} A) d.g)
          (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)).hom := by
  sorry

/-- The composition isomorphism is computed by every proper/open tower. Thus it is
independent of compactification choices and commutes with their refinement comparisons.
Source: Stacks Project, Tag 0F7J
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: steps 5 and 6 apply proper/open interchange in a tower, then compose direct images
and open extensions. Two towers have a common refining tower. Horizontal pasting identifies
its two open/refinement factors; vertical pasting identifies its two proper/refinement
factors. Naturality commutes the middle factors. The common-refinement cocycles then cancel,
giving the displayed equation for every tower, not only the one used in the definition. -/
theorem unboundedEtaleLowerShriekCompIso_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    (unboundedEtaleLowerShriekCompIso A f g).hom =
      NatTrans.hcomp (rightDerivedLowerShriekIso A e.restrict).inv
        (rightDerivedLowerShriekIso A d).inv ≫
      (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom ≫
      (rightDerivedLowerShriekIso A (d.comp e)).hom := by
  sorry


/-- Congruence of the chosen compact-support functors under equality of morphisms.
Source: Stacks Project, Tag 0F7K
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleLowerShriekCongr
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' := by
  subst h
  exact Iso.refl _

/-- The identity compactification, followed by the exact identity sum-extension comparison.
Source: Stacks Project, Tag 0F7K
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleLowerShriekId
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [HasCompactification (𝟙 X)] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) ≅
      𝟭 (DerivedCategoryModule A X) :=
  (rightDerivedLowerShriekIso A (Compactification.ofIsProper (𝟙 X))).symm ≪≫
    identityEtaleCompactSupportComparison A X ≪≫
    Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointIdIso
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X) inferInstance)
        (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Associativity is equality of the two specified natural transformations.
Source: Stacks Project, Tag 0F7K
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: step 7 chooses a compatible three-level tower. Expand both composition maps using
the tower normalization. Horizontal and vertical pasting give the two rectangle maps.
Naturality of the middle proper/open interchange identifies the two orders in which the
disjoint factors are applied. Direct-image and open-extension associativity supply the
parentheses. The tower-independence equation then gives the assertion for arbitrary choices. -/
theorem unboundedEtaleLowerShriekCompIso_assoc
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z T : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z] [IsNoetherian T]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification (f ≫ g)] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)] :
    Functor.whiskerRight (unboundedEtaleLowerShriekCompIso A f g).hom
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h) ≫
      (unboundedEtaleLowerShriekCompIso A (f ≫ g) h).hom ≫
      (unboundedEtaleLowerShriekCongr A (Category.assoc f g h)).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleLowerShriekCompIso A g h).hom ≫
      (unboundedEtaleLowerShriekCompIso A f (g ≫ h)).hom := by
  sorry

/-- Both unit laws have the canonical identity-compactification normalization.
Source: Stacks Project, Tag 0F7K
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: step 7 uses the identity compactification in the unit towers. The proper/open square
then has identity proper or identity open sides. Its comparison is the identity, and the
direct-image and open-extension unit identifications leave precisely the displayed maps.
Tower independence transfers these calculations to the chosen compactifications. -/
theorem unboundedEtaleLowerShriekCompIso_units
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification (𝟙 X)] [HasCompactification (𝟙 Y)]
    [HasCompactification (𝟙 X ≫ f)] [HasCompactification (f ≫ 𝟙 Y)] :
    ((unboundedEtaleLowerShriekCompIso A (𝟙 X) f).hom =
      Functor.whiskerRight (unboundedEtaleLowerShriekId A X).hom _ ≫
        (Functor.leftUnitor _).hom ≫
        (unboundedEtaleLowerShriekCongr A (Category.id_comp f).symm).hom) ∧
    ((unboundedEtaleLowerShriekCompIso A f (𝟙 Y)).hom =
      Functor.whiskerLeft _ (unboundedEtaleLowerShriekId A Y).hom ≫
        (Functor.rightUnitor _).hom ≫
        (unboundedEtaleLowerShriekCongr A (Category.comp_id f).symm).hom) := by
  sorry

/-- The exact inverse-image composition is the sheaf comparison descended termwise.
Source: Stacks Project, Tags 0F7H and 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleUpperStarCompIso
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar (ModuleCat.{u + 1} A) (f ≫ g)).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The exact inverse-image identity is the sheaf identity descended termwise.
Source: Stacks Project, Tags 0F7H and 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleUpperStarIdIso
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory ≅
      𝟭 (DerivedCategoryModule A X) :=
  Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
    Functor.mapDerivedCategoryIdIso _

private lemma upperStar_comp_id_unit
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X) (by simp)) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).hom ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory
          (unboundedEtaleUpperStarIdIso A X).hom = 𝟙 _ := by
  rw [upperStarComp_id_left]
  simp only [Iso.trans_hom, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [reassoc_of% Functor.mapDerivedCategoryNatIso_isoWhiskerLeft]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    unboundedEtaleUpperStarIdIso, Iso.trans_hom]
  simp only [Functor.mapDerivedCategoryNatIso_symm, Iso.inv_hom_id_app_assoc]
  have hr : (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).rightUnitor = Iso.refl _ := rfl
  rw [hr]
  have he : Functor.mapDerivedCategoryNatIso
      (Iso.refl ((upperStar (ModuleCat.{u + 1} A) (𝟙 X)) ⋙ 𝟭 _)) = Iso.refl _ := by
    apply Iso.ext
    exact Functor.mapDerivedCategoryNatIso_refl
  rw [he]
  erw [Category.id_comp]
  exact congr_app (Functor.mapDerivedCategoryCompIso_comp_id
    (upperStar (ModuleCat.{u + 1} A) (𝟙 X))) K

private lemma identity_exchange_of_pasting
    {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) (I : D ⥤ D) (J : E ⥤ E)
    (C : F ⋙ J ⟶ I ⋙ F) [IsIso C]
    (e : I ≅ 𝟭 D) (d : J ≅ 𝟭 E) (δ : I ≅ I ⋙ I) (ε : J ≅ J ⋙ J)
    (hδ : δ.hom ≫ Functor.whiskerLeft I e.hom = 𝟙 _)
    (hε : ε.hom ≫ Functor.whiskerLeft J d.hom = 𝟙 _)
    (hp : ∀ K, C.app K = ε.hom.app (F.obj K) ≫ J.map (C.app K) ≫
      C.app (I.obj K) ≫ F.map (δ.inv.app K)) :
    C ≫ Functor.whiskerRight e.hom F ≫ (Functor.leftUnitor F).hom =
      Functor.whiskerLeft F d.hom ≫ (Functor.rightUnitor F).hom := by
  have : J.Faithful := Functor.Faithful.of_iso d.symm
  ext K
  have hδ' : δ.inv.app K = I.map (e.hom.app K) := by
    have h := congr_app hδ K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at h
    have he : e.hom.app (I.obj K) = I.map (e.hom.app K) := by
      apply (cancel_mono (e.hom.app K)).1
      exact (e.hom.naturality (e.hom.app K)).symm
    rw [he] at h
    apply (cancel_epi (δ.hom.app K)).1
    exact (δ.hom_inv_id_app K).trans h.symm
  let c := C.app K ≫ F.map (e.hom.app K)
  have h := hp K
  rw [hδ'] at h
  have hn : J.map (F.map (e.hom.app K)) ≫ C.app K =
      C.app (I.obj K) ≫ F.map (I.map (e.hom.app K)) :=
    C.naturality (e.hom.app K)
  rw [← hn, ← Category.assoc (J.map _) (J.map _) _, ← J.map_comp] at h
  have hc : ε.hom.app (F.obj K) ≫ J.map c = 𝟙 _ := by
    apply (cancel_mono (C.app K)).1
    simpa only [c, Category.id_comp, Category.assoc] using h.symm
  have hd : ε.hom.app (F.obj K) ≫ J.map (d.hom.app (F.obj K)) = 𝟙 _ := by
    have hd := congr_app hε (F.obj K)
    have he : d.hom.app (J.obj (F.obj K)) = J.map (d.hom.app (F.obj K)) := by
      apply (cancel_mono (d.hom.app (F.obj K))).1
      exact (d.hom.naturality (d.hom.app (F.obj K))).symm
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app, he] using hd
  have hcd : c = d.hom.app (F.obj K) := by
    apply J.map_injective
    apply (cancel_epi (ε.hom.app (F.obj K))).1
    exact hc.trans hd.symm
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app]
  change C.app K ≫ F.map (e.hom.app K) ≫ 𝟙 _ =
    d.hom.app (F.obj K) ≫ 𝟙 _
  simpa only [Category.comp_id] using hcd

/-- The chosen-compactification exchange with exact inverse images. This extends the
existing `exactCompactSupportExchange` from the chosen fibre product to an arbitrary
specified cartesian square, using exactly the same canonical exact-functor transport.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleCompactSupportExchange
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v) (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (c.ofIsPullback sq) :=
  Functor.whiskerLeft (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).inv ≫
    rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A) sq c ≫
    Functor.whiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v').hom _

/-- Compact-support exchange is an isomorphism on every unbounded complex, independently
of the compactification, with the specified exact proper exchange and inverse open factor.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: in step 8 a finite ring has positive additive exponent. Unbounded proper base change
makes the proper factor invertible; the degreewise open comparison is invertible by exact
extension by zero. Their composite is the specified exchange. Step 9 applies the base-change
equation for proper/open interchange to a refinement and then applies the ambient direct
image. Mate pasting and the common-refinement cocycle identify the exchanges for any two
compactifications. This gives the displayed equation, for every supplied compactification. 

Full proof plan of the node, retained for stage 3:

1. First fix the structural comparisons that will be inserted in all formulas. By
[lem-weil-pbc-extension-by-zero-exact] and [prop-weil-pbc-inverse-image-modules-exact], open
extension and constant-module inverse image are exact, hence act termwise on every complex. The
sheaf open adjunction of [lem-weil-pbc-extension-by-zero-adjunction] induces the termwise
adjunction on homotopy categories by [lem-weil-pbc-termwise-adjunction-homotopy]. Its unit and
counit descend by [lem-weil-pbc-localization-universal-property], since both functors are exact;
their triangle identities descend as equalities. Hence $Dj_!\dashv j^*$ on the unbounded derived
categories for every open immersion, without needing a finite-type hypothesis. The open
composition and identity maps of [lem-cbc-extension-zero-composition] consequently descend, with
their same equations, by [lem-weil-pbc-localization-universal-property]. For proper maps use the
canonical unbounded direct-image comparison of
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition]. Its associativity and units can be
checked under the inverse-image/direct-image adjunctions specified in
[def-kun-unbounded-exchange]: for three maps $a,b,c$, both comparisons are adjoint to the
composite evaluation $$a^*b^*c^*Rc_*Rb_*Ra_*\xrightarrow{a^*b^*\varepsilon_c}a^*b^*Rb_*Ra_*
\xrightarrow{a^*\varepsilon_b}a^*Ra_*\xrightarrow{\varepsilon_a}1.$$
Termwise inverse-image composition
identifies the two parenthesizations. The mate-pasting identities and identity clause of
[lem-weil-pbc-mate-pasting] therefore give the same right-adjoint comparisons. They also show that
proper exchange commutes with composition of proper maps and successive changes of base: take the
mates of the pasted inverse-image square isomorphisms. This establishes the structural coherence
used below on the entire derived categories.
Dependencies: lem-weil-pbc-extension-by-zero-exact, prop-weil-pbc-inverse-image-modules-exact,
lem-weil-pbc-extension-by-zero-adjunction, lem-weil-pbc-termwise-adjunction-homotopy,
lem-cbc-extension-zero-composition, lem-weil-pbc-localization-universal-property,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition, def-kun-unbounded-exchange,
lem-weil-pbc-mate-pasting.

2. Use [lem-amb-unbounded-proper-open-interchange] for a square
$Q=(U\xrightarrow{k}V,r,p,W\xrightarrow{i}Z)$ with open horizontal maps and proper vertical maps.
Denote its specified isomorphism by $\Gamma_Q:Di_!Rr_*\to Rp_*Dk_!$. This is available on all of
$D(U_{\mathrm{et}},A)$, including for noncartesian refinement squares. For a cartesian square the
same node fixes its adjunct to be the inverse proper open-restriction exchange followed by the
open unit identification. Thus this is precisely the tower normalization required in the
statement, rather than an arbitrary isomorphism of the two functors. Retain both pasting
identities and the base-change equation of this node throughout the construction.
Dependencies: lem-amb-unbounded-proper-open-interchange.

3. For a refinement $u:c_1\to c_2$, write $c_i=(j_i,r_i)$, so $u j_1=j_2$ and $r_2u=r_1$. Apply
$\Gamma$ to the square with top $j_1$, bottom $j_2$, and vertical maps $1_X,u$. It gives
$\gamma_u:Dj_{2!}\to Ru_*Dj_{1!}$. For the candidates of [def-amb-etale-compact-support] define
$$\tau_u: F_{c_2}=Rr_{2,*}Dj_{2!}\xrightarrow{Rr_{2,*}\gamma_u}Rr_{2,*}Ru_*Dj_{1!}
\xrightarrow{\sim}Rr_{1,*}Dj_{1!}=F_{c_1}.$$ It is a natural isomorphism by
[lem-amb-unbounded-proper-open-interchange] and
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition]. On the open $X$ the sheaf
identification in $\gamma_u$ is the identity. The vertical pasting identity for $\Gamma$ gives
$\gamma_{vu}=(Rv_*\gamma_u)\gamma_v$ for $u:c_1\to c_2$, $v:c_2\to c_3$, and the identity-square
clause gives $\gamma_1=1$. Step 1's direct-image comparisons then give $\tau_{vu}=\tau_u\tau_v$
and $\tau_1=1$.
Dependencies: lem-amb-unbounded-proper-open-interchange, def-amb-etale-compact-support,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition.

4. The compactification category is nonempty and cofiltered, and base change acts on it, by
[lem-cbc-compactifiable-cofiltered]; a compactification is part of our hypotheses. For $c,d$
choose $u:e\to c$, $v:e\to d$ and put $\rho_{d,c}=\tau_v^{-1}\tau_u:F_c\to F_d$. To check
independence, choose a common refinement of two possible $e$'s. Its two induced maps to $c$, and
its two induced maps to $d$, can be equalized successively by cofilteredness. At that refinement
Step 3 makes both candidate expressions equal: replacing $e$ by $t:e'\to e$ replaces the
expression by $(\tau_t\tau_v)^{-1}(\tau_t\tau_u)=\tau_v^{-1}\tau_u$. Cancellation also shows
independence of parallel arrows. For three compactifications make these choices simultaneously;
then $$(\tau_w^{-1}\tau_v)(\tau_v^{-1}\tau_u)=\tau_w^{-1}\tau_u.$$ This is the cocycle condition,
and the expression for $c=d$ is the identity. Hence the $F_c$ are canonically identified as
$Rf_!$. No limit over a possibly large category is being formed: choose one compactification and
use these specified pairwise comparisons.
Dependencies: lem-cbc-compactifiable-cofiltered.

5. For $f:X\to Y$ and $g:Y\to Z$, choose a compactification $d=(i,s)$ of $g$ and one of $gf$. The
compatible-tower lemma [lem-cbc-compactifiable-compatible-tower] gives a compactification $(a,p)$
of $if$, a refinement of the supplied compactification of $gf$, and $V=\overline
X\times_{\overline Y}Y$ with open $b:V\to\overline X$, $j:X\to V$ and proper $q:V\to Y$,
satisfying $bj=a$, $qj=f$, $pb=iq$. These are compactifications $c_f=(j,q)$, $c_{gf}=(a,sp)$.
Using [def-amb-etale-compact-support], define on these choices $$\alpha^T=\bigl(Rs_*Rp_*Db_!Dj_!
\xrightarrow{\sim}R(sp)_*D(bj)_!\bigr)\circ(Rs_*\Gamma_QDj_!):Rs_*Di_!Rq_*Dj_!\longrightarrow
R(sp)_*Da_!.$$ All arrows are isomorphisms by [lem-amb-unbounded-proper-open-interchange],
[lem-cbc-extension-zero-composition] and
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition]. Use Step 4 to compare its three
candidates with arbitrary chosen candidates. The formula is the proper/open tower comparison in
the question, including its open-adjunction normalization from Step 2.
Dependencies: lem-cbc-compactifiable-compatible-tower, def-amb-etale-compact-support,
lem-amb-unbounded-proper-open-interchange, lem-cbc-extension-zero-composition,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition.

6. Here is the independence calculation for $\alpha^T$. Any two towers admit a common refining
tower by [lem-cbc-compactifiable-compatible-tower], so consider a refining tower $1\to2$ with
proper maps $v:\overline X_1\to\overline X_2$, $u:\overline Y_1\to\overline Y_2$, $w:V_1\to V_2$.
Write $Q_1,Q_2$ for their cartesian proper/open squares and abbreviate all direct-image/open
composition identifications by Step 1. Set $$A:Dj_{2!}\to Rw_*Dj_{1!},\quad D:Di_{2!}\to
Ru_*Di_{1!},\quad F:Db_{2!}Rw_*\to Rv_*Db_{1!},\quad E:D(b_2j_2)_!\to Rv_*D(b_1j_1)_!,$$ each the
$\Gamma$ for its indicated square. These squares have proper vertical maps by the tower lemma;
they need not be cartesian. Horizontal pasting gives $E=(F Dj_{1!})(Db_{2!}A)$. Vertical pasting,
applied to the rectangle from $V_1$ to $\overline Y_2$ in its two decompositions, gives
$$(Rp_{2,*}F)(\Gamma_{Q_2}Rw_*)=(Ru_*\Gamma_{Q_1})(D Rq_{1,*}).$$ Both equations are clauses of
[lem-amb-unbounded-proper-open-interchange]. Now apply $Rs_{2,*}$, insert $A$ on the input, and
use naturality of $\Gamma_{Q_2}$ to move this insertion past that comparison. The first displayed
identity replaces the resulting $F,A$ by $E$; the second replaces the remaining two square maps.
The left route is $\tau_{gf}\alpha^{T_2}$ and the right route is $\alpha^{T_1}(\tau_g\tau_f)$,
where the $\tau$'s are precisely Step 3's maps. Therefore the composition square commutes with
refinements. Comparing through a common tower proves independence, including independence of the
maps to the original chosen compactifications by Step 4's parallel-arrow calculation.
Dependencies: lem-cbc-compactifiable-compatible-tower, lem-amb-unbounded-proper-open-interchange.

7. For associativity take $f:X\to Y$, $g:Y\to Z$, $h:Z\to T$. Choose $Z\xrightarrow{i}\overline
Z\xrightarrow{t}T$. Apply [lem-cbc-compactifiable-compatible-tower] to $(g,h)$, using a
compactification of $hg$, to obtain $Y\hookrightarrow\overline Y\xrightarrow{s}\overline Z$. Apply
it to $(f,hg)$, using this compactification of $hg$ and one of $hgf$, to obtain
$X\hookrightarrow\overline X\xrightarrow{p}\overline Y$. Put $W=\overline Y\times_{\overline Z}Z$,
$V=\overline X\times_{\overline Y}W$, and $U=\overline X\times_{\overline Y}Y$. Write
$k:W\hookrightarrow\overline Y$, $d:Y\hookrightarrow W$, $b:V\hookrightarrow\overline X$,
$a:U\hookrightarrow V$, and $l:X\hookrightarrow U$ for the opens, and $q:W\to Z$, $r:V\to W$,
$m:U\to Y$ for the proper projections. Here $p,s,t$ are proper, and $q,r,m$ are their base
changes; no properness of $f,g,h$ is claimed. Define the three squares
$$A=\begin{array}{ccc}U&\xrightarrow{a}&V\\ m\downarrow&&\downarrow r\\
Y&\xrightarrow{d}&W\end{array},\quad B=\begin{array}{ccc}V&\xrightarrow{b}&\overline X\\
r\downarrow&&\downarrow p\\ W&\xrightarrow{k}&\overline Y\end{array},\quad
C=\begin{array}{ccc}W&\xrightarrow{k}&\overline Y\\ q\downarrow&&\downarrow s\\
Z&\xrightarrow{i}&\overline Z\end{array}.$$ All have proper vertical and open horizontal edges.
With Step 1's structural composition identifications, put $\mathsf A=\Gamma_A:Dd_!Rm_*\to
Rr_*Da_!$, $\mathsf B=\Gamma_B:Dk_!Rr_*\to Rp_*Db_!$, and $\mathsf C=\Gamma_C:Di_!Rq_*\to
Rs_*Dk_!$. Horizontal and vertical pasting of [lem-amb-unbounded-proper-open-interchange] give
$$\Gamma_{A+B}=(\mathsf B Da_!)\circ(Dk_!\mathsf A),\qquad \Gamma_{B+C}=(Rs_*\mathsf
B)\circ(\mathsf C Rr_*).$$ The starting triple functor is $Rt_*Di_!Rq_*Dd_!Rm_*Dl_!$. Expanding
Step 5, composition first for $(g,f)$ and then for $(h,gf)$ gives $$(Rt_*Rs_*\mathsf B
Da_!Dl_!)\circ(Rt_*\mathsf C Rr_*Da_!Dl_!)\circ(Rt_*Di_!Rq_*\mathsf A Dl_!),$$ whereas composition
first for $(h,g)$ and then for $(hg,f)$ gives $$(Rt_*Rs_*\mathsf B
Da_!Dl_!)\circ(Rt_*Rs_*Dk_!\mathsf A Dl_!)\circ(Rt_*\mathsf C Dd_!Rm_*Dl_!).$$ For every $K\in
D(X_{\mathrm{et}},A)$, set $z=\mathsf A_{Dl_!K}:Dd_!Rm_*Dl_!K\to Rr_*Da_!Dl_!K$. Naturality of
$\mathsf C$ is exactly $$Rs_*Dk_!(z)\circ\mathsf C_{Dd_!Rm_*Dl_!K} =\mathsf C_{Rr_*Da_!Dl_!K}\circ
Di_!Rq_*(z).$$ Applying $Rt_*$ and then the common first factor identifies the two composites.
Step 1 supplies the structural parentheses, and Step 6 passes from this tower to arbitrary
choices. For an identity morphism choose its identity compactification; the tower squares have
either both proper or both open maps identities, so the identity clause for $\Gamma$ and Step 1
give the identity comparison. This proves associativity and the unit normalizations.
Dependencies: lem-cbc-compactifiable-compatible-tower, lem-amb-unbounded-proper-open-interchange.

8. Construct base change first on a compactification $c=(j,r)$ and its fibre-product base change
$c_v=(j',r')$. These are compactifications and refinements base-change functorially by
[lem-cbc-compactifiable-cofiltered]. Write $\bar v:\overline X'\to\overline X$. Since $A$ is
finite, two of $0,1,1+1,\ldots$ coincide, so $n1_A=0$ for some $n>0$. Thus
[lem-kun-proper-base-change-torsion-ring] applies to the proper $r$ and arbitrary $v$, with the
unbounded mate of [def-kun-unbounded-exchange]. Let $\beta:Dj'_!v'^*\to\bar v^*Dj_!$ be the
degreewise comparison of [def-weil-pbc-etale-shriek-base-change-map]. The open-specialization in
[lem-cbc-extension-zero-base-change] identifies its inverse with $\bar v^*Dj_!\to Dj'_!v'^*$: the
map $\beta$ and the inverse of the comparison in that lemma both have adjunct the open-unit map
under $Dj'_!\dashv j'^*$. For $\beta$, expand its composite-adjunction mate formula: the unit and
counit for the base-change inverse image cancel by a triangle identity, leaving the pulled-back
open unit. This is the pasting calculation of [lem-weil-pbc-mate-pasting]. Hence the adjunction
bijection identifies the specified maps. Their degreewise isomorphisms descend on every complex,
using exactness and the localization clauses in Step 1. Define
$$C^c_{f,v}=(Rr'_*\beta^{-1})\circ\operatorname{Ex}_{r,v,Dj_!}:v^*Rr_*Dj_!\longrightarrow
Rr'_*Dj'_!v'^*.$$ Both factors are natural isomorphisms on unbounded complexes. The proper
base-change theorem imposes no restriction on the residue characteristics, $v$, or the
cohomological amplitude of the input.
Dependencies: lem-cbc-compactifiable-cofiltered, lem-kun-proper-base-change-torsion-ring,
def-kun-unbounded-exchange, def-weil-pbc-etale-shriek-base-change-map,
lem-cbc-extension-zero-base-change, lem-weil-pbc-mate-pasting.

9. For a refinement $u:c_1\to c_2$, apply the base-change equation of
[lem-amb-unbounded-proper-open-interchange] to its square with proper edges $1_X,u$ and open edges
$j_1,j_2$. It states that the proper/open arrow $\gamma_u$ commutes with proper exchange and the
inverse degreewise open comparisons. Whisker that equation by the remaining proper direct image.
The proper composition/exchange compatibility proved by taking mates in Step 1, using
[def-kun-unbounded-exchange] and [lem-weil-pbc-mate-pasting], identifies the result as
$$C^{c_1}_{f,v}\circ v^*\tau_u=(\tau_{u_v}v'^*)\circ C^{c_2}_{f,v}.$$ Thus the $C^c$ commute with
every refinement comparison. Step 4, using [lem-cbc-compactifiable-cofiltered], proves agreement
under pairwise comparisons independently of the common refinement. This defines $C_{f,v}$ for the
compactification-independent functors.
Dependencies: lem-amb-unbounded-proper-open-interchange, def-kun-unbounded-exchange,
lem-weil-pbc-mate-pasting, lem-cbc-compactifiable-cofiltered.

10. For successive changes of base $Y''\xrightarrow{w}Y'\xrightarrow{v}Y$, choose $c$, then its
two successive base changes. For the proper factor, [def-kun-unbounded-exchange] defines exchange
as the mate of the inverse-image square; horizontal pasting in [lem-weil-pbc-mate-pasting] gives
$\operatorname{Ex}_{r,vw}=(\operatorname{Ex}_{r_v,w}\bar v^*)\circ(w^*\operatorname{Ex}_{r,v})$.
For the open factor the two comparisons are the same: under the adjunction $Dj''_!\dashv j''^*$
constructed in Step 1, compare the maps in the direction $Dj''_!\to(\text{inverse image})Dj_!$
before inverting them. Both the single map and the pasted pair of maps of
[def-weil-pbc-etale-shriek-base-change-map] have adjunct the composite open unit followed by the
iterated inverse-image identification. Thus those maps agree, and so do their inverses used in
$C$. The units satisfy the triangle identities, and their degreewise equations descend by Step 1.
Substituting these two equalities in Step 8's formula, with naturality to interchange the middle
factors, yields $$C_{f,vw}=(C_{f_v,w}v'^*)\circ w^*C_{f,v}.$$ For the identity base change, the
identity clause of mate pasting and the identity open unit make both factors identities. Step 9
gives the same assertions after any compactification comparisons.
Dependencies: def-kun-unbounded-exchange, lem-weil-pbc-mate-pasting,
def-weil-pbc-etale-shriek-base-change-map.

11. Finally base-change a chosen compatible tower for $(f,g)$;
[lem-cbc-compactifiable-compatible-tower] says this is again such a tower. Write $v_Z:Z'\to Z$,
$v_Y:Y'\to Y$, $v_X:X'\to X$ for projections. Expand $\alpha$ by Step 5 and $C$ by Step 8. The
resulting diagram has exactly three types of nontrivial factor squares: exchange with the
composition of proper direct images, exchange with the composition of two open extensions, and
exchange with the proper/open interchange. The first commutes by the mate-pasting calculation of
Step 1 ([def-kun-unbounded-exchange, lem-weil-pbc-mate-pasting]); the second commutes by composing
the open-unit adjuncts of Step 10, inserting the composition identification of
[lem-cbc-extension-zero-composition]. For the third, the required equality is precisely
$$(Rp'_*e_b)(\operatorname{Ex}_{p}Db_!)(v_{\overline Y}^*\Gamma_Q)
=(\Gamma_{Q'}v_V^*)(Di'_!\operatorname{Ex}_q)(e_iRq_*),$$ the base-change equation of
[lem-amb-unbounded-proper-open-interchange] for the tower square $Q=(V,b,q,p,Y,i,\overline Y)$.
Whisker this equality by the outer proper functor and the inner open extension. Composing the
three factor squares and canceling the structural identifications gives the full equality
$$C_{gf,v_Z}\circ v_Z^*\alpha_{g,f}
=(\alpha_{g',f'}v_X^*)\circ(Rg'_!C_{f,v_Y})\circ(C_{g,v_Z}Rf_!).$$ Step 6 and Step 9 then give
this equation for arbitrary compactification choices. This explicitly proves the
composition/exchange compatibility which the proof of Tag 0F7L leaves to its three factor
compatibilities.
Dependencies: lem-cbc-compactifiable-compatible-tower, def-kun-unbounded-exchange,
lem-weil-pbc-mate-pasting, lem-cbc-extension-zero-composition,
lem-amb-unbounded-proper-open-interchange.

12. Check the final bounded-below normalization on actual maps. The category of module sheaves has
enough injectives by [lem-weil-pbc-module-sheaves-enough-injectives], and
[lem-weil-pbc-dplus-injective-representative] provides bounded-below injective representatives,
which are also K-injective. Exact open extension preserves the lower bound, so bounded-below
resolutions can be chosen again after every open extension. Both bounded-below and unbounded
$Rr_*$ are then represented by $r_*I$ on the same injective resolution, naturally in the input;
equality of the induced morphisms is checked by [lem-weil-pbc-kinjective-hom-derived]. On these
representatives, the new $\Gamma$ of [lem-amb-unbounded-proper-open-interchange] and the
bounded-below $\gamma$ of [lem-cbc-proper-open-interchange-coherence] are represented by the
identical map $i_!r_*J\cong p_*k_!J\to p_*I$. Thus all refinement and tower-composition maps agree
with [lem-amb-etale-compact-comparisons]. For the proper exchange, the two constructions are the
same adjunction mate: on an injective representative $I$, the derived counit is induced by the
sheaf evaluation $r^*r_*I\to I$, and both inverse images and square isomorphisms are termwise.
Hence the unit--square--counit formula in [def-kun-unbounded-exchange] restricts to the identical
formula in [def-cbc-exchange-map]. The open factor there is the same inverse degreewise comparison
by Step 8. Therefore the whole exchange restricts to the specified map of
[thm-cbc-finite-torsion], and the already proved coherence equations restrict with it. This is
equality of the named maps; no assertion that cohomology or stalks detect equality of derived
morphisms is used.
Dependencies: lem-weil-pbc-module-sheaves-enough-injectives,
lem-weil-pbc-dplus-injective-representative, lem-weil-pbc-kinjective-hom-derived,
lem-amb-unbounded-proper-open-interchange, lem-cbc-proper-open-interchange-coherence,
lem-amb-etale-compact-comparisons, def-kun-unbounded-exchange, def-cbc-exchange-map,
thm-cbc-finite-torsion.
-/
theorem unboundedEtaleCompactSupport_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :
    IsIso (unboundedEtaleCompactSupportBaseChange A sq) ∧
    ∀ c : Compactification f,
      unboundedEtaleCompactSupportBaseChange A sq =
        Functor.whiskerRight (rightDerivedLowerShriekIso A c).inv
          (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ≫
        unboundedEtaleCompactSupportExchange A sq c ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory
          (rightDerivedLowerShriekIso A (c.ofIsPullback sq)).hom := by
  sorry

/-- The proper open-restriction map, followed by the inverse of the open unit. It is the
map called lambda in the tower normalization, formed from the specified exact-derived mate.
Source: Stacks Project, Tag 0F7B, case (b)
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleProperOpenRestriction
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] (sq : IsPullback k r p i)
    (K : DerivedCategoryModule A U) :
    (upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategory.obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) p).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj K)) ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj K :=
  (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj K) ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map
      ((asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) k).unit).inv.app K)

/-- The tower interchange has adjunct inverse to the specified proper open-restriction
exchange. The equation specifies the inverse without choosing any unrelated isomorphism.
Source: Stacks Project, Tag 0F7B, case (b)
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: steps 1 and 2 descend the open adjunction and its triangles termwise. Proper base
change makes lambda invertible, and the open unit is invertible. The two mate formulas
for the tower exchange transpose to lambda inverse by triangle identities and mate pasting.
This is equality of the actual maps, and does not use stalks to detect derived morphisms. -/
theorem unboundedEtaleCompactSupport_tower_adjunct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback k r p i) (K : DerivedCategoryModule A U) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv
        _ _ ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq.flip).app K) ≫
      unboundedEtaleProperOpenRestriction A sq K =
        𝟙 ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj K) := by
  let B := ModuleCat.{u + 1} A
  let e := mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B sq.flip
  let α := TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq.toCommSq).hom
  have := isIso_openImmersionLowerShriekBaseChangeMap B sq.flip
  have hα (M : DerivedCategoryModule A W) :
      (derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit.app
          ((upperStar B r).mapDerivedCategory.obj M) ≫
        (upperStar B k).mapDerivedCategory.map (e.hom.app M) =
      (upperStar B r).mapDerivedCategory.map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction B i).unit.app M) ≫
        α.natTrans.app ((openImmersionLowerShriek B i).mapDerivedCategory.obj M) := by
    exact Adjunction.mapDerivedCategoryAdjunction_mate
      (openImmersionLowerShriekUpperStarAdjunction B i)
      (openImmersionLowerShriekUpperStarAdjunction B k)
      (squareUpperStarIso B sq.toCommSq)
      (asIso (openImmersionLowerShriekBaseChangeMap B sq.flip.toCommSq))
      (unit_map_openImmersionLowerShriekBaseChangeMap_app B sq.flip.toCommSq) M
  have h := inverse_mates_unit
    (mapDerivedUpperStarLowerStarAdjunction B r)
    (mapDerivedUpperStarLowerStarAdjunction B p)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B k) e α hα K
  change _ ≫ ((mateEquiv (mapDerivedUpperStarLowerStarAdjunction B p)
      (mapDerivedUpperStarLowerStarAdjunction B r) α).app
        ((openImmersionLowerShriek B k).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerStar B r).map
        ((asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit).inv.app K)) = _
  dsimp only [openImmersionLowerShriekLowerStarExchange]
  rw [← Category.assoc]
  erw [h]
  dsimp only [rightDerivedLowerStar, Functor.comp_obj, Functor.comp_map, Functor.id_obj]
  rw [← Functor.map_comp]
  have hc : (derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit.app K ≫
      (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit).inv.app K = 𝟙 K :=
    (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit).hom_inv_id_app K
  rw [hc]
  exact CategoryTheory.Functor.map_id _ _


set_option backward.isDefEq.respectTransparency false in
/-- On a compactification, exchange is exactly proper exchange followed by the inverse
of the degreewise open-extension comparison, with the displayed canonical associators.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: step 8 expands the exact-functor transport in the existing exchange definition.
The proper factor becomes the exact inverse-image adjunction mate of def-kun-unbounded-exchange.
The open factor is the degreewise inverse conjugate of the sheaf exchange, hence the map
of def-weil-pbc-etale-shriek-base-change-map. Triangle identities cancel the exact-functor
transport isomorphisms. Localization descends this equation on every complex. -/
theorem unboundedEtaleCompactSupport_exchange_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback v' f' f v) (c : Compactification f) :
    unboundedEtaleCompactSupportExchange A sq c =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g v).toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
          (c.isPullback_i_ofIsPullback sq)).inv
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) (c.ofIsPullback sq).g) ≫
      (Functor.associator _ _ _).hom := by
  ext K
  have h := congrArg (fun η ↦ η.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K))
    (exact_exchange_transport A (IsPullback.of_hasPullback c.g v).toCommSq)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp only [unboundedEtaleCompactSupportExchange,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    derivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_obj, Functor.comp_map] at h ⊢
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.map_comp]
  rw [← h]
  simp only [Category.assoc]
  rw [((openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq).i).mapDerivedCategory).map_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id]
  rfl

/-- Successive changes of base give the composite exchange, with the termwise
inverse-image composition identifications.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: step 10 chooses the twice base-changed compactification. Mate pasting identifies the
proper factors for the pasted square; degreewise open-extension pasting identifies the open
factors. Naturality interchanges the adjacent factors. Conjugate by the independent
compactification comparisons to obtain the equation for the canonical functors. -/
theorem unboundedEtaleCompactSupport_baseChange_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (sq₃ : IsPullback (w' ≫ v') f'' f (w ≫ v)) :
    unboundedEtaleCompactSupportBaseChange A sq₃ =
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleUpperStarCompIso A w v).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleCompactSupportBaseChange A sq₁)
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory
        (unboundedEtaleCompactSupportBaseChange A sq₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleUpperStarCompIso A w' v').inv
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'') := by
  sorry

attribute [local irreducible] unboundedEtaleCompactSupportBaseChange

set_option backward.isDefEq.respectTransparency true in
/-- Identity base changes give identity exchange after the canonical pullback unit maps.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: step 10 expands the exchange for an identity square. The inverse-image square is the
identity, and the unit and counit cancel by their triangle identity. The open factor is
also its identity normalization. Compactification independence removes the chosen model. -/
theorem unboundedEtaleCompactSupport_baseChange_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (sq : IsPullback (𝟙 X) f f (𝟙 Y)) :
    unboundedEtaleCompactSupportBaseChange A sq ≫
        Functor.whiskerRight (unboundedEtaleUpperStarIdIso A X).hom _ ≫
        (Functor.leftUnitor _).hom =
      Functor.whiskerLeft _ (unboundedEtaleUpperStarIdIso A Y).hom ≫
        (Functor.rightUnitor _).hom := by
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let I := (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory
  let J := (upperStar (ModuleCat.{u + 1} A) (𝟙 Y)).mapDerivedCategory
  let C := unboundedEtaleCompactSupportBaseChange A sq
  have : IsIso C := (unboundedEtaleCompactSupport_baseChange A sq).1
  apply identity_exchange_of_pasting F I J C
    (unboundedEtaleUpperStarIdIso A X) (unboundedEtaleUpperStarIdIso A Y)
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X) (by simp)) ≪≫
        Functor.mapDerivedCategoryCompIso _ _)
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) (𝟙 Y) (𝟙 Y) (𝟙 Y) (by simp)) ≪≫
        Functor.mapDerivedCategoryCompIso _ _)
    (upperStar_comp_id_unit A X) (upperStar_comp_id_unit A Y)
  intro K
  have h := unboundedEtaleCompactSupport_baseChange_comp A sq sq
    (by simpa only [Category.id_comp] using sq)
  have hK := congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    unboundedEtaleUpperStarCompIso] at hK
  dsimp only [F, I, J, C]
  exact hK

/-- Base change is compatible with the specified compact-support composition maps.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: step 11 base changes a compatible tower for f and g. The proper direct-image
composition factors commute with exchange by mate pasting, the open-extension composition
factors commute degreewise, and the middle proper/open interchange commutes by its specified
base-change equation. Compose these three equations and use naturality to interchange their
whiskered factors. Tower independence and comparison independence give the stated equation. -/
theorem unboundedEtaleCompactSupport_baseChange_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' Z Z' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    [IsNoetherian Z] [IsNoetherian Z']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {vX : X' ⟶ X} {vY : Y' ⟶ Y} {vZ : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ) :
    Functor.whiskerRight (unboundedEtaleLowerShriekCompIso A f g).hom
        (upperStar (ModuleCat.{u + 1} A) vZ).mapDerivedCategory ≫
      unboundedEtaleCompactSupportBaseChange A sqgf =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleCompactSupportBaseChange A sqg) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleCompactSupportBaseChange A sqf)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g') ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) vX).mapDerivedCategory
        (unboundedEtaleLowerShriekCompIso A f' g').hom := by
  sorry

/-- The pairwise comparisons restrict to the already specified bounded-below comparisons.
Source: Stacks Project, Tags 0F7H and 0F7I
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: step 12 uses bounded-below injective representatives, which are K-injective. Both
constructions then use the same direct-image complex and the same sheaf proper/open map.
The full embedding of K-injectives into the derived category identifies these actual maps,
naturally in K. The existing compatibility isomorphisms give the displayed transport. -/
theorem unboundedEtaleCompactSupport_comparison_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom.app K) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) d).hom.app K =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app K ≫
      (rightDerivedLowerShriekOfCompactificationIso A c d).hom.app
        (DerivedCategory.Plus.ι.obj K) := by
  sorry

/-- The normalized composition comparison restricts to the existing bounded-below one.
Source: Stacks Project, Tags 0F7H--0F7K
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: step 12 computes both tower maps on common bounded-below injective representatives.
Their proper/open comparison, direct-image composition and degreewise open-extension
composition are the identical maps. The preceding comparison restriction identifies the
common-refinement factors. Compose these equalities to obtain the displayed equation. -/
theorem unboundedEtaleCompactSupport_composition_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((rightDerivedLowerShriekPlusCompIso A f g).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (f ≫ g)).hom.app K =
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).hom.app
        ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom.app K) ≫
      (unboundedEtaleLowerShriekCompIso A f g).hom.app (DerivedCategory.Plus.ι.obj K) := by
  sorry

/-- The compactification-relative exchange restricts to the specified finite-torsion
bounded-below exchange, with the same proper and degreewise open normalizations.
Source: Stacks Project, Tags 0F7H and 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: step 12 represents the proper counit by evaluation on one common bounded-below
injective resolution. Both proper exchanges are its unit--square--counit mate, with the same
termwise square. The inverse open factor is the same degreewise comparison. Hence their
composites agree on the nose after the canonical inclusion compatibility isomorphisms.
Comparison independence and the preceding comparison restriction give the same conclusion
for compactification-independent exchange. This checks equality of morphisms via
K-injective representatives, rather than claiming cohomology detects their equality. -/
theorem unboundedEtaleCompactSupport_exchange_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback v' f' f v) (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c).app K) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).hom.app
          ((upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategoryPlus.obj K) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (c.ofIsPullback sq)).map
          ((upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategoryPlusCompatibility.hom.app K) =
    (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlusCompatibility.hom.app
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).hom.app K) ≫
      (unboundedEtaleCompactSupportExchange A sq c).app (DerivedCategory.Plus.ι.obj K) := by
  sorry

/-- The open factor used above is precisely the specified inverse-conjugate beta map of
extension by zero, specialized to the canonical fibre product. Termwise descent therefore
uses that named map and its inverse, with its prescribed orientation.
Source: Stacks Project, Tags 03S6 and 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: expand both definitions as inverse conjugates under the two composite adjunctions.
The open sum extension is the existing open-immersion extension. Both right-adjoint maps
are the same underived exchange of the same cartesian square. The adjunction hom bijection
therefore identifies the two beta maps. Descend the equality degreewise as in step 8. -/
theorem unboundedEtaleCompactSupport_open_beta
    (A : Type (u + 1)) [CommRing A]
    {U Y Y' : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] (v : Y' ⟶ Y) :
    openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback v j).flip.toCommSq =
      etaleLowerShriekBaseChangeMap A v j := by
  rfl

end AlgebraicGeometry.Etale
