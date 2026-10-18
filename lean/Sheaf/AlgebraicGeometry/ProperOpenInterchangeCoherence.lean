/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import Sheaf.AlgebraicGeometry.ProperOpenComparison
public import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
public import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeRefinementNormalization
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeComposition
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeBaseChange
import Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import Sheaf.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Proper/open interchange and its coherence

Source: Stacks Project, More on Étale Cohomology, Tags 0F7B, 0F7C, 0F7D, 0F7F
(blueprint: lem-cbc-proper-open-interchange-coherence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


private theorem ordinaryInterchange (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
        (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
        [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i),
        lowerStar (ModuleCat.{u + 1} Λ) r ⋙ openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ≅
          openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙ lowerStar (ModuleCat.{u + 1} Λ) p),
      ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
        (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
        [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
        (F : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app
            ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F := by
  classical
  obtain ⟨L, ι, hι, hp, ho, c, e, hc, he, hce⟩ := properSupportSheafComposition Λ
  have hproper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : IsIso (ι f) := by
    have : ∀ F, IsIso ((ι f).app F) := hp X Y f
    exact NatIso.isIso_of_isIso_app _
  let c' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
      (fg : X ⟶ Z) [IsSeparated fg] [LocallyOfFiniteType fg] (w : fg = f ≫ g) :
      L f ⋙ L g ≅ L fg := by
    subst fg
    exact c X Y Z f g
  have hc' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
      (fg : X ⟶ Z) [IsSeparated fg] [LocallyOfFiniteType fg] (w : fg = f ≫ g)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      (c' f g fg w).hom.app F ≫ (ι fg).app F =
        (ι g).app ((L f).obj F) ≫ (lowerStar (ModuleCat.{u + 1} Λ) g).map
          ((ι f).app F) ≫ (lowerStarComp (ModuleCat.{u + 1} Λ) f g fg w).hom.app F := by
    subst fg
    exact hc X Y Z f g F
  let δ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
      (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :=
    have := hproper r
    have := hproper p
    Functor.isoWhiskerRight (asIso (ι r)).symm _ ≪≫
      Functor.isoWhiskerLeft _ (ho C D i).choose ≪≫ c' r i (k ≫ p) h ≪≫ (c A B D k p).symm ≪≫
      Functor.isoWhiskerRight (ho A B k).choose.symm _ ≪≫
      Functor.isoWhiskerLeft _ (asIso (ι p))
  refine ⟨δ, ?_⟩
  intro A B C D k i r p _ _ _ _ h F
  have := hproper r
  have := hproper p
  have hok := congr_app (ho A B k).choose_spec F
  have hoi := congr_app (ho C D i).choose_spec ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F)
  dsimp only [NatTrans.comp_app] at hok hoi
  dsimp [δ]
  simp only [Category.assoc]
  rw [← (ι p).naturality_assoc, ← Functor.map_comp_assoc, ← hok,
    Iso.inv_hom_id_app_assoc, (ι p).naturality_assoc, ← hc A B D k p F,
    Iso.inv_hom_id_app_assoc,
    hc' r i (k ≫ p) h F]
  rw [(ho C D i).choose.hom.naturality_assoc, (ι i).naturality_assoc,
    ← Functor.map_comp_assoc]
  simp only [← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]
  rw [← hoi, Category.assoc]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem derivedBaseChange_fac_app
    {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
    [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
    [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [EnoughInjectives B] [EnoughInjectives B']
    {G : B ⥤ C} {G' : B' ⥤ C'} {P : B ⥤ B'} {Q : C ⥤ C'}
    [G.Additive] [G'.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (e : G ⋙ Q ⟶ P ⋙ G') (J : HomotopyCategory.Plus B) :
    Q.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnit.app J) ≫
      (Functor.rightDerivedFunctorPlusBaseChange e).app (DerivedCategory.Plus.Qh.obj J) =
    Q.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj J) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app J) ≫
      G'.rightDerivedFunctorPlusUnit.app (P.mapHomotopyCategoryPlus.obj J) ≫
      G'.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app J) := by
  have hfac := NatTrans.congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac e) J
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] at hfac
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp] at hfac
  exact hfac


private theorem acyclic_of_homology_vanishing
    {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C] [EnoughInjectives B]
    (G : B ⥤ C) [G.Additive] (F : B)
    (h : ∀ n : ℕ, IsZero ((DerivedCategory.Plus.homologyFunctor C (n + 1)).obj
      (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj F)))) :
    G.rightAcyclic F := by
  intro n
  exact (h n).of_iso (G.homologyRightDerivedFunctorPlusObjSingleFunctorIso F (n + 1)).symm

private theorem derivedInterchange (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
    (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (δ : lowerStar (ModuleCat.{u + 1} Λ) r ⋙ openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙ lowerStar (ModuleCat.{u + 1} Λ) p) :
    IsIso (Functor.rightDerivedFunctorPlusBaseChange
        (G := lowerStar (ModuleCat.{u + 1} Λ) r)
        (G' := lowerStar (ModuleCat.{u + 1} Λ) p)
        (β := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
        (γ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) δ.hom) := by
  have hacyclic (J : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
      (lowerStar (ModuleCat.{u + 1} Λ) p).rightAcyclic
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj J) := by
    apply acyclic_of_homology_vanishing
    intro n
    exact isZero_higherDirectImage_openImmersionLowerShriek_injective
      Λ k i r p h J (n + 1) (by omega)
  exact Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (G := lowerStar (ModuleCat.{u + 1} Λ) r)
    (G' := lowerStar (ModuleCat.{u + 1} Λ) p)
    (β := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (γ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) δ hacyclic

private theorem normalized_iso_square
    {C : Type*} [Category* C] {X Y Z : C} (a : X ≅ Y) (b : Z ≅ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : a.inv ≫ f = g) (hg : g ≫ b.hom = 𝟙 Y) :
    f ≫ b.hom = a.hom := by
  apply (cancel_epi a.inv).1
  rw [← Category.assoc, h, hg, a.inv_hom_id]

private theorem derived_identity_of_refinement
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B : Scheme.{u}} (k : A ⟶ B) [IsOpenImmersion k]
    (δ : lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B))
    (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) A).inv.app K) ≫
        (Functor.rightDerivedFunctorPlusBaseChange
        (G := lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A))
        (G' := lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B))
        (β := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
        (γ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) δ.hom).app K =
      properOpenComparison Λ (𝟙 B) k k (Category.comp_id k) K) :
    (Functor.rightDerivedFunctorPlusBaseChange
        (G := lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A))
        (G' := lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B))
        (β := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
        (γ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) δ.hom).app K ≫
        (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) B).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) A).hom.app K) := by
  let E := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus
  exact normalized_iso_square
    (E.mapIso ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) A).app K))
    ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) B).app (E.obj K))
    ((Functor.rightDerivedFunctorPlusBaseChange
        (G := lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A))
        (G' := lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B))
        (β := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
        (γ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) δ.hom).app K)
    (properOpenComparison Λ (𝟙 B) k k (Category.comp_id k) K) h
    (properOpenComparison_id Λ k K)

-- Preserve the binder names of the existing public interface.
set_option linter.unusedVariables false in
/-- The canonical proper/open interchange isomorphism, normalized by the derived units,
with refinement normalization, vertical and horizontal composition, identities and base change.
The ordinary isomorphism `δ` is fixed by equality in the common ordinary direct image.
The unit equation is the resolution-independent form of the K-injective normalization:
on an injective representative the left unit is invertible; the right unit is represented
by applying `p_*` to a K-injective replacement of `k_!J`.
Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F
(blueprint: lem-cbc-proper-open-interchange-coherence).

Proof:
1. Use properSupportSheafComposition to identify each proper direct image and each
open extension with its proper-support functor. Compose through the common morphism
k ≫ p = r ≫ i. Its inclusion/composition equations give exactly the ordinary
normalization displayed below, without a Cartesian hypothesis.
2. Open-extended injectives are acyclic for p*. The homology/classical-derived
comparison converts this to the source rightAcyclic predicate. The proved source
rightDerivedFunctorPlusBaseChange acyclicity criterion makes the canonical derived
transformation invertible. The canonical asIso constructor supplies an isomorphism
with this prescribed hom; an isomorphism is uniquely determined by its hom, so this
choice introduces no arbitrary data. Evaluating its unit factorization gives the
second displayed equation, on every bounded-below homotopy-category object.
3. Apply the refinement-normalization subargument to this normalized ordinary map.
4. Apply the formal composition subargument to obtain both pasting equations and the
horizontal identity. These statements concern the already specified canonical
transformation, and do not repeat the construction or its invertibility.
5. For the vertical identity, specialize refinement normalization to the identity
proper map, compose with lowerStarIdDerivedPlus, and apply properOpenComparison_id.
Cancel the isomorphism given by extension of the inverse source identity compositor.
6. The base-change subargument proves the ordinary cube by cancellation into the
common direct image. The proved generic right-derived cube then lifts it. Its exact
comparison isomorphisms are the specified extensionZeroBaseChangeDerivedPlusIso,
and its two other derived faces are definitionally derivedBaseChangeMapPlus.
-/
theorem properOpenInterchangeCoherence (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
      (γ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅ (openImmersionLowerShriek (ModuleCat.{u +
        1} Λ) k).mapDerivedCategoryPlus ⋙ (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p)),
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (J :
        HomotopyCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map ((lowerStar
        (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusUnit.app J) ≫
        (γ k i r p h).hom.app (DerivedCategory.Plus.Qh.obj J) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusFactorsh.hom.app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomotopyCategoryPlus.obj J) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus (δ k i r p h).hom).app J) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusUnit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomotopyCategoryPlus.obj J) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).map ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlusFactorsh.inv.app J)) ∧
    (∀ {T₁ T₂ X : Scheme.{u}} (p : T₁ ⟶ T₂) [IsProper p]
      (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (h : j₁ ≫ p = j₂) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app K) ≫
        (γ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp j₂).symm)).hom.app K =
      properOpenComparison Λ p j₁ j₂ h K) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) r₁) (lowerStar
        (ModuleCat.{u + 1} Λ) r₂) (lowerStarComp (ModuleCat.{u + 1} Λ) r₁ r₂)).hom.app K) ≫
        (γ k j (r₁ ≫ r₂) (p₁ ≫ p₂) h).hom.app K ≫
        (Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) p₁) (lowerStar
        (ModuleCat.{u + 1} Λ) p₂) (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂)).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (γ i j r₂ p₂ h₂).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r₁).obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₂).map ((γ k i r₁ p₁ h₁).hom.app K)) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (l : B ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j))
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroCompDerivedPlusIso Λ i j).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1}
        Λ) r).obj K) ≫
        (γ (k ≫ l) (i ≫ j) r q h).hom.app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) q).map ((extensionZeroCompDerivedPlusIso Λ
        k l).inv.app K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map ((γ k i r p
        h₁).hom.app K) ≫
        (γ l j p q h₂).hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        k).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {A B : Scheme.{u}} (k : A ⟶ B) [IsOpenImmersion k]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (γ k k (𝟙 A) (𝟙 B) ((Category.comp_id k).trans (Category.id_comp k).symm)).hom.app K ≫
        (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) B).hom.app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) A).hom.app K)) ∧
    (∀ {A C : Scheme.{u}} (r : A ⟶ C) [IsProper r]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (γ (𝟙 A) (𝟙 C) r r ((Category.id_comp r).trans (Category.comp_id r).symm)).hom.app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).map
        ((Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 A)) (upperStarId
        (ModuleCat.{u + 1} Λ) A)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app K) =
      (Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 C)) (upperStarId
        (ModuleCat.{u + 1} Λ) C)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj K)) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ {A₁ B₁ C₁ D₁ :
        Scheme.{u}}
      (a : B₁ ⟶ B) (b : D₁ ⟶ D) (c : C₁ ⟶ C) (d : A₁ ⟶ A)
      (k₁ : A₁ ⟶ B₁) (i₁ : C₁ ⟶ D₁) (r₁ : A₁ ⟶ C₁) (p₁ : B₁ ⟶ D₁)
      [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
      (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sr : IsPullback d r₁ r c) (sp : IsPullback a p₁ p b)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.map ((γ k i r p h).hom.app K) ≫
        (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sp.toCommSq).app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₁).map
        ((extensionZeroBaseChangeDerivedPlusIso Λ sk).hom.app K) =
      (extensionZeroBaseChangeDerivedPlusIso Λ si).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u
        + 1} Λ) r).obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sr.toCommSq).app K) ≫
        (γ k₁ i₁ r₁ p₁ h₁).hom.app ((upperStar (ModuleCat.{u + 1} Λ) d).mapDerivedCategoryPlus.obj
        K)) := by
  classical
  let δ := @Exists.choose _ _ (ordinaryInterchange Λ)
  have hδ := @Exists.choose_spec _ _ (ordinaryInterchange Λ)
  let γ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
      (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
      rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r ⋙
          (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
          rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p :=
    @asIso _ _ _ _ (Functor.rightDerivedFunctorPlusBaseChange
      (G := lowerStar (ModuleCat.{u + 1} Λ) r)
      (G' := lowerStar (ModuleCat.{u + 1} Λ) p)
      (β := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
      (γ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) (δ k i r p h).hom)
      (derivedInterchange Λ k i r p h (δ k i r p h))
  have href := @properOpenInterchange_refinement_normalization Λ _ _ @δ @hδ
  have hcomp := properOpenInterchange_composition Λ @δ @hδ
  refine ⟨@δ, @γ, @hδ, ?_, @href, hcomp.1, hcomp.2.1, ?_, hcomp.2.2,
    @properOpenInterchange_baseChange Λ _ _ @δ @hδ⟩
  · intro A B C D k i r p _ _ _ _ h J
    exact derivedBaseChange_fac_app
      (G := lowerStar (ModuleCat.{u + 1} Λ) r)
      (G' := lowerStar (ModuleCat.{u + 1} Λ) p)
      (P := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
      (Q := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) (δ k i r p h).hom J
  · intro A B k _ K
    exact derived_identity_of_refinement Λ k
      (δ k k (𝟙 A) (𝟙 B) ((Category.comp_id k).trans (Category.id_comp k).symm)) K
      (href (𝟙 B) k k (Category.comp_id k) K)

end AlgebraicGeometry.Etale
