/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U5
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGraphChosenComparisons
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

/-! # Component of proper-first graph normalization

This is the K-injective component calculation in the proof of
`graph_proper_precomposition_unit` (blueprint: lem-pur-graph-proper-precomposition-unit).
It isolates the objectwise geometric calculation; natural-transformation extensionality is
handled in the parent module.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor canonicalEtaleCompactSupportComparison
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

/-- The representative graph equation after postcomposition by the codomain identity.
Source: Stacks Project, Tags 0F7B, 0F7I and 0F7J; representative-complex normalization.

Proof in words: isolate the remaining representative-complex geometric calculation after
postcomposing by the codomain identity. The parent component equation cancels this identity.
(blueprint: lem-pur-graph-proper-precomposition-unit-component-core-after-identity).
-/
theorem graph_proper_precomposition_unit_component_on_complex_after_identity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    {f : W ⟶ Y} (hf : f = q ≫ v) [HasCompactification f]
    (c : Compactification f)
    (τ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hτ : ∀ F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A),
      τ.app F ≫ (compactificationSheafToDirectImage A c).app F =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) q v f hf).hom.app F)
    (K : HomologicalComplex
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    𝟙 _ ≫
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit
        (lowerStar (ModuleCat.{u + 1} A) q)
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance) ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
            (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
          Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
            (graphChosenEtaleComparison A v).symm ≪≫
          unboundedEtaleLowerShriekCompIso A q v ≪≫
          unboundedEtaleLowerShriekCongr A hf.symm ≪≫
          (rightDerivedLowerShriekIso A c).symm).hom).app
      ((HomotopyCategory.quotient
        (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).obj K) =
      𝟙 _ ≫
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (.up ℤ))
          DerivedCategory.Qh ≫
        Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
          (lowerStar (ModuleCat.{u + 1} A) c.g)).app
        ((HomotopyCategory.quotient
          (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).obj K) := by
  sorry

end AlgebraicGeometry.Etale
