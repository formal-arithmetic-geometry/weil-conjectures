/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear

/-!
# Inverse image and restriction for composable open immersions

Source: Stacks Project, sites.tex Tag 03EH (lemma-relocalize), together with
etale-cohomology.tex after Definition 03S3 (blueprint:
lem-cbc-open-inverse-image-restriction-composition).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- For composable open immersions, the canonical inverse-image composition comparison is
compatible with the identifications of inverse image with restriction. Source: Stacks
Project, Tag 03EH and the restriction description after Definition 03S3
(blueprint: lem-cbc-open-inverse-image-restriction-composition).

Proof: evaluate both restriction functors on an étale object `T ⟶ V`; both are given by
restriction of sections of `G` along the same composite `T ⟶ V ⟶ U ⟶ X`, so their
composition is strict. The extension-by-zero adjunction identifies the unit of inverse
image with this restriction map. The unit equation characterizing the canonical
composition comparison, together with the module-linear inverse-image-composition
statement, then identifies the two displayed composites. This is natural in `G` and uses
no finiteness or torsion hypothesis on `Λ`.
-/
theorem openInverseImageRestrictionComposition
    {Λ : Type (u + 1)} [CommRing Λ]
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} Λ) k).obj
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} Λ) j).obj G) =
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} Λ) (k ≫ j)).obj G ∧
    (@Etale.upperStarComp (ModuleCat.{u + 1} Λ) _ _
      (ModuleCat.isGrothendieckAbelian_of_commRing Λ) _ _ _ k j (k ≫ j) rfl).inv.app G ≫
      (@Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) _ _
        (ModuleCat.isGrothendieckAbelian_of_commRing Λ) _ _ (k ≫ j)).hom.app G =
      (@Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) _ _
        (ModuleCat.isGrothendieckAbelian_of_commRing Λ) _ _ k).hom.app
        ((@Etale.upperStar (ModuleCat.{u + 1} Λ) _ _
          (ModuleCat.isGrothendieckAbelian_of_commRing Λ) _ _ j).obj G) ≫
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} Λ) k).map
        ((@Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) _ _
          (ModuleCat.isGrothendieckAbelian_of_commRing Λ) _ _ j).hom.app G) := by
  sorry

end AlgebraicGeometry.Etale
