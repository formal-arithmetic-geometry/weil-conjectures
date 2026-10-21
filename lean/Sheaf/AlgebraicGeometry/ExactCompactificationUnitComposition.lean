/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.ExactCompactificationUnit
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-!
# Compatibility of normalized exact compact-support units with composition

Source: Stacks Project, Tags 0F7B, 0F7J and 0D6E
(blueprint: lem-sfb-exact-compactification-unit-composition).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The inverse normalized units respect the proper/open composition map.
Source: Stacks Project, Tags 0F7B, 0F7J and 0D6E
(blueprint: lem-sfb-exact-compactification-unit-composition).

Proof: choose a compatible proper/open tower for h,e. On a homotopy representative J,
resolve j!J to I and then b!I to M. Proper direct image preserves K-injectives, so resolve
i!q*I to L and lift its proper/open comparison to p*M. Naturality of the section-preserving
sheaf identification and its normalization into ordinary direct image identify the two
paths after applying s*. The equality of resolution paths is precisely
properOpenTowerDerivedUnit. The composite b!j!J to b!I to M is a K-injective resolution
because b! is exact. The derived-composition normalization therefore identifies the
successive units with the single unit, after D(sigma). Localization descends the equality
on all representatives. Refinement compatibility transports it from the tower to the
chosen compactifications. Finally invert the three units and cancel their invertible
whiskerings. This gives exactly the displayed equation. -/
theorem exactCompactificationUnit_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T B : Scheme.{u}} [IsNoetherian V] [IsNoetherian T] [IsNoetherian B]
    (h : V ⟶ T) (e : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (ιh : F ⟶ lowerStar (ModuleCat.{u + 1} A) h)
    (ιe : G ⟶ lowerStar (ModuleCat.{u + 1} A) e)
    (ιhe : H ⟶ lowerStar (ModuleCat.{u + 1} A) (h ≫ e))
    (ah : ∀ c : Compactification h, F ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (ae : ∀ c : Compactification e, G ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (ahe : ∀ c : Compactification (h ≫ e), H ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (nh : ∀ c, (ah c).hom ≫ compactificationSheafToDirectImage A c = ιh)
    (ne : ∀ c, (ae c).hom ≫ compactificationSheafToDirectImage A c = ιe)
    (nhe : ∀ c, (ahe c).hom ≫ compactificationSheafToDirectImage A c = ιhe)
    (ch : ∀ c : Compactification h,
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        F.mapDerivedCategory)
    (ce : ∀ c : Compactification e,
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        G.mapDerivedCategory)
    (che : ∀ c : Compactification (h ≫ e),
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        H.mapDerivedCategory)
    (uh : ∀ c, (ch c).inv = exactCompactificationUnit A c F (ah c))
    (ue : ∀ c, (ce c).inv = exactCompactificationUnit A c G (ae c))
    (uhe : ∀ c, (che c).inv = exactCompactificationUnit A c H (ahe c))
    (σ : F ⋙ G ≅ H)
    (nσ : ∀ M, σ.hom.app M ≫ ιhe.app M =
      ιe.app (F.obj M) ≫ (lowerStar (ModuleCat.{u + 1} A) e).map (ιh.app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app M) :
    (unboundedEtaleLowerShriekCompIso A h e ≪≫
      (rightDerivedLowerShriekIso A
        (HasCompactification.compactification (h ≫ e))).symm ≪≫
      che (HasCompactification.compactification (h ≫ e))) =
    (Functor.isoWhiskerRight
        ((rightDerivedLowerShriekIso A
          (HasCompactification.compactification h)).symm ≪≫
          ch (HasCompactification.compactification h))
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) e) ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory
        ((rightDerivedLowerShriekIso A
          (HasCompactification.compactification e)).symm ≪≫
          ce (HasCompactification.compactification e)) ≪≫
      (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso σ) := by
  sorry

end AlgebraicGeometry.Etale
