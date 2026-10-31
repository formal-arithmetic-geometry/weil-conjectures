/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestrictionData

/-! # Finite evaluation of normalized compact-support restriction

Source: Stacks 03DI and 0D6E; Zheng Construction 4.1; the coefficient-composition detail
(blueprint: def-sp-system-compact-support-restriction-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

variable {l : ℕ}

/-- The actual coefficient map at a finite level.
Source: Zheng 4.1 (blueprint: def-sp-system-compact-support-restriction-evaluation). -/
abbrev levelMap (W : Scheme.{u}) {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ) :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (ProEt.topology W) CommRingCat.{u + 1}).map (a.app (op n))

/-- Finite-level exact restriction, using the existing module-sheaf restriction.
Source: Stacks 03CZ (blueprint: def-sp-system-compact-support-restriction-evaluation). -/
abbrev levelRestriction (W : Scheme.{u}) {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ) :=
  (res.{u + 1, u, u + 1} (levelMap W a n)).mapDerivedCategory

/-- Compatibility of the actual constant-ring pullback maps, not an extra geometric datum.
Source: Stacks 03CZ (blueprint: def-sp-system-compact-support-restriction-evaluation). -/
def LevelComm {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) : Prop :=
  (StrictTower.constantRingIso (levels B n) f).hom ≫ levelMap X a n =
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (levelMap Y a n) ≫
      (StrictTower.constantRingIso (levels C n) f).hom

/-- The existing, normalized finite inverse-image comparison.
Source: Stacks 0D6D (blueprint: def-sp-system-compact-support-restriction-evaluation). -/
def levelPull {B C : Etale.SystemProjection.Coefficients.{u} l}
    {a : B.rings ⟶ C.rings} {X Y : Scheme.{u}} {f : X ⟶ Y} {n : ℕ}
    (h : LevelComm a f n) :=
  proEtaleRingRestrictionDerivedPullback f
    (VaryingRing.coefficients (levels B) Y n) (VaryingRing.coefficients (levels C) Y n)
    (VaryingRing.coefficients (levels B) X n) (VaryingRing.coefficients (levels C) X n)
    (levelMap Y a n) (levelMap X a n)
    (StrictTower.constantRingIso (levels B n) f)
    (StrictTower.constantRingIso (levels C n) f) h

/-- The existing finite proper comparison, with its K-injective/unit normalization.
Source: Stacks 0D6E (blueprint: def-sp-system-compact-support-restriction-evaluation). -/
def levelProper {B C : Etale.SystemProjection.Coefficients.{u} l}
    {a : B.rings ⟶ C.rings} {X Y : Scheme.{u}} {f : X ⟶ Y} {n : ℕ}
    (h : LevelComm a f n) :=
  (proEtaleRingRestrictionDerivedDirectImage f
    (VaryingRing.coefficients (levels B) Y n) (VaryingRing.coefficients (levels C) Y n)
    (VaryingRing.coefficients (levels B) X n) (VaryingRing.coefficients (levels C) X n)
    (levelMap Y a n) (levelMap X a n)
    (StrictTower.constantRingIso (levels B n) f)
    (StrictTower.constantRingIso (levels C n) f) h).symm

/-- Finite evaluation agrees with the specified finite open/proper comparisons.
The open comparison is fixed by the original derived open-adjunction units; the proper
comparison is the existing normalized ring-sheaf change comparison, not an arbitrary iso.
These equations assert compatibility, not faithfulness of evaluation.
Source: Stacks 03DI, 0D6E; proof step 7
(blueprint: def-sp-system-compact-support-restriction-evaluation). -/
structure FiniteCompatibility {B C : Etale.SystemProjection.Coefficients.{u} l}
    {a : B.rings ⟶ C.rings} {X Z Y : Scheme.{u}}
    {j : X ⟶ Z} [IsOpenImmersion j] {p : Z ⟶ Y} (d : Comparison a j p) where
  openComm : ∀ n : ℕ, LevelComm a j n
  properComm : ∀ n : ℕ, LevelComm a p n
  openIso : ∀ n : ℕ,
    levelRestriction X a n ⋙ (StrictTower.moduleJ (levels B n) j).mapDerivedCategory ≅
      (StrictTower.moduleJ (levels C n) j).mapDerivedCategory ⋙ levelRestriction Z a n
  openNormalized : ∀ (n : ℕ) (M : DerivedCategory (StrictTower.Modules (levels C n) X)),
    (VaryingRing.levelJAdj (levels B) j n).unit.app ((levelRestriction X a n).obj M) ≫
      (StrictTower.modulePullback (levels B n) j).mapDerivedCategory.map
        ((openIso n).hom.app M) ≫
      (levelPull (openComm n)).inv.app
        ((StrictTower.moduleJ (levels C n) j).mapDerivedCategory.obj M) =
    (levelRestriction X a n).map ((VaryingRing.levelJAdj (levels C) j n).unit.app M)
  openEvaluation : ∀ (n : ℕ) (M : VaryingRing.Derived (levels C) (steps C) X),
    (VaryingRing.ev (levels B) (steps B) Z n).map (d.openPart.derived.hom.app M) ≫
      (restrictionEvaluation Z a n).hom.app ((VaryingRing.J (levels C) (steps C) j).obj M) ≫
      (levelRestriction Z a n).map ((VaryingRing.evalJ (levels C) (steps C) j n).hom.app M) =
    (VaryingRing.evalJ (levels B) (steps B) j n).hom.app
        ((derivedRestriction X a).obj M) ≫
      (StrictTower.moduleJ (levels B n) j).mapDerivedCategory.map
        ((restrictionEvaluation X a n).hom.app M) ≫
      (openIso n).hom.app ((VaryingRing.ev (levels C) (steps C) X n).obj M)
  properEvaluation : ∀ (n : ℕ) (M : VaryingRing.Derived (levels C) (steps C) Z),
    (VaryingRing.ev (levels B) (steps B) Y n).map (d.properPart.iso.hom.app M) ≫
      (restrictionEvaluation Y a n).hom.app ((VaryingRing.P (levels C) (steps C) p).obj M) ≫
      (levelRestriction Y a n).map ((VaryingRing.evalP (levels C) (steps C) p n).hom.app M) =
    (VaryingRing.evalP (levels B) (steps B) p n).hom.app
        ((derivedRestriction Z a).obj M) ≫
      (StrictTower.moduleDirectImage (levels B n) p).rightDerivedFunctor.map
        ((restrictionEvaluation Z a n).hom.app M) ≫
      (levelProper (properComm n)).hom.app ((VaryingRing.ev (levels C) (steps C) Z n).obj M)

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
