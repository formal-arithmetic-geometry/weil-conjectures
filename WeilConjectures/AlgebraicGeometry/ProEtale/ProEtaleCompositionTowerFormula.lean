/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions

/-! # The canonical origin compositor on a compatible proper/open tower

Source: thm-sf-comp-composition, Construction; Stacks Tag 0F7J
(blueprint: lem-trf-proetale-composition-tower-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The composition formula, separated from invertibility for all etale-origin inputs.
Source: thm-sf-comp-composition, Construction, and Stacks Tag 0F7J
(blueprint: lem-trf-proetale-composition-tower-formula).

Proof: Let a=e.restrict.i and b=pullback.fst e.g d.i. In bounded-below coordinates
use properOpenSiteExtensionIso at a to identify J_a nu^*L with the explicit witness
nu^*(a_!L). The proper/open site mate identifies its specified interchange with the
open adjunct of inverse restriction exchange. Transport the exact open unit and the
derived direct-image compatibility through the bounded-below inclusion; the resulting
restriction map is towerLambda, so injectivity of the open Hom equivalence identifies
the interchange with towerGamma. The proper compositor restricts to the inverse of
finiteDirectImageComposition, by derived composition compatibility. The exact open
compositor restricts to towerOpenComposition, since both are conjugate to composite
restriction under the two open adjunctions. Insert e.restrict_i_fst at the final open.
The finite-site tower pasting equation now computes the compositor as the three
maps on the right. Finally expand towerOriginComposition: precomposition by the
etale-origin equivalence evaluates each towerCandidateComparison to its specified
site-conjugated etale change of compactification. Naturality moves the middle change
through the witness isomorphism. The adjacent boundary comparisons cancel, leaving
precisely the same finite-site tower compositor. This proves equality for the given
canonical origin map, without inferring invertibility from the adjunction.
-/
theorem proEtaleCompositionTowerFormula [Finite Λ]
    {U V W : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian W]
    (h : U ⟶ V) (f : V ⟶ W)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : Compactification f) (e : Compactification (h ≫ d.i))
    [IsNoetherian d.Z] [IsNoetherian e.Z] [IsNoetherian e.restrict.Z]
    (L : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hLambda : IsIso (towerLambda Λ (pullback.fst e.g d.i) d.i e.restrict.g e.g
      e.isPullback_restrict.w.symm ((towerJ Λ e.restrict.i).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj L.obj)))) :
    let b := pullback.fst e.g d.i
    let N := (towerJ Λ e.restrict.i).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj L.obj)
    towerOriginComposition Λ h f d e L =
      (towerP Λ d.g).map
          (towerGamma Λ b d.i e.restrict.g e.g e.isPullback_restrict.w.symm N hLambda) ≫
        (finiteDirectImageComposition Λ e.g d.g).inv.app ((towerJ Λ b).obj N) ≫
        (towerP Λ (e.g ≫ d.g)).map
          ((towerOpenComposition Λ e.restrict.i b ≪≫
            towerOpenCongr Λ e.restrict_i_fst).hom.app
              ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj
                L.obj)) := by sorry

end AlgebraicGeometry.ProEtale
