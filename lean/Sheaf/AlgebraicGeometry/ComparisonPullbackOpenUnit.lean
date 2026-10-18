/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Open-restriction normalization for the comparison adjunction unit

Source: literature/stacks-project/sites.tex, Tag 00WX (lemma-adjoint-sheaves),
with the open restriction normalization extracted from the comparison-pullback
construction (blueprint: lem-pur-comparison-pullback-open-unit).

The comparison `gamma` is the canonical conjugate of the sectionwise identity
on direct images.  Its inverse is `a`, and `c` is the fixed restriction
identification between the two direct-image composites.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The canonical comparison `gamma` for an open immersion, obtained by the
conjugate construction from the sectionwise direct-image identity.
Source: Stacks Project, Tag 00WX; (blueprint: lem-pur-comparison-pullback-open-unit). -/
noncomputable abbrev comparisonPullbackOpenUnitGamma (A : Type (u + 1)) [CommRing A]
    [Finite A] {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] :
    Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) V ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j :=
  openComparisonRestrictionIso A j

/-- The inverse `a = gamma⁻¹` of the canonical open comparison.
Source: Stacks Project, Tag 00WX; (blueprint: lem-pur-comparison-pullback-open-unit). -/
noncomputable abbrev comparisonPullbackOpenUnitA (A : Type (u + 1)) [CommRing A]
    [Finite A] {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] :
    comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j ≅
      Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) V :=
  (comparisonPullbackOpenUnitGamma A j).symm

/-- The fixed restriction identification `c` on direct images.
Source: Stacks Project, Tag 00WX; (blueprint: lem-pur-comparison-pullback-open-unit). -/
noncomputable abbrev comparisonPullbackOpenUnitC (A : Type (u + 1)) [CommRing A]
    [Finite A] {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] :
    comparisonLowerStar (ModuleCat.{u + 1} A) T ⋙
        Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ≅
      ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonLowerStar (ModuleCat.{u + 1} A) V :=
  comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j

/-- For every etale module sheaf `F` on `T`, the comparison adjunction unit
is preserved by restriction to the open `V`.  The first map is the etale
restriction of `eta^T_F`; `c` is the fixed sectionwise restriction
identification; and `a = gamma⁻¹`, where `gamma` is the conjugate of the
sectionwise direct-image identity.

Source: literature/stacks-project/sites.tex, Tag 00WX (lemma-adjoint-sheaves),
and the open restriction normalization of the comparison pullback
(blueprint: lem-pur-comparison-pullback-open-unit).

Proof: identify both right adjoints on an etale object over `V` with the
sections on its fibre product with `V`, so `c` is the identity.  Expand the
units of the two composite adjunctions and apply the conjugate-isomorphism
unit equation to the canonical comparison `gamma`.  Evaluate the resulting
identity on every etale object over `V` and cancel `gamma` using `a = gamma⁻¹`.
This gives the displayed equality, and equality on all components is equality
of sheaf morphisms.
(blueprint: lem-pur-comparison-pullback-open-unit). -/
theorem comparisonPullbackOpenUnit (A : Type (u + 1)) [CommRing A]
    [Finite A] {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] :
    ∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map
          ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F) ≫
        (comparisonPullbackOpenUnitC A j).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) V).map
          ((comparisonPullbackOpenUnitA A j).hom.app F) =
      (comparisonAdjunction (ModuleCat.{u + 1} A) V).unit.app
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F) := by
  sorry

end AlgebraicGeometry.ProEtale
