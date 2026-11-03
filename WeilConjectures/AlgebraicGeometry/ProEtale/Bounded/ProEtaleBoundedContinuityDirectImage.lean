/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedComplexDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Bounded-below filtered-colimit continuity of pro-etale direct images

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity,
`det-pe-bounded-continuity-direct-image.md` (blueprint:
`det-pe-bounded-continuity-direct-image`).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The module direct image over the direct-image coefficient sheaf.
Source: the Weil conjectures blueprint, `det-pe-bounded-continuity-direct-image`
(blueprint: det-pe-bounded-continuity-direct-image). -/
noncomputable def ringModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ⥤
      SheafOfModules.{u + 1} ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := topology Y) (K := topology X)
    (S := (proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)
    (R := R) (𝟙 _)

/-- K-injective resolutions exist for sheaves of modules over the pro-etale ringed site.
Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: det-pe-bounded-continuity-direct-image).
Proof: transport the site to `proEtaleSiteModel X`, which only enlarges the Hom universe.
There `SheafOfModules.isGrothendieckAbelian` applies to the transported ring sheaf, so
`CochainComplex.kInjectiveResolutionFunctor` gives K-injective quasi-isomorphic
resolutions. Transport back along the inverse sectionwise equivalence, which preserves
acyclicity, homotopies and quasi-isomorphisms. No commutativity, boundedness or
finiteness condition is imposed. -/
theorem ringModuleDirectImage_hasKInjectiveResolutions {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    ∀ L : CochainComplex (SheafOfModules.{u + 1} R) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u + 1} R) ℤ) (s : L ⟶ I),
        I.IsKInjective ∧ QuasiIso s := by
  exact boundedRingModuleDirectImage_hasKInjectiveResolutions R

end AlgebraicGeometry.Scheme.ProEt
