/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerGlobalChart
public import Sheaf.Paper.KummerScalarInvariantSquare
public import Sheaf.Paper.KummerChartGeometryMaps
public import Sheaf.Paper.KummerRefinement

/-! # Simultaneous normalized coefficient comparisons on a root chart
Source: direct-image proof (3), whole stratum with both coefficient fields.
(blueprint: def-sfb-kummer-stratum-chart).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale
open CategoryTheory.CondensedBar

/-- The exact full tame inertia product indexed by the branches on this stratum.
Source: direct-image proof (3), G_I
(blueprint: def-sfb-kummer-stratum-chart). -/
abbrev kummerChartGroup (p : ℕ) {A : Type u} (I : Finset A) : Profinite.{u} :=
  Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I})

variable (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {Y : Scheme.{u}} {A : Type u} [Finite A]
  (D : Y.IdealSheafData) (C : A → Y.IdealSheafData) (I : Finset A)
  (L : KummerModules (Profinite.continuousMapRingObj E.1) (tameBoundaryOpen D).toScheme)
  (c : TameRootExtensionChart C I)
  [ActionAbelian (kummerCoefficientRing.{u} E.1) (kummerChartGroup p I)]
  [ActionAbelian (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) (kummerChartGroup p I)]
  [IsGrothendieckAbelian.{u + 1}
    (Equivariant (kummerCoefficientRing.{u} E.1) (kummerChartGroup p I))]
  [IsGrothendieckAbelian.{u + 1}
    (Equivariant (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) (kummerChartGroup p I))]
  [HasDerivedCategory.{u + 2}
    (Equivariant (kummerCoefficientRing.{u} E.1) (kummerChartGroup p I))]
  [HasDerivedCategory.{u + 2}
    (Equivariant (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) (kummerChartGroup p I))]
  [HasDerivedCategory.{u + 2} (Modules (kummerCoefficientRing.{u} E.1))]
  [HasDerivedCategory.{u + 2} (Modules (kummerCoefficientRing.{u} (PadicAlgCl ℓ)))]

/-- Both coefficient comparisons use one actual full-root geometry and one continuous
finite representation. Their maps are fixed by the normalized nerve, invariant and scalar
resolution equations, and restrict by the actual Cartesian comparisons.
Source: direct-image proof (3), common E and Omega model
(blueprint: def-sfb-kummer-stratum-chart). -/
structure KummerStratumChart
    (BE : Model (kummerCoefficientRing.{u} E.1) (kummerChartGroup p I))
    (BO : Model (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) (kummerChartGroup p I))
    (b : ScalarModel (kummerCoefficientMap ℓ E) BE BO)
    (geometry : TameRootChartGeometry p D c) where
  boundary : c.boundary ⟶ c.tower p
  boundary_over : boundary ≫ c.towerMap p = c.boundaryToBase
  roots_zero : ∀ (n : TameRootOrder p) (i : {a : A // a ∈ I}),
    boundary.appTop (fullParameterRootSection p c.parameters n i) = 0
  representation : PartialKummer.FiniteRepresentation E.1 (kummerChartGroup p I)
  primeToEll : KummerFinitePrimeToEllImage p ℓ {a : A // a ∈ I} E.1 representation
  coefficients : KummerCoefficientModels ℓ E (kummerChartGroup p I) representation b.restriction
  comparisonE : KummerGlobalChart (kummerCoefficientRing.{u} E.1) (kummerChartGroup p I) BE
    (tameBoundaryOpen D).ι c.toBase c.boundaryToBase geometry.openAction
    (c.toPuncturedBase p D) geometry.overQuotient (c.openInclusion p D) (c.towerMap p)
    (kummerChartOpen_commutes p D c) boundary boundary_over L coefficients.finite.object
  comparisonOmega : KummerGlobalChart (kummerCoefficientRing.{u} (PadicAlgCl ℓ))
    (kummerChartGroup p I) BO (tameBoundaryOpen D).ι c.toBase c.boundaryToBase geometry.openAction
    (c.toPuncturedBase p D) geometry.overQuotient (c.openInclusion p D) (c.towerMap p)
    (kummerChartOpen_commutes p D c) boundary boundary_over
    (kummerOmegaModuleForRing ℓ E (tameBoundaryOpen D).toScheme L) coefficients.closureForRing
  scalar : KummerInvariantScalarArrow (kummerCoefficientRing.{u} E.1)
    (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) (kummerCoefficientMap ℓ E)
    (kummerChartGroup p I) BE BO b c.boundary
    coefficients.finite.object coefficients.closureForRing coefficients.unit
    comparisonE.normalized.descent.actionResolution
    comparisonOmega.normalized.descent.actionResolution
  scalar_square : KummerCoefficientSquare ℓ E (tameBoundaryOpen D).ι
    (c.boundaryToBase ≫ c.toBase) L
    (kummerInvariantObject (kummerCoefficientRing.{u} E.1) (kummerChartGroup p I) BE c.boundary
      coefficients.finite.object)
    (kummerInvariantObject (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) (kummerChartGroup p I)
      BO c.boundary coefficients.closureForRing)
    comparisonE.comparison comparisonOmega.comparison scalar.arrow
  refinementE : KummerRefinementNatural (kummerCoefficientRing.{u} E.1)
    (kummerChartGroup p I) BE (tameBoundaryOpen D).ι c.toBase c.boundaryToBase
    geometry.openAction (c.toPuncturedBase p D) geometry.overQuotient
    (c.openInclusion p D) (c.towerMap p) (kummerChartOpen_commutes p D c)
    boundary boundary_over L coefficients.finite.object comparisonE
  refinementOmega : KummerRefinementNatural (kummerCoefficientRing.{u} (PadicAlgCl ℓ))
    (kummerChartGroup p I) BO (tameBoundaryOpen D).ι c.toBase c.boundaryToBase
    geometry.openAction (c.toPuncturedBase p D) geometry.overQuotient
    (c.openInclusion p D) (c.towerMap p) (kummerChartOpen_commutes p D c)
    boundary boundary_over (kummerOmegaModuleForRing ℓ E (tameBoundaryOpen D).toScheme L)
    coefficients.closureForRing comparisonOmega
  empty_tower : I = ∅ → IsIso (c.towerMap p)
  empty_open : I = ∅ → ∃ w : c.boundary ⟶ (tameBoundaryOpen D).toScheme,
    w ≫ (tameBoundaryOpen D).ι = c.boundaryToBase ≫ c.toBase ∧
      Nonempty ((upperStar (Profinite.continuousMapRingObj E.1) w).obj L ≅
        ((upperStarFromPoint c.boundary).mapMod (Profinite.continuousMapRingObj E.1)).obj
          coefficients.finite.object.module)

end AlgebraicGeometry.ProEtale.CondensedRing
