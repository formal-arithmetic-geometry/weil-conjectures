/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityCoordinateMaps
public import WeilConjectures.DeligneLaumon.CurrentPurityConventions.Setting.CurrentPurityConventions
import WeilConjectures.AlgebraicGeometry.FiniteAdmissibleComparison
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.ProjectiveSpaceStandardCharts
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFiniteLines
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Affine-line purity comparison for every finite primary ring

Source: latest blueprint, sec-smooth-purity/sk-prop-an,
def-pur-affine-line-purity-comparison.md, integration and transpose displays;
Wei Yang #1441, item 27 (2026-11-02)
(blueprint: def-pur-affine-line-purity-comparison).

The public source and target use the current internal-module categories. The fixed
scalar formulas below serve only as coordinates through `finiteModelEquivalence`.
The exceptional transpose uses `P.exceptionalData` itself.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GeneralFiniteAffineLinePurity

open AffineLinePurity VectorIntegrationSite

namespace Fixed

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The actual compactification Rp_! = Rq_* j_!, with j the standard affine chart.
Source: integration display (blueprint: def-pur-affine-line-purity-comparison). -/
abbrev support (Y : Scheme.{u}) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (affineTraceLineCompactification Y)

variable (F : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (hl : l ≠ F.p) (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
  (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
  [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

include F hl aY in
variable [hnoeth : IsNoetherian Y]

/-- The shifted ordinary projective Tate line. No restriction of scalars of K is used.
Source: Tate-line paragraph (blueprint: def-pur-affine-line-purity-comparison). -/
abbrev projectiveLine :=
  (Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine Y))⟦(2 : ℤ)⟧

include hnoeth in
/-- The Tate line on the affine chart in its canonical j^* coordinates, including [2].
Source: integration display (blueprint: def-pur-affine-line-purity-comparison). -/
abbrev line :=
  (comparison A (AffineSpace PUnit.{u + 1} Y)).obj
    ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart Y)).obj
      (projectiveLine A l r hA Y))

/-- Integration is Rq_* of the actual open-extension counit followed by the specified trace.
Source: first displayed composite (blueprint: def-pur-affine-line-purity-comparison). -/
def integration (hY : IsUnit (l : Γ(Y, ⊤))) :
    (support A Y).obj (line A l r hA Y) ⟶ unit A Y :=
  restrictTrace A Y (projectiveLine A l r hA Y) (projectiveTrace A l r hA Y hY)

end Fixed

open WeilConjectures.CurrentPurityConventions
open PurityTransport

variable (P : Setting.{u})

/-- The native derived braiding is the signed Koszul braiding of the recorded tensor.
Source: signed symmetry convention (blueprint: def-pur-affine-line-purity-comparison). -/
local instance nativeBraiding (T : Scheme.{u}) : BraidedCategory (P.derived T) :=
  _root_.DerivedCategory.braidedCategory' _

/-- The positive signed line is the original line, through the section equivalence's
inverse unit, without choosing a root basis.
Source: def-pur-conventions, twists (blueprint: def-pur-affine-line-purity-comparison). -/
def signedFirstIso (T : Scheme.{u}) : P.twistLine T 1 ≅ P.firstTwist T :=
  (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology T) (P.coefficientSheaf T)).unitIso.symm.app (P.firstTwist T)

/-- The current Tate coefficient complex, including its shift.
Source: Tate-line paragraph (blueprint: def-pur-affine-line-purity-comparison). -/
abbrev nativeLine (T : Scheme.{u}) : P.derived T :=
  ((DerivedCategory.singleFunctor _ 0).obj (P.twistLine T 1))⟦(2 : ℤ)⟧

variable (A : CommRingCat.{0}) [fin : Finite A] (n : ℕ)
  (hA : (P.coefficients.l ^ (n + 1) : A) = 0)
  (hP : P.coefficient = .finite A fin n hA)

/-- Finite coefficients have their discrete topology.
Source: finite coefficient model (blueprint: def-pur-affine-line-purity-comparison). -/
local instance : TopologicalSpace A := ⊥
/-- The selected coefficient topology is discrete.
Source: finite coefficient model (blueprint: def-pur-affine-line-purity-comparison). -/
local instance : DiscreteTopology A := discreteTopology_bot A

/-- The named model equivalence is the existing exact section-action encoding,
with only the coefficient-presentation equality transported. Its inverse takes fixed
scalar coordinates back to the actual current Lambda_T-module category.
Source: finite coefficient comparison (blueprint: def-pur-affine-line-purity-comparison). -/
def finiteModelEquivalence (T : Scheme.{u}) :
    P.derived T ≌ DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) := by
  cases P with
  | mk F C c =>
    dsimp only at hA hP ⊢
    change c = @Coefficient.finite C.l C.prime A fin n hA at hP
    subst c
    exact (finiteEncodingDerived A T).symm

variable (Y : Over (Spec (.of P.field.k)))
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The affine line as an object over the stipulated base field.
Source: geometry paragraph (blueprint: def-pur-affine-line-purity-comparison). -/
abbrev affineOver : Over (Spec (.of P.field.k)) :=
  Over.mk ((AffineSpace PUnit.{u + 1} Y.left ↘ Y.left) ≫ Y.hom)

/-- The actual affine-line projection in the over category.
Source: geometry paragraph (blueprint: def-pur-affine-line-purity-comparison). -/
def affineMap : affineOver P Y ⟶ Y :=
  Over.homMk (AffineSpace PUnit.{u + 1} Y.left ↘ Y.left)

/-- The literal current-conventions source Lp^*K(1)[2].
Source: M_K display (blueprint: def-pur-affine-line-purity-comparison). -/
abbrev source (K : P.constructibleFiniteTor Y.left) : P.derived (affineOver P Y).left :=
  (P.twist (affineOver P Y).left ((P.pullback (affineMap P Y).left).obj K.obj) 1)⟦(2 : ℤ)⟧

/-- Distribute [2] to the Tate tensor factor using the canonical signed tensor shift.
Source: M_K and Pi_K displays (blueprint: def-pur-affine-line-purity-comparison). -/
def sourceTensorIso (K : P.constructibleFiniteTor Y.left) :
    source P Y K ≅
      (P.pullback (affineMap P Y).left).obj K.obj ⊗ nativeLine P (affineOver P Y).left :=
  (((tensorLeft ((P.pullback (affineMap P Y).left).obj K.obj)).commShiftIso
    (2 : ℤ)).app ((DerivedCategory.singleFunctor _ 0).obj
      (P.twistLine (affineOver P Y).left 1))).symm

include A n hA hP in
include A n hA hP in
/-- The literal twisted pullback belongs to the existing constant-model Dctf category.
Source: M_K paragraph (blueprint: def-pur-affine-line-purity-comparison).
Proof: pullback preserves the finite stratifications and finite Tor tests. The native
Tate line is the root-normalized finite locally free rank-one A-line; tensor with it
and shift by two preserve both properties. The finite model equivalence preserves
and reflects these statements, without restricting K to Z/ell^(n+1). -/
theorem source_mem (K : P.constructibleFiniteTor Y.left) :
    constantModelBoundedConstructible P.ring (affineOver P Y).left (source P Y K) ∧
      _root_.DerivedCategory.finiteTorAmplitude _ (source P Y K) := by
  sorry

end AlgebraicGeometry.ProEtale.GeneralFiniteAffineLinePurity
