/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityCoordinateMaps
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import all WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.ProjectiveSpaceStandardCharts
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
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

private theorem comparisonMate_app_homEquiv
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ H} {R' : H ⥤ E}
    {G : C ⥤ E} {F : D ⥤ H} (a : L ⊣ R) (b : L' ⊣ R')
    (α : G ⋙ L' ⟶ L ⋙ F) (K : D) :
    (mateEquiv a b α).app K = b.homEquiv _ _
      (α.app (R.obj K) ≫ F.map (a.counit.app K)) := by
  simp [mateEquiv_apply, Adjunction.homEquiv_unit]

namespace Fixed

variable (A : Type (u + 1)) [CommRing A] [Finite A]

variable (F : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (hl : l ≠ F.p) (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : A) = 0)
  (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
  [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

set_option linter.unusedSectionVars false in
include F hl aY in
/-- The standing characteristic hypothesis makes ell invertible on every base scheme.
Source: def-pur-conventions (blueprint: def-pur-affine-line-purity-comparison).
Proof: the global datum gives char(k)=p. Since ell and p are distinct primes, ell
is a nonzero element of k, hence a unit. Its image under the structure morphism is
a unit on Y. The same argument applies to the empty scheme and to every chart. -/
theorem primeUnit : IsUnit (l : Γ(Y, ⊤)) := by
  let : Fintype F.k₀ := Fintype.ofFinite _
  let : Fact F.p.Prime := ⟨F.prime⟩
  let : CharP F.k₀ F.p := charP_of_card_eq_prime_pow (f := F.a)
    (by simpa only [Nat.card_eq_fintype_card] using F.card_base.trans F.cardinality_eq)
  let : CharP F.k F.p := charP_of_injective_algebraMap' F.k₀ F.p
  have hunit : IsUnit (l : F.k) :=
    isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime F.k (Fact.out : l.Prime) hl.symm)
  simpa only [map_natCast] using
    hunit.map (((Scheme.ΓSpecIso (.of F.k)).inv ≫ aY.appTop).hom)

variable [hnoeth : IsNoetherian Y]

set_option linter.unusedSectionVars false in
include hnoeth in
/-- The actual canonical direct-image mate is invertible on the projective Tate line.
Source: finite-coefficient direct-image comparison
(blueprint: def-pur-affine-line-purity-comparison).
Proof: the ordinary line is a locally free rank-one A-sheaf in degree -2. The
canonical direct-image comparison of finite comparison applies to q and this input;
its component is precisely geoP1PushComparison, the inverse-image/counit mate. -/
theorem traceComparison_isIso :
    IsIso (geoP1PushComparison A (ProjectiveLine Y ↘ Y)
      (projectiveLine A l r hA Y)) := by
  have hm : geoP1PushComparison A (ProjectiveLine Y ↘ Y) (projectiveLine A l r hA Y) =
      (BoundaryComparison.directImageMate (ModuleCat.{u + 1} A)
        (ProjectiveLine Y ↘ Y)).app (projectiveLine A l r hA Y) := by
    unfold geoP1PushComparison BoundaryComparison.directImageMate
    rw [comparisonMate_app_homEquiv]
    unfold geoP1PullComparison BoundaryComparison.pullbackSquare
      leftDerivedUpperStarIsoMapDerivedCategory Etale.leftDerivedUpperStarIsoMapDerivedCategory
    rfl
  rw [hm, ← sp_comparison_hom A (ProjectiveLine Y ↘ Y) (projectiveLine A l r hA Y)
    (DerivedCategory.TStructure.t.plus.le_shift (2 : ℤ) _ ⟨0, inferInstance⟩)]
  infer_instance

end Fixed

open WeilConjectures.CurrentPurityConventions
open PurityTransport

variable (P : Setting.{u})

/-- The native derived braiding is the signed Koszul braiding of the recorded tensor.
Source: signed symmetry convention (blueprint: def-pur-affine-line-purity-comparison). -/
local instance nativeBraiding (T : Scheme.{u}) : BraidedCategory (P.derived T) :=
  _root_.DerivedCategory.braidedCategory' _

variable (A : CommRingCat.{0}) [fin : Finite A] (n : ℕ)
  (hA : (P.coefficients.l ^ (n + 1) : A) = 0)
  (hP : P.coefficient = .finite A fin n hA)

/-- Finite coefficients have their discrete topology.
Source: finite coefficient model (blueprint: def-pur-affine-line-purity-comparison). -/
local instance : TopologicalSpace A := ⊥
/-- The selected coefficient topology is discrete.
Source: finite coefficient model (blueprint: def-pur-affine-line-purity-comparison). -/
local instance : DiscreteTopology A := discreteTopology_bot A

variable (Y : Over (Spec (.of P.field.k)))
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

include A n hA hP in
include A n hA hP in
/-- The standing characteristic facts needed by the existing canonical compactification
comparison. Source: def-pur-conventions (blueprint: def-pur-affine-line-purity-comparison).
Proof: the finite base has cardinality p^a, a>0, hence characteristic p. Its algebraic
closure has the same characteristic. The coefficient datum gives ell != p. -/
theorem baseCharacteristic :
    (ringChar P.field.k).Prime ∧ ringChar P.field.k ≠ P.coefficients.l := by
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  let : Fact P.field.p.Prime := ⟨P.field.prime⟩
  let : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (f := P.field.a)
    (by simpa only [Nat.card_eq_fintype_card] using
      P.field.card_base.trans P.field.cardinality_eq)
  let : CharP P.field.k P.field.p :=
    charP_of_injective_algebraMap' P.field.k₀ P.field.p
  rw [ringChar.eq P.field.k P.field.p]
  exact ⟨P.field.prime, P.coefficients.different.symm⟩

end AlgebraicGeometry.ProEtale.GeneralFiniteAffineLinePurity
