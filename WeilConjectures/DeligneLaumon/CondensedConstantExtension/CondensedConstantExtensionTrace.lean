/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.DeligneLaumon.CondensedWeil.ConstantExtensionPunctualWeights
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedConstantExtensionFrobenius
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleSheetSumCompatibility
import WeilConjectures.DeligneLaumon.ConstantExtensionWeilHeartData
import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.DeligneLaumon.CondensedFiniteEtale.CondensedFiniteEtaleStalkCycles
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleSplitHomDescent
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Constant-extension sheets and trace for condensed Weil sheaves

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, paragraph 5
(blueprint: lem-zl-condensed-constant-extension-trace).

The hearts below specialize the recorded fixed-pair and finite constant local model
constructions. The module functors, their compositors, adjunction and coefficient action
are the published condensed ones. In particular the coefficient is the finite-subextension
valued ring, including when the extension degree is divisible by the coefficient prime.

The existing definitions used in the signature have definition-node owners:
`CondensedWeil.extend` is recorded by def-zl-condensed-weil-constant-extension;
`finiteEtaleSheetSum` by def-zl-finite-etale-sheet-sum; and
`FiniteEtaleModuleChart.Compatible` by def-zl-finite-etale-chart-compatibility.
Their published source modules are imported above without duplicating their definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedConstantExtension

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (m : ℕ) (hm : 1 ≤ m) (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]

/-- The actual geometric projection of the constant extension, over the original field.
Source: latest blueprint, paragraph 5
(blueprint: lem-zl-condensed-constant-extension-trace). -/
abbrev projection := NativeCondensedPullback.fiberMap D (NativeCondensedPullback.constantExtensionProjection D m hm T₀)

/-- Pullback with the canonical Frobenius square, on ordinary Weil modules.
Source: latest blueprint, paragraph 5, g^*M
(blueprint: lem-zl-condensed-constant-extension-trace). -/
def pull : CondensedWeil.WeilModule D l T₀ ⥤
    CondensedWeil.WeilModule D l (NativeCondensedPullback.constantExtensionOriginalModel D m hm T₀) :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (CommSq.mk (NativeCondensedPullback.frobenius_naturality D
        (NativeCondensedPullback.constantExtensionProjection D m hm T₀)))).symm

/-- Underived direct image, with the specified base-change exchange followed by g_*theta.
Source: latest blueprint, paragraph 5, exact finite image
(blueprint: lem-zl-condensed-constant-extension-trace). -/
def push : CondensedWeil.WeilModule D l (NativeCondensedPullback.constantExtensionOriginalModel D m hm T₀) ⥤
    CondensedWeil.WeilModule D l T₀ :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (asIso (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
      (CommSq.mk (NativeCondensedPullback.frobenius_naturality D
        (NativeCondensedPullback.constantExtensionProjection D m hm T₀)))))

/-- The sheet-return identity with the positive powers of the local Frobenius trace.
Source: latest blueprint, paragraph 5, cyclic-sheet interpretation
(blueprint: lem-zl-condensed-constant-extension-trace).
Proof: the native and local positive powers have the same recursion; rewrite the
native sheet-return identity along their equality. -/
theorem sheet_return :
    ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFrobenius
        (NativeCondensedPullback.constantExtensionModel D m hm T₀)).hom ≫
        NativeCondensedPullback.constantExtensionSheet D m hm T₀ =
      NativeCondensedPullback.constantExtensionSheet D m hm T₀ ≫
        localPositivePower
          (D.geometricFrobenius (NativeCondensedPullback.constantExtensionOriginalModel D m hm T₀)).hom
          (m - 1) := by
  have hpow (n : ℕ) :
      NativeCondensedModule.localPositivePower
          (D.geometricFrobenius (NativeCondensedPullback.constantExtensionOriginalModel D m hm T₀)).hom n =
        localPositivePower
          (D.geometricFrobenius (NativeCondensedPullback.constantExtensionOriginalModel D m hm T₀)).hom n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change NativeCondensedModule.localPositivePower _ n ≫ _ = localPositivePower _ n ≫ _
      rw [ih]
  have h := NativeCondensedPullback.constantExtensionSheet_return D m hm T₀
  rw [hpow] at h
  exact h

/-- Return to the distinguished sheet: the ordered m-fold Weil iterate, restricted
along the actual sheet inclusion with its canonical pullback-square comparison.
Source: latest blueprint, paragraph 5, cyclic-sheet interpretation
(blueprint: lem-zl-condensed-constant-extension-trace). -/
def returnObj
    (N : CondensedWeil.WeilModule D l (NativeCondensedPullback.constantExtensionOriginalModel D m hm T₀)) :
    CondensedWeil.WeilModule (NativeCondensedPullback.constantExtensionDatum D m hm) l
      (NativeCondensedPullback.constantExtensionModel D m hm T₀) :=
  (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (CommSq.mk (sheet_return D m hm T₀))).symm).obj
    (CategoryTheory.Endofunctor.IsoAlgebra.mk N.carrier
      (CondensedWeil.iterate (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius (NativeCondensedPullback.constantExtensionOriginalModel D m hm T₀)).hom
        N.carrier N.str (m - 1)))

/-- The scalar-fibre identification is the pullback compositor for the geometric point
and the distinguished sheet, followed by actual point sections.
Source: latest blueprint, paragraph 5, preservation of local spectra
(blueprint: lem-zl-condensed-constant-extension-trace). -/
def sheetFibreIso
    (N : CondensedWeil.WeilModule D l (NativeCondensedPullback.constantExtensionOriginalModel D m hm T₀))
    (z : Spec (.of D.k) ⟶
      ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFiber
        (NativeCondensedPullback.constantExtensionModel D m hm T₀)).left) :=
  (CondensedQbarGeometricEvaluation.fieldFiber D.k l).mapIso
    ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l)
      z (NativeCondensedPullback.constantExtensionSheet D m hm T₀)).app N.carrier)

end WeilConjectures.CondensedConstantExtension
