/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerComplex
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFiniteLines
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.CompatibleKummerCoefficients.CompatibleKummerCoefficientData
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Uniqueness of normalized native Kummer realizations

Source: compatible-root construction, Steps 5--6
(blueprint: lem-pur-compatible-kummer-uniqueness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Abelian AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
variable (ell : ℕ) [Fact ell.Prime]

/-- The finite normalization and limit projections determine the integral datum.
Source: compatible-root construction, Step 5
(blueprint: lem-pur-compatible-kummer-uniqueness).
Proof: the prescribed inverse fixes each finite isomorphism. All projections
then fix the inclusion by limit extensionality, and normalization fixes the
projection. Every other field is a proposition. -/
instance compatibleIntegralKummer_subsingleton (T : Scheme.{u}) :
    Subsingleton (CompatibleKummerCoefficients.IntegralKummer ell T) := by
  constructor
  intro K L
  have hlevel : K.level = L.level := by
    funext n
    apply Iso.ext_inv
    exact (K.level_normalized n).trans (L.level_normalized n).symm
  have hincl : K.inclusion = L.inclusion := by
    apply limit.hom_ext
    rintro ⟨n⟩
    have hl : (K.level n).hom = (L.level n).hom :=
      congrArg (fun e : (tateModuleLevel T ell (n + 1)).X ≅
        Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1)) ↦ e.hom) (congrFun hlevel n)
    refine (K.inclusion_normalized n).trans ?_
    refine (congrArg (fun v ↦ (limit.π (tateModuleSystem T ell) (op (n + 1))).hom ≫
      v ≫ Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))) hl).trans ?_
    exact (L.inclusion_normalized n).symm
  have hproj : K.projection = L.projection :=
    K.projection_normalized.trans L.projection_normalized.symm
  cases K
  cases L
  cases hlevel
  cases hincl
  cases hproj
  rfl

end AlgebraicGeometry.ProEtale
