/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.ProjectiveBundleFormula
public import WeilConjectures.AlgebraicGeometry.KummerAdditivity
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # Etale origin of all positive-degree Chern coordinates

Source: Stacks Tags 03PK and 099V; finite-coefficient etale/pro-etale comparison.
(blueprint: lem-pur-chern-etale-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.Etale
attribute [local irreducible] derivedTensor

/-- Every positive shifted Tate power has a lower cohomological bound, with
no projective-bundle rank bound on its exponent.
Source: Stacks Tag 03PK, finite Tate lines and their tensor powers.
Proof: normal form identifies the recorded ordered power with the degree-zero
finite Tate sheaf shifted by 2d. It is concentrated in degree -2d; transport the
standard lower bound across that isomorphism. This includes d=0 and an empty base.
(blueprint: lem-pur-chern-etale-origin). -/
theorem ordinaryFinitePositiveTwistEtale_isPlus (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) (d : ℕ) :
    _root_.DerivedCategory.TStructure.t.plus (P.diagonalTwistEtale T d) := by
  obtain ⟨q⟩ := base_normal_form P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates T (P.diagonalExponent_isUnit a) d
  let L := (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent T
      P.diagonalExponent_annihilates (d : ℤ))
  have hge : _root_.DerivedCategory.TStructure.t.IsGE
      (L⟦2 * (d : ℤ)⟧) (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isGE_shift L 0 (2 * (d : ℤ))
      (-(2 * (d : ℤ))) (by omega)
  exact ⟨-(2 * (d : ℤ)),
    _root_.DerivedCategory.TStructure.t.isGE_of_iso q.symm (-(2 * (d : ℤ)))⟩

/-- Exact etale/pro-etale comparison gives every ordinary Chern coordinate and
reflects its equality, for the actual positive Tate-power objects in every degree.
Source: Stacks finite-coefficient site comparison, Tag 099V.
Proof: the target is bounded below by the preceding theorem. The existing
finite-coefficient comparison Hom bijection applies with the recorded unit as
source and that target; its map is exactly the published exact comparison.
(blueprint: lem-pur-chern-etale-origin). -/
theorem ordinaryFiniteCohomologyComparison_bijective (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) (d : ℕ) :
    Function.Bijective
      (fun α : Etale.ordinaryFiniteUnit P.Coefficient T ⟶ P.diagonalTwistEtale T d ↦
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map α) := by
  exact ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
    (Etale.ordinaryFiniteUnit P.Coefficient T) (P.diagonalTwistEtale T d)
    (P.ordinaryFinitePositiveTwistEtale_isPlus a d)

end WeilConjectures.PurityFiniteSetting
