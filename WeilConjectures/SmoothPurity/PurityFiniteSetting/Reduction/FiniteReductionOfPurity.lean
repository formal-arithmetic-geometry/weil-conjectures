/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionAffineOrientation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescent
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionReassociation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorPurity
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalOrientationReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCoherence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionBaseChangeSource
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityNaturality

/-! # Reduction of the canonical finite-coefficient purity maps

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
thm-pur-finite-reduction-of-purity (blueprint: thm-pur-finite-reduction-of-purity).

## Main statements

- `finiteReductionOfPurity`: reduction of the canonical purity morphism.
- `finiteReductionOfSmoothTrace`: reduction of coefficient-valued smooth traces.
- `finiteReductionOfCompositionCoherence`: reduction of the full purity composite.
- `finiteReductionOfBaseChange`: reduction of the specified smooth exchange square.
- `finiteReductionOfAffineOrientation`: reduction of the supported-Kummer orientation.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Finite reduction takes the specified purity morphism to the specified purity
morphism over the smaller quotient, through the canonical six-operation comparisons.
There is no ramification-index divisibility or quotient-flatness hypothesis.
Source: blueprint thm-pur-finite-reduction-of-purity, displayed square
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: use bounded flat representatives to obtain the tensor, pullback, support,
shift and rank-one twist comparisons. The supported Cartier class reduces because
the finite Kummer sequences commute and the supported boundary is natural; its
adjoint gives the affine orientation at the smaller level. The deformation
localization triangles and their specialization maps commute with reduction, as
do zero-section duality and vector-bundle trace, so normalized diagonal orientation
reduces. The tensor transformation is the counit mate of the projection-formula
inverse; finite adjoint-mate compatibility makes it commute with reduction.
Substitute these identities into tau, tensor with the inverse diagonal orientation,
and theta defining gamma. This gives precisely the displayed equality. -/
theorem finiteReductionOfPurity (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (P.finiteReduction m hm hmn X).map (P.smoothPurityMap f d K hK) ≫
        P.finiteReductionExceptionalComparison m hm hmn f d K hK =
      (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).smoothPurityMap f d
          ((P.finiteReduction m hm hmn Y).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Y K hK) := by
  unfold smoothPurityMap
  rw [Functor.map_comp, Category.assoc,
    P.finiteReduction_tensorPurity m hm hmn f d K hK, ← Category.assoc,
    P.finiteReduction_reassociation m hm hmn f d K hK, Category.assoc]

set_option linter.unusedSectionVars false in
/-- Transport the intrinsic finite-Tor predicate along an actual isomorphism.
Source: the definitions of constructibility and Tor amplitude. -/
private theorem finiteTor_of_iso
    {T : Scheme.{u}} {K L : Scheme.proEtaleDerivedCategory T P.Ring}
    (e : K ≅ L)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T L := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (Scheme.intrinsicFiniteTorsionConstructible
        P.coefficients.l P.extension P.level P.level_pos T) :=
    (Scheme.proEtale_bounded_constructible_isTriangulated T P.Ring).1
  refine ⟨ObjectProperty.prop_of_iso _ e hK.1, ?_⟩
  obtain ⟨a, b, ht⟩ := hK.2
  refine ⟨a, b, ht.1, ?_⟩
  intro M N hM g hg hN V i hi
  exact ht.2 M N (hM.map (fun j ↦ j ≪≫ e.symm)) g hg hN V i hi

attribute [-instance] WeilConjectures.finiteHomEtaleCategory in
set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
end Morphism
section Composition
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y Z : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [Z.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Z ↘ Spec (.of P.field.k))]
variable [IsSeparated (Z ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
variable (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]

set_option linter.unusedSectionVars false in
end Composition
section BaseChange
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X X' Y Y' : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
variable [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X' ↘ Spec (.of P.field.k))]
variable [IsSeparated (X' ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y' ↘ Spec (.of P.field.k))]
variable (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
variable [u.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
variable [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
variable (sq : IsPullback u f' f v) (d : ℕ)
variable [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']

set_option linter.unusedSectionVars false in
end BaseChange

end WeilConjectures.PurityFiniteSetting
