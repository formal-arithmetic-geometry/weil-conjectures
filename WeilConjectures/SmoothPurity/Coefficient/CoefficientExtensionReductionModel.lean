/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRRoosFiniteReduction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.ZMod.Basic
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictRepresentatives
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRepresentativeRoos
/-! # Coherent finite reduction of completed coefficient extension

Source: main-20261015 blueprint, sec-proetale-coefficients/sk-def-sf-operations,
def-weil-derived-pullback-tensor-hom, integral operations; Stacks 06YS, 0G7E, 06YY.
(blueprint: lem-pur-coefficient-extension-reduction-model).
Positive exponent m is encoded by n=m-1. All derived categories are unbounded,
and the small pro-etale site's object and morphism universes remain independent.

## Main definitions

- `CoefficientExtensionReductionData`: simultaneous models and their canonical counit.
- `coefficientExtensionReductionIso`: that counit as a coherent-system isomorphism.

## Main statements

- `coefficientExtensionReductionModel`: existence on the entire unbounded derived category.
- `coefficientExtensionReduction_identity`: normalization for identity coefficients.
- `coefficientExtensionReduction_composition`: compatibility for three coefficient fields.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
section ScalarAssociation
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  {R S T : Sheaf J CommRingCat.{max c v r}} {f : R ⟶ S} {g : S ⟶ T} {h : R ⟶ T}
  (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
  (B : SemilinearSections.ScalarData.{c, v, max c v r} g)
  (D : SemilinearSections.ScalarData.{c, v, max c v r} h)

end ScalarAssociation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

variable (SE : CoefficientDerivedSystemCalculus l E W)
  (SL : CoefficientDerivedSystemCalculus l L W)
  (A : CoefficientExtensionSystems l E L ι W)

section SuccessiveExtension
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (j : L →ₐ[ℚ_[l]] F) (SF : CoefficientDerivedSystemCalculus l F W)
  (B : CoefficientExtensionSystems l L F j W)
  (D : CoefficientExtensionSystems l E F (j.comp ι) W)
  (dEL : CoefficientExtensionReductionData l E L ι W SE SL A)
  (dLF : CoefficientExtensionReductionData l L F j W SL SF B)
  (dEF : CoefficientExtensionReductionData l E F (j.comp ι) W SE SF D)

end SuccessiveExtension

end WeilConjectures
