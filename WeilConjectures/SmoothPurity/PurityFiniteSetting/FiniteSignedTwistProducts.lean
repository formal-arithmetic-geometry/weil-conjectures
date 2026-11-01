/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorProductFrameExt
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorComparisonEquations
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSignedReduction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientReductionFlatModel
public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SixFunctors.Orientation.OrientationFiniteCoefficientTwists
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorProductMap
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorProductMapIsIso

import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicTensorComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Finite reduction of signed twists and tensor presentations

Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2;
Stacks Tags 07A4, 0FPT, 0FNH, 03EK and 03EM.
(blueprint: def-pur-finite-signed-twist-products)

## Main declarations

- `finiteTensorSheafProducts`
- `finiteTensorProduct`
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting

/-- The local generator prescription determines every ordinary signed addition map,
including cancellation of opposite signs.
Source: blueprint proof Step 5; Stacks 03EK, 04TT and 03EM
(blueprint: def-pur-finite-signed-twist-products).
Proof: in each trivialization send the product of the r and t basis powers to
the r+t basis power. Changes of basis multiply both sides by the same power of
the transition unit. Hence these maps glue and are unique. Dual evaluation gives
the opposite-sign cases, and unitors give the zero cases. -/
theorem existsUnique_finiteTensorSheafProducts (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] :
    ∃! p : ∀ r t : ℤ, P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ≅
        P.finiteTensorFixedSheaf T (r + t),
      (∀ (r t : ℤ) (V : T.ProEt) (e : P.FiniteTensorFrame T V)
        (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
        (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)),
        P.finiteTensorSection T r V x = e.basis r 0 →
        P.finiteTensorSection T t V y = e.basis t 0 →
        P.finiteTensorSection T (r + t) V
          ((p r t).hom.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) =
            e.basis (r + t) 0) := by
  classical
  choose f hf using fun r t : ℤ ↦ P.exists_finiteTensorSheafProductMap T r t
  let (r t : ℤ) : IsIso (f r t) :=
    P.finiteTensorSheafProductMap_isIso T r t (f r t) (hf r t)
  refine ⟨fun r t ↦ asIso (f r t), ?_, ?_⟩
  · intro r t V e x y hx hy
    exact hf r t V e x y hx hy
  · intro p hp
    funext r t
    apply Iso.ext
    apply P.finiteTensorSheafProduct_frame_ext T r t (r + t)
    intro V e x y hx hy
    exact (hp r t V e x y hx hy).trans (hf r t V e x y hx hy).symm

/-- The unique ordinary signed product, with its local basis normalization retained.
Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorSheafProducts (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] :=
  (P.existsUnique_finiteTensorSheafProducts T).exists.choose

end WeilConjectures.PurityFiniteSetting
