/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteTensorProductFrameExt
public import WeilConjectures.AlgebraicGeometry.FiniteTensorReductionData
public import WeilConjectures.AlgebraicGeometry.FiniteTensorComparisonEquations
public import WeilConjectures.AlgebraicGeometry.FiniteTensorSignedReduction
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.FiniteReductionRootCharts
public import WeilConjectures.AlgebraicGeometry.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientReductionFlatModel
public import WeilConjectures.SecSmoothPurity.SupportedEtaleTensorOrigin
public import WeilConjectures.AlgebraicGeometry.SupportedCup
public import WeilConjectures.AlgebraicGeometry.OrientationFiniteCoefficientTwists
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

import WeilConjectures.AlgebraicGeometry.FiniteTensorProductMap
import WeilConjectures.AlgebraicGeometry.FiniteTensorProductMapIsIso

import all WeilConjectures.AlgebraicGeometry.SupportedCup
import WeilConjectures.SixFunctors.ProEtaleIntrinsicTensorComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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

/-- The type of the prescribed derived signed product, shared before its
normalization and choice are checked. Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def FiniteTensorProductType (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r t : ℤ) :=
  P.finiteTensorFixedLine T r ⊗ P.finiteTensorFixedLine T t ≅
    P.finiteTensorFixedLine T (r + t)

private theorem finiteTensorFixedSheaf_flat (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r : ℤ) :
    ObjectProperty.flat (P.finiteTensorFixedSheaf T r) := by
  let : ∀ x : T, Invertible (P.coefficients.l : T.residueField x) := fun x ↦
    (map_natCast (IsLocalRing.residue (T.presheaf.stalk x)) P.coefficients.l) ▸
      ((P.coefficientPrime_isUnit_stalk T (T ↘ Spec (.of P.field.k)) x).map
        (IsLocalRing.residue (T.presheaf.stalk x))).invertible
  have transport_rank (n m : ℕ) (h : n = m)
      (L : proEtaleRingModules T (proEtaleConstantRing T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension n)))
      (hL : L.IsFiniteLocallyFreeOfRank 1) :
      (Eq.mp (congrArg (fun k : ℕ ↦ proEtaleRingModules T (proEtaleConstantRing T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension k))) h) L
        ).IsFiniteLocallyFreeOfRank 1 := by
    subst m
    exact hL
  have hfirst : (P.finiteTensorFirstLine T).IsFiniteLocallyFreeOfRank 1 := by
    exact transport_rank _ _ (Nat.sub_add_cancel P.level_pos) _
      (coefficientTwistFiniteRank P.coefficients.l P.extension T (P.level - 1))
  let := hfirst
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let e := sfIntrinsicModuleEquivalence T P.Ring
  let N := P.finiteTensorFixedSheaf T r
  let F := SheafOfModules.siteSheafTensorRight (A := proEtaleConstantRing T P.Ring)
    (P.finiteTensorLine T r)
  have : PreservesFiniteLimits F :=
    (coefficientTwistLine_exact T (P.finiteTensorFirstLine T) r).2.1
  let R := proEtaleConstantRing T P.Ring
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let q : SheafOfModules.siteSheafTensorRight (A := R) (e.functor.obj N) ≅ F :=
    SheafOfModules.siteSheafTensorRightIso R (e.functor.obj N) ≪≫
      (curriedTensor _).flip.mapIso (e.counitIso.app (P.finiteTensorLine T r)) ≪≫
      (SheafOfModules.siteSheafTensorRightIso R (P.finiteTensorLine T r)).symm
  have : PreservesFiniteLimits
      (SheafOfModules.siteSheafTensorRight (A := proEtaleConstantRing T P.Ring)
        (e.functor.obj N)) := preservesFiniteLimits_of_natIso q.symm
  obtain ⟨t⟩ := proEtale_intrinsic_tensorRight_comparison T P.Ring N
  have : PreservesFiniteLimits (e.functor ⋙
      SheafOfModules.siteSheafTensorRight (A := proEtaleConstantRing T P.Ring)
        (e.functor.obj N)) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (tensorRight N ⋙ e.functor) :=
    preservesFiniteLimits_of_natIso t
  have : PreservesFiniteLimits (tensorRight N) :=
    preservesFiniteLimits_of_reflects_of_preserves _ e.functor
  exact (ObjectProperty.flat_iff_preservesFiniteLimits N).2
    (preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N).symm)

/-- The native tensor-to-single arrow followed by the normalized sheaf product
specifies exactly one derived product. Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products).
Proof: all signed lines are locally free of rank one, hence flat. Their singles
are K-flat, so the canonical tensor-to-single arrow is invertible. Compose it
with the single of the uniquely normalized ordinary product. The displayed
arrow equation determines the resulting isomorphism uniquely. -/
theorem existsUnique_finiteTensorProducts (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r t : ℤ) :
    ∃! a : P.FiniteTensorProductType T r t,
      FiniteTensorSingleProductNormalized (P.finiteTensorFixedSheaf T r)
        (P.finiteTensorFixedSheaf T t) (P.finiteTensorFixedSheaf T (r + t))
        (P.finiteTensorSheafProducts T r t).hom a.hom := by
  let p := P.finiteTensorSheafProducts T r t
  have hflat := P.finiteTensorFixedSheaf_flat T r
  have := ProEtale.cupSingleTensorMap_isIso
    (P.finiteTensorFixedSheaf T r) (P.finiteTensorFixedSheaf T t) hflat
  let f := finiteTensorSingleProductHom (P.finiteTensorFixedSheaf T r)
    (P.finiteTensorFixedSheaf T t) (P.finiteTensorFixedSheaf T (r + t)) p.hom
  have : IsIso f := by
    dsimp only [f, finiteTensorSingleProductHom]
    infer_instance
  refine ⟨asIso f, HEq.rfl, ?_⟩
  intro a ha
  apply Iso.ext
  exact eq_of_heq ha

/-- Canonical signed addition, fixed by the actual single-complex product arrow.
Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorProduct (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r t : ℤ) : P.FiniteTensorProductType T r t :=
  (P.existsUnique_finiteTensorProducts T r t).exists.choose

end WeilConjectures.PurityFiniteSetting
