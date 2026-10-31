/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.FieldTheory.FieldTower
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.AlgebraicGeometry.CurveDegreeTensorAdditive
import WeilConjectures.AlgebraicGeometry.CurveSectionDegreePositivity
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Numerical Riemann--Hurwitz for a separable map of proper curves

Source: Stacks Project, Algebraic Curves, Tags 0C1B and 0C1C; Varieties, Tag 0A26.
(blueprint: lem-sfb-curve-riemann-hurwitz-numerical)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Numerical Riemann--Hurwitz retains the full effective different, including wild
ramification. The algebra on the function fields is the one induced by `f`: its spectrum
commutes with the canonical generic-point morphisms. Genus is the existing `Hom.genus`,
identified with `dim H¹(O)` by `Scheme.genus_eq_arithmeticGenus` for these curves.

Source: Stacks Project, Algebraic Curves, Tags 0C1B and 0C1C; Varieties, Tag 0A26.
(blueprint: lem-sfb-curve-riemann-hurwitz-numerical)

Proof:
1. The induced function-field extension makes `f` dominant. Its finite dimension `d` is
   positive, since the singleton consisting of one is linearly independent over the base field.
2. Set `B = Ω_X/k` and `A = f* Ω_Y/k`. The relative differential sheaf agrees with the
   affine-local Kahler differential sheaf (def-sc-relative-differential-sheaf and
   def-sc-kahler-differentials). Both are invertible by lem-sc-canonical-sheaf and
   lem-weil-pbc-invertible-pullback-tensor. Finite separability makes `df : A → B` nonzero
   by lem-sfb-separable-curve-differential-nonzero.
3. The local expressions of `df` glue to a nonzero section of `L = B ⊗ A.dual`:
   changing generators by units `u,v` multiplies the coefficient by `u/v` and the tensor
   generator by `v/u`. The dual and tensor are invertible (def-sc-invertible-module,
   def-pur-sheaf-tensor-product). Set `r = deg L`; lem-trf-curve-section-degree-positivity
   gives `r ≥ 0` on the proper integral curve `X`.
4. All degrees are Euler-characteristic degrees (def-pc-degree-line-bundle).
   Riemann--Roch (lem-sc-riemann-roch) identifies these with Picard degrees by subtracting
   the formula for `O` from that for a line bundle. By lem-sc-canonical-degree and
   def-sc-pic0 the canonical differential bundles have degree `2g - 2` on `X` and `Y`.
5. Evaluation identifies `A ⊗ A.dual` with `O`. Tensor additivity
   (lem-trf-curve-degree-tensor-additive) and degree zero of `O` imply
   `deg A.dual = -deg A`, hence `r = deg B - deg A`. Isomorphisms preserve degree because
   they preserve the dimensions defining Euler characteristic.
6. Apply lem-sfb-proper-curve-bundle-pullback-degree to the invertible `Ω_Y/k`:
   `deg A = d * deg Ω_Y/k`. Substitution gives the displayed equality, with `d > 0`
   from step 1 and `r ≥ 0` from step 3. No tameness or characteristic restriction is used.
-/
theorem curve_riemannHurwitz_numerical
    (k : Type u) [Field k] [IsAlgClosed k]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsIntegral X] [IsIntegral Y]
    [IsCurve (X ↘ Spec (.of k))] [IsCurve (Y ↘ Spec (.of k))]
    [Smooth (X ↘ Spec (.of k))] [Smooth (Y ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))]
    [GeometricallyIntegral (Y ↘ Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (hY : topologicalKrullDim Y = 1)
    (f : X ⟶ Y) (hf : f ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k))
    (hnonconstant : ¬ ∃ p : Spec (.of k) ⟶ Y,
      p ≫ (Y ↘ Spec (.of k)) = 𝟙 (Spec (.of k)) ∧ (X ↘ Spec (.of k)) ≫ p = f)
    [Algebra Y.functionField X.functionField]
    (hfield : Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
      Y.fromSpecFunctionField = X.fromSpecFunctionField ≫ f)
    [Module.Finite Y.functionField X.functionField]
    [Algebra.IsSeparable Y.functionField X.functionField] :
    0 < Module.finrank Y.functionField X.functionField ∧
      ∃ r : ℤ, 0 ≤ r ∧
        2 * ((X ↘ Spec (.of k)).genus : ℤ) - 2 =
          (Module.finrank Y.functionField X.functionField : ℤ) *
            (2 * ((Y ↘ Spec (.of k)).genus : ℤ) - 2) + r := by
  sorry

end AlgebraicGeometry
