/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.FieldTheory.FieldTower
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.DominantIntegralCurveQuasiFinite
import WeilConjectures.AlgebraicGeometry.CurveEulerTensorGenericRank
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
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge

/-! # Degree of an invertible sheaf pulled back between proper curves

Source: Stacks Project, Varieties, Tag 0AYZ, `lemma-degree-pullback-map-proper-curves`,
the rank-one case; Morphisms, `definition-degree`.
(blueprint: lem-sfb-proper-curve-bundle-pullback-degree)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback by a dominant morphism of proper integral curves multiplies the degree of
an invertible module by the degree of the induced finite extension of function fields.
The field map is the actual generic stalk map `f.functionFieldMap`; its algebra structure
is passed explicitly to `Module.finrank`. Both degrees are the existing differences of
Euler characteristics, and the pullback is the explicit tensor pullback.

Source: Stacks Project, Varieties, Tag 0AYZ, `lemma-degree-pullback-map-proper-curves`,
rank one; Morphisms, `definition-degree`.
(blueprint: lem-sfb-proper-curve-bundle-pullback-degree)

Proof:
1. By lem-weil-pbc-proper-over-separated, f is proper, since X is proper and Y is
   separated over k. The integral finite-type dimension-one hypotheses are those of
   def-pc-curve. Dominance and the finite function-field extension allow
   lem-trf-birational-curve-quasifinite; then pqf-lem-proper-lqf-finite makes f finite,
   hence affine by def-weil-finite-integral-morphism.
2. A field is Noetherian. By lem-weil-pbc-finite-type-over-noetherian, X and Y are
   Noetherian. By lem-weil-pbc-invertible-pullback-tensor, f* M is invertible.
   Invertible modules and structure modules are quasi-coherent and locally generated
   by one element (def-sc-invertible-module), so pqf-lem-coherent-ft-locnoeth makes
   M, f* M, and O_X coherent. Their coherent Euler characteristics are defined.
3. Put F = f_* O_X. By lem-weil-pbc-finite-pushforward-coherent, F is coherent.
   By lem-sfb-finite-dominant-generic-pushforward-stalk, its generic stalk is k(X)
   as a k(Y)-algebra for the actual generic stalk map of f. Thus its generic rank
   is d = dim_{k(Y)} k(X), the finite field degree of def-pc-field-tower.
4. The canonical projection map M tensor F -> f_* f* M sends m tensor a to a f* m
   (def-pc-module-pullback, def-pur-sheaf-tensor-product). On an open with a basis e
   of M (def-sc-invertible-module), it sends e tensor a to a f* e and is the identity
   after trivializing both sides. Replacing e by a unit multiple changes both sides
   by the same pulled-back unit. Hence these local inverses agree and glue.
5. By lem-weil-pbc-finite-pushforward-coherent, f_* f* M is coherent. The affine
   cohomology edge comparison lem-weil-pbc-affine-morphism-cohomology-edge applies
   to f* M and O_X. Its maps are linear over global sections on Y, hence k-linear
   because f is over k. Taking alternating dimensions (def-pc-euler-characteristic)
   and using step 4 gives chi(X,f* M) = chi(Y,M tensor F) and chi(X,O_X) = chi(Y,F).
6. Apply lem-trf-curve-euler-tensor-generic-rank on Y to the invertible M and the
   coherent F of generic rank d: chi(Y,M tensor F) = d degree(M) + chi(Y,F).
   With step 5 this gives chi(X,f* M) = d degree(M) + chi(X,O_X).
7. Subtract chi(X,O_X); def-pc-degree-line-bundle identifies the left side with
   degree(f* M), giving the asserted equality. No smoothness, flatness, separability,
   or algebraic closure of k is assumed.
-/
theorem proper_curve_bundle_pullback_degree
    (k : Type u) [Field k]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsIntegralCurve (X ↘ Spec (.of k))] [IsIntegralCurve (Y ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f]
    (hfinite : (f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.Finite)
    (M : Y.Modules) [M.IsInvertible] :
    ((tensorPullback f).obj M).degree k =
      (@Module.finrank Y.functionField X.functionField _ _
        (f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.toAlgebra.toModule : ℤ) *
          M.degree k := by
  sorry

end AlgebraicGeometry.Scheme.Modules
