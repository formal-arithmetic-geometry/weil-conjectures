/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import Sheaf.AlgebraicGeometry.ProperBirationalCurveFinite
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-!
# Birational pullback preserves degree on proper integral curves

Source: Stacks Project, Varieties, Tag 0AYU, lemma-degree-birational-pullback,
rank-one specialization for integral proper curves
(blueprint: lem-per-birational-curve-degree-invariance).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback along a morphism of proper integral curves which is an isomorphism on dense
opens preserves the degree of an invertible module. No smoothness or algebraic-closedness
assumption is imposed. Source: Stacks Project, Varieties, Tag 0AYU
(blueprint: lem-per-birational-curve-degree-invariance).

Proof:
1. Properness over the field makes both schemes Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`). Dense open isomorphisms identify generic
   stalks (`lem-weil-pbc-scheme-sober`). The map is proper by
   `lem-weil-pbc-proper-over-separated`, hence finite by
   `lem-trf-proper-birational-curve-finite`.
2. Put F = f_* O_X'. The structure sheaves and the invertible modules are coherent by
   `pqf-lem-coherent-ft-locnoeth` and `lem-weil-pbc-invertible-pullback-tensor`.
   F and f_* f^* L are coherent by `lem-weil-pbc-finite-pushforward-coherent`.
   The cokernel Q of O_X -> F is coherent by
   `lem-weil-pbc-coherent-modules-kernel-cokernel-sum`.
3. On an affine open Spec A, its inverse image is Spec B with B finite over A
   (`def-weil-finite-integral-morphism`). The two rings embed compatibly into their
   common function field (`lem-sc-integral-function-field-affine-fraction`). Thus
   A -> B is injective and becomes an isomorphism at the generic point. We obtain
   the exact sequence 0 -> O_X -> F -> Q -> 0, with zero generic stalk for Q.
4. The support of Q is closed (`lem-weil-pbc-scheme-theoretic-support`) and misses the
   generic point. A chain in it, extended by X, shows its dimension is at most zero
   (`def-kun-topological-krull-dimension`). Thus `lem-pc-chi-zero-dim-support` gives
   chi(Q tensor L) = chi(Q).
5. The map L tensor F -> f_* f^* L sends s tensor b to (f^*s)b. On a trivializing
   open for L it is the identity on F, so it is an isomorphism; the descriptions
   agree on overlaps by the tensor pullback and sheaf tensor definitions
   (`def-pc-module-pullback`, `def-pur-sheaf-tensor-product`).
6. Tensoring the sequence in step 3 with L stays exact: on each trivializing open
   tensoring is the identity. Its terms are coherent by steps 2, 4 and 5.
7. Since f is finite and hence affine, `lem-weil-pbc-affine-morphism-cohomology-edge`
   identifies cohomology of F and f_* f^* L with that of O_X' and f^* L, respectively.
   These maps are k-linear because f is over k. Proper coherent cohomology is finite
   and eventually zero (`lem-pc-coherent-hi`), so the Euler characteristics agree
   (`def-pc-euler-characteristic`).
8. Euler additivity (`lem-pc-euler-additive`) on the sequences in steps 3 and 6,
   the equality from step 4, and tensor symmetry give
   chi(X', f^*L) - chi(X', O_X') = chi(X, L) - chi(X, O_X).
9. Both differences are the degree of `def-pc-degree-line-bundle`. -/
theorem degree_tensorPullback_of_birational_curve
    (k : Type u) [Field k] {X X' : Scheme.{u}}
    [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]
    [IsIntegral X] [IsIntegral X']
    [IsProper (X ↘ Spec (.of k))] [IsProper (X' ↘ Spec (.of k))]
    (hdimX : topologicalKrullDim X = 1) (hdimX' : topologicalKrullDim X' = 1)
    (f : X' ⟶ X) [f.IsOver (Spec (.of k))]
    (hbirational : ∃ (U' : X'.Opens) (U : X.Opens) (e : U'.toScheme ≅ U.toScheme),
      Dense (U' : Set X') ∧ Dense (U : Set X) ∧ U'.ι ≫ f = e.hom ≫ U.ι)
    (L : X.Modules) [L.IsInvertible] :
    ((tensorPullback f).obj L).degree k = L.degree k := by
  sorry

end AlgebraicGeometry.Scheme.Modules
