/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Sheaf.AlgebraicGeometry.SchemeTheoreticUnion
import Sheaf.AlgebraicGeometry.EtaleOpenChartMorphismDescent
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Closed unions as pushouts of algebraic spaces

Source: Stacks Project, Pushouts of Algebraic Spaces, Tags 0GFQ and 0EDP;
Morphisms of Schemes, Tag 0C4J
(blueprint: lem-sfb-closed-space-union-pushout).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- If the defining ideals of two closed subspaces have zero intersection, the ambient
algebraic space is their pushout along their fibre product. The defining ideals are the
kernels of the structure maps, as in `closed_ideal_correspondence`; their zero intersection
is expressed on sections of every etale chart. The fibre product is specified by its
universal property, allowing any presentation of the same sheaf product.
There are no Noetherian, separation or quasi-compactness assumptions.
Source: Stacks Project, Tags 0GFQ, 0EDP and 0C4J
(blueprint: lem-sfb-closed-space-union-pushout).

Proof:
1. Choose a representable surjective etale scheme atlas U of X using
   def-trf-algebraic-space. On every etale scheme chart V of X, the two closed subspaces
   and their fibre product become closed subschemes A_V, B_V and E_V, by
   def-sfb-space-closed-subspace and lem-trf-space-fibre-products-etale-covers.
   By lem-sfb-space-closed-ideal-correspondence their ideals are the restrictions of the
   two kernel ideals. Etale restriction evaluates both on the same objects, so their
   intersection is still zero; no claim about arbitrary base change is needed.
2. By lem-weil-pbc-scheme-theoretic-union their scheme-theoretic union is defined by the
   zero ideal, hence is V: on each affine open this is Spec(R/0) mapping to Spec(R).
   Lemma lem-trf-closed-union-pushout makes V the scheme pushout along E_V.
3. Apply lem-sfb-ferrand-pushout-space-agreement. Both maps out of E_V are closed
   immersions. One is integral by lem-weil-pbc-closed-immersion-integral-separated-uc.
   Each fibre of that map has at most one point, whose image in the other branch has
   an affine neighbourhood by lem-weil-pbc-affine-opens-basis. For an empty fibre use
   the empty affine open. Thus V is also the pushout against algebraic-space targets.
4. Given compatible maps A to H and B to H, step 3 gives a unique map U to H. The
   overlap R = U times_X U is a scheme and is etale over X by
   lem-trf-space-fibre-products-etale-covers and
   lem-weil-pbc-etale-composition-cancellation. The two induced maps R to H agree by
   step 3 applied to R. Use lem-trf-etale-open-chart-morphism-descent with the full
   invariant open U to descend the map to X.
5. The induced atlases A_U to A and B_U to B are surjective etale by
   lem-trf-space-fibre-products-etale-covers. Equality detection in
   lem-trf-etale-open-chart-morphism-descent shows the descended map restricts to the
   prescribed maps. Any second extension equals it after pullback to U by step 3,
   hence equals it globally by the same equality detection. This is exactly the
   colimit universal property of def-weil-pbc-category-colimit. -/
theorem closed_union_isPushout {S : Scheme.{u}} (X : AlgebraicSpace S)
    (A B : ClosedSubspace X)
    (hIJ : ∀ (V : X.EtaleSite) (s : X.structureSheaf.obj.obj (op V)),
      (moduleStructureMap A.val.arrow).val.app (op V) s = 0 →
      (moduleStructureMap B.val.arrow).val.app (op V) s = 0 → s = 0)
    (E : AlgebraicSpace S) (a : E ⟶ (A.val : AlgebraicSpace S))
    (b : E ⟶ (B.val : AlgebraicSpace S))
    (hE : IsPullback a b A.val.arrow B.val.arrow) :
    IsPushout a b A.val.arrow B.val.arrow := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
