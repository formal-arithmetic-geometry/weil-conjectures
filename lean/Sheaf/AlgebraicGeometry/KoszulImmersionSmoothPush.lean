/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import Sheaf.RingTheory.KoszulSplitConormalCancellation
import WeilConjectures.RingTheory.KoszulRegularFlatBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.SmoothPairRegularEquations

/-!
# Pushing Koszul regularity through a smooth ambient morphism

Source: Stacks Project, Divisors, Tag 0693
(blueprint: lem-sfb-koszul-immersion-smooth-push).

Koszul regularity is expressed at every source point using the existing local predicate.
Its finite equations may have different lengths on different neighbourhoods.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- In a commuting triangle of immersions with smooth ambient projection, Koszul regularity
of the immersion into the ambient scheme implies Koszul regularity into the base.
Source: Stacks Project, Divisors, Tag 0693, Koszul-regular case
(blueprint: lem-sfb-koszul-immersion-smooth-push).

Proof:
1. First take the ambient scheme to be affine space over the base. At a source point,
shrink the base so the base immersion is closed and the base is Spec A. Write its ideal
as I, the polynomial ring as B = A[x_1,...,x_n], and lift the images of the coordinates
to a_l in A. The ambient immersion is the surjection B -> A/I with kernel
J = (x_1-a_1,...,x_n-a_n) + IB (def-weil-closed-immersion, def-sbc-affine-space).
2. Put t_l = x_l-a_l and K = (t_1,...,t_n). Translation makes B a polynomial ring in t.
Each t_l acts injectively modulo its predecessors, hence this sequence is Koszul-regular
by lem-weil-pbc-regular-sequence-koszul-regular. Linear coefficients identify K/KJ
with (A/I)^n and give a B/J-linear retraction J/J^2 -> K/KJ: products of elements
of J have zero linear coefficients modulo I. Thus the conormal sequence is split exact.
3. The affine criterion lem-sfb-koszul-closed-immersion-affine-criterion supplies local
Koszul-regular generators of J. Localization preserves the Koszul regularity of the t_l
by lem-weil-pbc-localization-flat and lem-sc-koszul-regular-flat-base-change.
Apply lem-sfb-koszul-split-conormal-cancellation to K contained in J. It gives local
Koszul-regular generators for J/K = I in B/K = A. Further principal localizations
preserve regularity by the same flatness inputs. The affine criterion proves the base
immersion Koszul-regular, including when the polynomial dimension is zero.
4. For general smooth projection, choose affine base and ambient neighbourhoods of the
image points where both immersions are closed. Shrink the base by a principal open so
its inverse image in the source lies in the chosen ambient neighbourhood. The restricted
ambient neighbourhood is still affine, and its projection is smooth by
lem-weil-pbc-smooth-restrict-open-subschemes. The affine smooth comparison
lem-weil-pbc-smooth-ring-map-iff-smooth-affine and def-weil-pbc-smooth-ring-map give a
finite presentation, hence a closed embedding of the ambient neighbourhood into affine
space over the base.
5. Both this affine space and the ambient neighbourhood are smooth over the base
(sbc-lem-affine-space-smooth). By lem-pur-smooth-pair-regular-immersion the embedding
has local regular equations, hence Koszul-regular equations by
lem-weil-pbc-regular-sequence-koszul-regular. The original immersion remains
Koszul-regular after restriction, using flat localization as above. The composition
lem-sfb-koszul-immersion-composition is therefore Koszul-regular. Apply the polynomial
case to this composition. Since the original source point was arbitrary, the result
holds at every point. -/
theorem isKoszulRegularImmersion_of_smooth_comp {Z P S : Scheme.{u}}
    (i : Z ⟶ P) (p : P ⟶ S) (j : Z ⟶ S) (h : i ≫ p = j)
    [Smooth p] [IsImmersion i] [IsImmersion j]
    (hi : ∀ z : Z, IsKoszulRegularImmersionNear i z) :
    ∀ z : Z, IsKoszulRegularImmersionNear j z := by
  sorry

end AlgebraicGeometry
