/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-!
# Finitely many unit lines with bounded inverses

Source: agent-formulated finite-coordinate auxiliary lemma supporting Milne,
Algebraic Groups, Proposition 12.48, pp. 246-247. Geometric tools: Stacks Project,
Tags 01N0, 01M4, 01WC, 0478, 01TB and 01WN.
(blueprint: lem-sfb-bounded-inverse-unit-lines)

The quotient is represented by the image of the bounded-inverse units in the existing
scalar-orbit quotient of `Aˣ`. No finite generation of the algebra is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace Units

/-- Over an algebraically closed field, units in a finite-dimensional subspace whose
inverses lie in another finite-dimensional subspace have finitely many scalar classes.
The scalar action on units is the canonical one induced by the algebra structure; its
orbits identify exactly units `a, a'` with `a' = c * a` for a nonzero scalar `c`.

Source: agent-formulated auxiliary lemma for Milne, Algebraic Groups, Proposition 12.48,
pp. 246-247 (blueprint: lem-sfb-bounded-inverse-unit-lines).

Proof plan, following the eight steps of the DAG node:
1. If either subspace is zero there are no such units. Otherwise choose finite bases
   `v_i`, `w_j` and a basis `e_0 = 1, e_1, ..., e_t` of the space spanned by `1` and all
   products `v_i * w_j`. Write the products with coefficients `c_kij` in this basis.
2. In projective space with coordinates `z_ij`, impose the rank-one quadrics and the
   linear equations `l_k = sum c_kij * z_ij = 0` for `k > 0`. The graded quotient defines
   a closed subscheme `Z`, using prop-nagata-relative-proj-functoriality. On the charts
   of prop-nagata-proj-standard-open, its rational points are rank-one matrices `x_i*y_j`
   giving nonzero `v` in `V`, `w` in `W` with `v*w = l_0 * 1`.
3. Projective space is proper by lemma-nagata-projective-space-base-change-proper;
   lem-weil-pbc-closed-immersion-proper makes `Z` proper, hence finite type over `F`.
4. If the closed subset where `l_0` vanishes were nonempty, the Jacobson property
   (lem-sc-lft-over-field-jacobson-space) would give a closed point there. Its residue
   field is `F` by lem-weil-pbc-closed-point-residue-field-base, so step 2 would give
   nonzero elements with product zero, contrary to the domain hypothesis.
5. Thus `Z` lies in the affine standard open `D_+(l_0)`. Its closed immersion there
   makes it affine, including when `l_0 = 0`, in which case `Z` is empty.
6. Apply lem-sfb-affine-proper-finite, then lem-weil-pbc-finite-closed-map-finite-fibres:
   the underlying point set of `Z`, its fibre over `Spec F`, is finite.
7. A rational point is determined by its support: on an affine chart the induced map
   from its residue field to `F` is inverse to the structure map. Hence `Z(F)` is finite,
   even if `Z` is nonreduced.
8. Send `a` to the rank-one coordinates of `(a, a⁻¹)`. Scalar multiplication leaves
   these coordinates fixed; equality of the projective points forces the two units
   to differ by a nonzero scalar. This injects the stated set of orbits into `Z(F)`.
   Conversely `v*w = d*1` with `d` nonzero gives the unit `v` with inverse `d⁻¹*w`.
-/
theorem finite_boundedInverse_scalarOrbits
    (F : Type u) [Field F] [IsAlgClosed F]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra F A]
    (V W : Submodule F A) [FiniteDimensional F V] [FiniteDimensional F W] :
    Set.Finite
      (Quotient.mk (MulAction.orbitRel Fˣ Aˣ) ''
        {a : Aˣ | (a : A) ∈ V ∧ ((a⁻¹ : Aˣ) : A) ∈ W}) := by
  sorry

end Units
