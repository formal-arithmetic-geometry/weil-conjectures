/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import WeilConjectures.RingTheory.GRing

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.RingTheory.RegularLocalMaximal
import WeilConjectures.RingTheory.RegularRingEquiv

/-! # Regular morphisms and their stalk maps

Source: Stacks Project, More on Morphisms, Tag 07R8, equivalence of (2) and (3),
and More on Algebra, Tag 07C0
(blueprint: lem-per-regular-scheme-stalk-criterion).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism of locally Noetherian schemes is regular exactly when every induced
local homomorphism on structure-sheaf stalks is a regular ring map.
Source: Stacks Project, Tags 07R8 and 07C0
(blueprint: lem-per-regular-scheme-stalk-criterion).

Proof:
1. For affine opens U in X and V in Y with f(U) contained in V, let A and B be their
   section rings and let phi : A → B be the section map. At x in U, the affine stalk
   localization identifications of lem-weil-pbc-affine-open-stalk-localization identify
   the stalk map with A_p → B_q, where q corresponds to x and p = phi⁻¹(q) to f(x).
   Indeed, compatibility with germs sends a_y to phi(a)_x; locality gives the equality
   of primes, and fractions consequently map to the corresponding fractions of germs.
2. If f is regular, choose V around f(x) and U around x inside f⁻¹(V), using
   lem-weil-pbc-affine-opens-basis. The affine criterion
   lem-per-regular-morphism-affine-criterion gives regularity of phi. The target B is
   Noetherian by pqf-lem-affine-open-locnoeth. Apply the prime-local direction of
   lem-weil-pbc-regular-local-maximal, then transport to the stalk map using step 1
   and lem-weil-pbc-regular-ring-map-ring-equiv.
3. Conversely, if every stalk map is regular, take any such pair of affine opens.
   Step 1 and lem-weil-pbc-regular-ring-map-ring-equiv give regularity of every
   A_p → B_q. Since B is Noetherian by pqf-lem-affine-open-locnoeth, the converse of
   lem-weil-pbc-regular-local-maximal gives regularity of phi. The affine criterion
   lem-per-regular-morphism-affine-criterion then gives regularity of f. For empty X,
   both the pointwise and prime-local conditions are vacuous, so the argument still applies. -/
theorem isRegularSchemeMorphism_iff_stalkMap
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) :
    IsRegularSchemeMorphism f ↔ ∀ x : X, (f.stalkMap x).hom.IsRegular := by
  sorry

end AlgebraicGeometry
