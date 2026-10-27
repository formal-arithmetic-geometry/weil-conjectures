/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.RelativeSplitTorus

import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Sheaf.AlgebraicGeometry.AffineSpaceOpenInvertibleTrivial

/-! # Invertible modules on Laurent space over a normal scheme

Source: Stacks Project, Divisors, Tags 0BD7 (`lemma-in-image-pullback`) and
0BDA (`lemma-open-subscheme-UFD`), with Properties, Tag 033N.
(blueprint: lem-sfb-normal-laurent-line-invariance).

The existing `relativeSplitTorus X r` is the Laurent-space scheme over `X`.
Its projection is the structure map of its object in `Over X`; its identity
section is the base change of the Hopf counit, which sends every monomial to 1.
Its construction uses A = Gamma(X, O_X) and A[Z^r]; the canonical identification
A tensor_Z Z[Z^r] = A[Z^r] identifies it with X times Spec Z[Z^r] over Spec Z.
Thus no new torus, projection, section, or module-pullback notion is introduced.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Modules

/-- Every invertible module on the split torus over a locally Noetherian normal
scheme is isomorphic to the pullback of its restriction to the identity section.
No action, ampleness, connectedness, nonemptiness, or positive-rank assumption
is imposed. Both pullbacks are the recorded tensor inverse-image functors.

Source: Stacks Project, Divisors, Tags 0BD7 and 0BDA, applied componentwise;
Properties, Tag 033N
(blueprint: lem-sfb-normal-laurent-line-invariance).

Proof:
1. Decompose X into disjoint open normal integral components X_a. On each
Noetherian affine chart, `rem-pc-regular-normal`(2) gives finitely many disjoint
normal integral components. By `lem-sc-components-open-injection`, restriction
of a global irreducible component meeting a chart is a chart component and is
injective on components. Consequently global components are open and distinct
ones are disjoint. They cover X, and their original normal-domain stalks make
them reduced and integral (`def-pc-integral-scheme`). They remain locally
Noetherian (`pqf-def-locnoeth`); no quasi-compactness of X is needed.
2. Over Spec R put P = R[t_1,...,t_r] and f = product t_i. Laurent space is
Spec P_f: send t_i to z_i and 1/f to product z_i^(-1); the inverse sends z_i
to t_i and z_i^(-1) to (product over j != i of t_j)/f. These maps are inverse
on generators and commute with restrictions in R. By
`lem-weil-pbc-affine-ideals-closed-subscheme`(0), this is the principal open D(f)
of Spec P, including f = 1 when r = 0.
3. The polynomial projection is flat (`lem-nagata-polynomial-projection-flat`);
restriction to D(f) preserves source local rings, so q_a is flat
(`def-weil-flat-morphism`). The 2r Laurent generators give local finite type
(`def-weil-finite-type-morphism`), and `pqf-lem-locnoeth-lft` makes its source
locally Noetherian.
4. By `lem-weil-pbc-fibre-product-affine-spectra`, its fibre over x has ring
kappa(x) tensor_R R[Z^r], canonically kappa(x)[Z^r] by multiplying coefficients
on pure tensors. This is D(product t_i) in affine r-space over kappa(x).
The polynomial ring is a domain (`lem-sfb-polynomial-field-ufd`), the monomial
is nonzero, and localization is a nonzero domain. Its spectrum is therefore
nonempty and integral (`def-pc-integral-scheme`).
5. The generic fibre is an open of affine space over the generic residue field.
The restriction of N is invertible (`def-sc-invertible-module`,
`def-pc-module-pullback`), hence trivial by
`lem-sfb-affine-space-open-invertible-trivial`. Apply
`lem-sfb-normal-noetherian-generic-line-pullback`: steps 1, 3 and 4 check its
normal integral locally Noetherian base, locally Noetherian source, flatness,
local finite type, and integral nonempty fibres. It gives an invertible M_a
and an isomorphism alpha_a : q_a^* M_a to N restricted to Y_a.
6. Evaluation at 1 gives e_a followed by q_a equal to the identity. Pulling
alpha_a back along e_a and using the composition and identity comparisons of
`def-pc-module-pullback` gives beta_a : M_a to e_a^*(N restricted to Y_a).
Then alpha_a composed with q_a^*(beta_a inverse) gives the required local
isomorphism q_a^* e_a^*(N restricted to Y_a) to N restricted to Y_a.
7. The Y_a are pairwise disjoint opens covering Laurent space. Tensor inverse
image restricts to the indicated pullbacks on Y_a (`def-pc-module-pullback`).
Glue the local isomorphisms and their inverses: on an open V the sheaf axiom
identifies sections with the product of sections on V intersect Y_a, so apply
the local maps coordinatewise. They commute with restrictions and scalars.
The empty X uses the empty cover. At r = 0 the torus is X and the section and
projection identify with the identity, giving the same conclusion. -/
theorem nonempty_iso_tensorPullback_identity_relativeSplitTorus
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (r : ℕ) (N : (relativeSplitTorus X r).X.left.Modules) [N.IsInvertible] :
    Nonempty ((tensorPullback (relativeSplitTorus X r).X.hom).obj
      ((tensorPullback (η[(relativeSplitTorus X r).X]).left).obj N) ≅ N) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
