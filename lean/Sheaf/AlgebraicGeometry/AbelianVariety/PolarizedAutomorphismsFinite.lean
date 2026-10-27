/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.AbelianVariety.PoincareBiduality
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AbelianVariety.HomFiniteFree

/-! # Finiteness of polarized abelian-variety automorphisms

Source: Milne, Abelian Varieties, I Proposition 14.4(a), p.62;
polarization convention in I Section 11, p.53.
(blueprint: lem-sfb-polarized-abelian-automorphisms-finite).

The specified dual datum represents rigidified algebraically trivial line bundles.
The polarization classifies the normalized translated-difference family of L.
Its stabilizer is a subtype of scheme automorphisms over the field: the group-homomorphism
condition excludes translations. The existential dual map is pinned down by its
rigidified Poincare pullback characterization, rather than supplied arbitrarily.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The group of group-scheme automorphisms preserving an ample polarization is finite.
Categorical composition writes the preservation equation as `a.hom ≫ lambda ≫ aDual = lambda`.
`ClassifiesAbelianDualHom` says precisely that aDual is pullback on the represented Picard
identity component, respecting the identity-axis rigidification.

Source: Milne AV I Proposition 14.4(a), p.62; Section 11, p.53
(blueprint: lem-sfb-polarized-abelian-automorphisms-finite).

Proof plan:
1. Apply lem-sfb-abelian-hom-finite-free with B=A. The integral endomorphism group M has
   a finite integer basis. Its rationalization V contains M injectively, by the coordinate
   inclusion Z^r into Q^r, also when r=0. Composition extends bilinearly and preserves 1.
2. Apply lem-sfb-rosati-trace-positive to L and lambda. The rational inverse mu of lambda
   gives u-dagger = mu u-dual lambda and the symmetric positive definite rational form
   B(u,v) = Tr(u-dagger v), with Tr(1)=2 dim(A). No principal polarization is assumed.
3. Preservation gives a-dagger a = mu a-dual lambda a = mu lambda = 1. Consequently every
   automorphism in the subtype has B(a,a)=2 dim(A), and lies in the lattice sublevel
   B(m,m) <= 2 dim(A). Only rational homomorphisms are used to invert lambda.
4. Apply lem-sfb-positive-form-lattice-sublevels-finite to this sublevel. Forgetting the
   inverse and the preservation proof injects the displayed subtype into that finite set:
   a scheme isomorphism is determined by its underlying morphism. Hence it is finite.
The source's compactness sentence is applied to the positive-form sublevel, as in the DAG,
not to the whole real endomorphism space. -/
theorem polarized_abelian_automorphisms_finite
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (D : AbelianDualPoincareDatum A)
    (L : A.left.Modules) [Scheme.Modules.IsInvertible L] (hL : IsAmple A.hom L)
    (lambda : A ⟶ D.dual) (hlambda : ClassifiesAbelianDifference D L lambda) :
    Finite {a : A ≅ A // IsMonHom a.hom ∧
      ∃ aDual : D.dual ⟶ D.dual,
        ClassifiesAbelianDualHom D D a.hom aDual ∧
          a.hom ≫ lambda ≫ aDual = lambda} := by
  sorry

end AlgebraicGeometry
