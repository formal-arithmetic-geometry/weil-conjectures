/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dual.Defs
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality

/-!
# The Lie algebra and the cotangent dual at the identity

Source: blueprint `sk-i-cartier`, third paragraph, and the dimension paragraph of
`lem-wf-same-lie-closed-subgroup`.
(blueprint: lem-ag-lie-identity-cotangent-dual)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

/-- The Lie algebra is the dual of the cotangent space at the rational identity, with
scalars transported by the residue-field identification. No smoothness is required.

Source: blueprint `sk-i-cartier`, third paragraph, and
`lem-wf-same-lie-closed-subgroup`, dimension paragraph; Stacks Project, Tag 0B2C.
(blueprint: lem-ag-lie-identity-cotangent-dual)

Proof: Put `x = e(Spec k)` and `R = O(G,x)`. The section equation `e ≫ p = id`
identifies the residue field at `x` with `k`: the composite from `k` to the residue
field and back along `e` is the identity, and the map back is an injective map of
fields. The structural residue map is therefore bijective; let `r` be this ring
isomorphism. An infinitesimal point of the group is a dual-number morphism whose
restriction is `e`. Transport the dual numbers along `r` to identify these with the
rational tangent vectors at `x`. The library equivalence `lieEquiv` identifies the
infinitesimal points with `Lie G`; its multiplication-to-addition and scaling
identities identify the additive and scalar structures. Rational tangent-cotangent
duality identifies these tangent vectors with the `k`-linear dual of `m/m²`, by
taking the epsilon coefficient of the induced stalk map. Transport the values of
a functional by `r` to obtain the residue-field-linear dual. These identifications
compose to the asserted semilinear equivalence. Each inverse is given by the
inverse construction (a functional defines the local map `a ↦ residue(a) + D(a) ε`),
so the equivalence is bijective. More explicitly, let `i : k → R` be the structural
map and write `a₀ = a - i (r.symm (residue a))`, which lies in the maximal ideal.
For a residue-field-linear functional `φ`, set `D(a) = φ([a₀])`. Modulo the square
of the maximal ideal, `(ab)₀ = residue(a) b₀ + residue(b) a₀`, so this defines a
relative derivation and the stated local dual-number map. Its image lies at `x`,
hence an affine neighbourhood of `x` reconstructs the scheme morphism; this is
independent of the neighbourhood. Differentiating group multiplication at `(e,e)`
sends `(v,w)` to `v+w`: its restrictions to either factor are the identity by the
unit laws, and its differential is linear. Thus the group law on infinitesimal
points agrees with addition of functionals. Scaling epsilon scales the functional,
so the composed bijection is semilinear for the displayed ring isomorphism.
This argument includes cotangent space zero and requires neither finite dimension
nor regularity. -/
theorem exists_lie_identity_cotangent_dual_equiv
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let R := G.left.presheaf.stalk (unitSection G (IsLocalRing.closedPoint k))
    ∃ r : k ≃+* IsLocalRing.ResidueField R,
      letI : RingHomInvPair r.toRingHom r.symm.toRingHom :=
        RingHomInvPair.of_ringEquiv r
      letI : RingHomInvPair r.symm.toRingHom r.toRingHom :=
        RingHomInvPair.of_ringEquiv r.symm
      Nonempty (Lie G ≃ₛₗ[r.toRingHom]
        Module.Dual (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) := by sorry

end AlgebraicGeometry.GrpObj
