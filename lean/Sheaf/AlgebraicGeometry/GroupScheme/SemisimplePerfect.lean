/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple

/-! # Semisimple algebraic groups are perfect

Source: Milne, Algebraic Groups (2017), Corollary 21.50, printed p.440.
(blueprint: lem-sfb-semisimple-group-perfect)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A semisimple affine group over an algebraically closed field is its own derived
subgroup. The identity inclusion being derived says exactly that the smallest closed
subgroup through which the commutator morphism factors is the whole group.

Source: Milne, Corollary 21.50, printed p.440.
(blueprint: lem-sfb-semisimple-group-perfect)

Proof: semisimplicity implies reductivity and gives a split maximal torus T, by
lem-sfb-reductive-borel-pair-structure. The smooth connected derived subgroup D exists
by lem-sfb-smooth-connected-derived-subgroup. Root subgroup parametrizations and
coroots are supplied by lem-sfb-reductive-root-subgroup-parametrizations. Choose a root
s of X³-X-1 in F. Then s(s²-1)=1, so both s and c=s²-1 are units in every characteristic.
For each root alpha, t=alpha-coroot(s) satisfies
[t,u_alpha(a/c)]=u_alpha(s²a/c)u_alpha(-a/c)=u_alpha(a)
over every F-algebra. Thus each root subgroup inclusion factors through D as a scheme
morphism. By lem-sfb-semisimple-root-subgroups-generate, D=H. The same generation
statement includes the empty root family and hence the trivial group. -/
theorem semisimpleGroupScheme_perfect (F : Type u) [Field F] [IsAlgClosed F]
    (H : Over (Spec (.of F))) [GrpObj H] (hH : IsSemisimpleGroupScheme H) :
    IsDerivedGroupScheme (𝟙 H) := by
  sorry

end AlgebraicGeometry
