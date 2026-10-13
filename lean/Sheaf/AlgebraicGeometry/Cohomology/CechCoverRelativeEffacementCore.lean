/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Topology.Sheaves.CechCohomology

/-! # Cover effacement before inverse image

Source: `lem-pc-cech-cover-relative-effacement`, product and contraction paragraphs.
The construction is an expansion of that node's argument, written by an agent;
Stacks Project, Tags 01EQ and 01FD, supply its comparison context.
(blueprint: lem-pc-cech-cover-relative-effacement-core)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Core cover effacement: the quotient is sectionwise surjective and locally split,
with surjective Čech connecting maps. The inverse-image clause is derived separately.
Source: `lem-pc-cech-cover-relative-effacement`, product and contraction paragraphs
(agent-written expansion in the context of Stacks Project, Tags 01EQ and 01FD).
(blueprint: lem-pc-cech-cover-relative-effacement-core)

Proof: For j_i : U_i → X put E_i = (j_i)_*(F|U_i), E = ∏_i E_i, and let
f : F → E have components the restriction-adjunction units. On each U_i,
projection to E_i followed by the restriction-adjunction counit retracts f,
by the triangle identity. A section killed by f vanishes on every U_i;
the sheaf uniqueness axiom and the covering hypothesis make f monic. Take
Q = cokernel f and the cokernel short exact sequence T, with T.X₁ = F.
Restriction is exact, so its monic first arrow with the displayed retraction
splits the restricted sequence. Restricting its quotient section further to
any tuple intersection gives hg, since that intersection lies in its first member.
On an intersection W, E_i(W) = F(W ∩ U_i). In the Čech complex of E_i,
define h in positive degree by inserting i at the front of the tuple. The
intersection is unchanged by that insertion because U_i is already present
in the coefficient restriction. In dh + hd, the face deleting the inserted i
is the identity; all other faces cancel in pairs with opposite signs. Thus
positive-degree cocycles are boundaries. Products of these contractions give
the same identity for E, since products of sheaves are computed sectionwise.
Hence the positive Čech cohomology of E vanishes. The tuplewise exact sequence
of cochain groups is short exact (hg makes the product quotient map surjective).
Its long exact homology sequence says the image of each connecting map is the
kernel of the map into the zero positive cohomology group of E, giving hδ.
If the index type is empty, the covering hypothesis makes X empty, all sheaves
are zero, the same cokernel construction is exact, and all Čech groups vanish. -/
theorem exists_cechCoverRelativeEffacement_core
    {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ∃ (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})),
      T.X₁ = F ∧ ∃ (hT : T.ShortExact)
        (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
          Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))),
        (∀ i, IsSplitMono ((U i).sheafRestrict.map T.f)) ∧
        ∀ q, Function.Surjective (TopCat.Sheaf.cechδ U hT hg q) := by sorry

end AlgebraicGeometry.Scheme.Modules
