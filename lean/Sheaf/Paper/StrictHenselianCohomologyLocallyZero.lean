/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.EtaleCohomologyLocalRingColimit
import Sheaf.Paper.StrictlyHenselianEtaleAcyclic
import Sheaf.CategoryTheory.KInjectiveComputes

/-! # Positive étale cohomology classes are Zariski locally zero

Source: Stacks Project, Étale Cohomology, Tag 09AX, proof, Tags 03Q6 and 03QO.
(blueprint: lem-weil-pbc-strict-henselian-cohomology-locally-zero)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- Every positive-degree class on an open becomes zero near each point when all
local rings are strictly henselian.

Source: literature/stacks-project/etale-cohomology.tex, Tag 09AX, proof,
third and fourth sentences; Tags 03Q6 and 03QO.
(blueprint: lem-weil-pbc-strict-henselian-cohomology-locally-zero)

Proof: Evaluate an injective resolution on each etale object `i(U)`. The free
abelian sheaf on the representable represents this evaluation, so its Ext groups
are the cohomology of that section complex. Comparison of resolutions makes this
identification natural in `U`, including the restriction maps. Restriction to an
etale object preserves injectives because its extension-by-zero left adjoint is
exact. Thus these groups are also cohomology of the restricted sheaf on `U`.
The equality `hi_inclusion` identifies the underlying schemes and restriction
arrows with the open subschemes and their inclusions. It need not identify the
structural arrow of `i(⊤)` with the identity. First restrict `F` to that etale
object, whose underlying scheme is `X`; all `i(U)` are its open restrictions.
For a point `x` of `U`, the filtered colimit of these groups over neighbourhoods
of `x` is cohomology on `Spec (X.presheaf.stalk x)` of this restricted sheaf's
pullback (03Q6). Use a bounded-below injective resolution, which is K-injective,
to compare this description with the derived-cohomology vanishing of 03QO.
This group is zero in positive degree: sections on a strictly henselian local
scheme are evaluation at its closed geometric point and hence exact (03QO).
Thus the image of the given class in the colimit is zero. In a filtered colimit
of abelian groups this means its restriction is zero at a later index. Intersect
that neighbourhood with `U` to obtain the required smaller neighbourhood. All
identifications here preserve the canonical restriction maps, not just the groups.
The empty open has no points, and degree zero is deliberately excluded. -/
theorem strictHenselian_cohomology_locally_zero
    {X : Scheme.{u + 1}}
    (hX : ∀ x : X, IsStrictlyHenselianLocalRing (X.presheaf.stalk x))
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (hq : 0 < q) (U : X.Opens)
    (ξ : (i.op ⋙ Sheaf.cohomologyPresheaf F q).obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      (i.op ⋙ Sheaf.cohomologyPresheaf F q).map (homOfLE hVU).op ξ = 0 := by sorry
