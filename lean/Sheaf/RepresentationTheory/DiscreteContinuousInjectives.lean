/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker M1
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Profinite
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import WeilConjectures.RepresentationTheory.DiscreteContinuousFunctorialInjectives

/-!
# Injective embeddings of discrete continuous representations

Source: Stacks Project, Injectives, Tag 04JF (blueprint:
lem-exc-discrete-modules-abelian-injective-embeddings).

## Main statements

- `Rep.discreteContinuousRep_functorialInjectiveEmbeddings`: functorial injective
  embeddings over a finite ring for a profinite group.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

-- The carrier universe contains the coefficient ring and the group, as in Tag 04JF's
-- group-ring construction and the general functorial embedding theorem.
/-- (blueprint: lem-exc-discrete-modules-abelian-injective-embeddings)
Stacks Project, Injectives, Tag 04JF, specialized to a profinite group and a finite ring.
First apply `lem-exc-rg-discrete-modules-functorial-injective-embeddings` to
`G` and `A`. Its category is the full subcategory of `Rep A G` satisfying the
open-stabilizer condition; it supplies `J`, `j`, monic components, and injective
targets. Then every component of `j` is an injective presentation, so the
category has enough injectives in the sense used by
`def-sp-injective-resolutions`. -/
theorem discreteContinuousRep_functorialInjectiveEmbeddings
    (A : Type u) [Ring A] [Finite A] (G : Type v) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] :
    (∃ (J : DiscreteContinuousRep.{u, v, max u v w} A G ⥤
          DiscreteContinuousRep.{u, v, max u v w} A G)
       (j : 𝟭 (DiscreteContinuousRep.{u, v, max u v w} A G) ⟶ J),
       ∀ M, Mono (j.app M) ∧ Injective (J.obj M)) ∧
      EnoughInjectives (DiscreteContinuousRep.{u, v, max u v w} A G) := by
  obtain ⟨J, j, hmono, hinj⟩ :=
    discreteContinuousRep_functorialInjectiveEmbeddings_of_topologicalGroup.{u, v, w} A G
  exact ⟨⟨J, j, fun M ↦ ⟨hmono M, hinj M⟩⟩,
    ⟨fun M ↦ ⟨⟨J.obj M, hinj M, j.app M, hmono M⟩⟩⟩⟩

end Rep
