/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Constructible

/-!
# Constructible abelian sheaves with finite values

Source: Stacks Project, Tags 03RU, 03RW(2), 095E(3), with the global finite-partition
convention of the blueprint (blueprint: def-weil-pbc-constructible-abelian-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An abelian sheaf is constructible with finite values if a single finite partition
into constructible locally closed subschemes makes it locally constant with finite abelian
values. Restrictions to strata and to members of their étale covers are abelian inverse
images; the trivializations are isomorphisms of abelian sheaves, not just of underlying sets.
This is the global-partition convention, agreeing on qcqs schemes with Stacks 03RW(2)
by 095E(3); finite local constancy is as in 03RU.
(blueprint: def-weil-pbc-constructible-abelian-sheaf) -/
def IsConstructibleAbelianSheaf {T : Scheme.{u}}
    (C : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∃ S : LocallyClosedStratification T,
    (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) ∧
    ∀ k : Fin S.n, ∃ V : Cover.{u} etalePrecoverage (S.domain k),
      ∀ i : V.I₀, ∃ A : AddCommGrpCat.{u + 1}, Finite A ∧
        Nonempty
          ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (V.f i)).obj
            ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion k)).obj C) ≅
            (constantSheaf (V.X i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)

end AlgebraicGeometry.Scheme
