/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Finite generation by sections on affine etale charts

Source: Stacks Project, Tag 03SA, finite extension-by-zero generators; blueprint
`lem-kun-cp-approximation` (blueprint: def-kun-finitely-generated-etale-subsheaf).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- A subsheaf is finitely generated if it is the smallest subsheaf containing a finite
family of sections on affine etale charts. Containment of a section means that it lifts
through the subsheaf inclusion. This is equivalently the image of the finite sum of
extension-by-zero generators in Stacks Project, Tag 03SA.
(blueprint: def-kun-finitely-generated-etale-subsheaf). -/
def IsFinitelyGeneratedEtaleSubsheaf {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (G : Subobject F) : Prop :=
  ∃ (n : ℕ) (U : Fin n → X.Etale),
    (∀ j, IsAffine (U j).left) ∧
    ∃ s : (j : Fin n) → F.obj.obj (op (U j)),
      (∀ j, ∃ t : (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj.obj (op (U j)),
        G.arrow.hom.app (op (U j)) t = s j) ∧
      ∀ H : Subobject F,
        (∀ j, ∃ t : (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj.obj (op (U j)),
          H.arrow.hom.app (op (U j)) t = s j) → G ≤ H

end AlgebraicGeometry.Scheme
