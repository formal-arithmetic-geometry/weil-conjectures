/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Grp
import Sheaf.AlgebraicGeometry.GroupoidScheme

/-!
# Open images of homomorphisms of group schemes over a field

Source: Stacks Project, Tag 047S, `lemma-open-subgroup-closed-over-field`
(blueprint: lem-sfb-field-open-group-image-closed).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An open point image of a homomorphism of group schemes over a field is closed.

Source: Stacks Project, Tag 047S, `lemma-open-subgroup-closed-over-field`
(blueprint: lem-sfb-field-open-group-image-closed).

Proof: Regard each group scheme as an absolute groupoid scheme with object scheme
`Spec k`, source and target both the structure morphism, and unit, inverse and composition
its group operations. The group diagrams give the groupoid axioms
(`def-sc-group-scheme`, `def-a1-groupoid-scheme`). The homomorphism, together with the
identity on `Spec k`, commutes with all these operations. Apply
`lem-sfb-field-groupoid-open-image-closed` (Stacks Tag 04Q6) to this morphism of groupoids:
its open point image is closed. This is the given subset of the target group scheme.
-/
theorem isClosed_range_of_isMonHom_of_isOpen (k : Type u) [Field k]
    {P Q : Over (Spec (CommRingCat.of k))} [GrpObj P] [GrpObj Q]
    (f : P ⟶ Q) [IsMonHom f] (hopen : IsOpen (Set.range f.left)) :
    IsClosed (Set.range f.left) := by
  sorry

end AlgebraicGeometry
