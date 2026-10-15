/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite

import Sheaf.FieldTheory.CommonExtensionFields
import Mathlib.FieldTheory.IsSepClosed

/-!
# Geometric component counts and base change

Source: Stacks Project, More on Morphisms, Tag 055F,
`lemma-base-change-fibres-nr-geometrically-connected-components`
(blueprint: lem-weil-pbc-geometric-component-count-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Geometric connected-component counts are independent of the algebraically closed
extension of the residue field and commute with arbitrary base change. The count is
`ENat.card` of `ConnectedComponents`: zero for an empty fibre and infinity for infinitely
many components.

Source: Stacks Project, More on Morphisms, Tag 055F
(blueprint: lem-weil-pbc-geometric-component-count-base-change).

Proof: First embed two algebraically closed extensions of the same residue field into a
common field using `Field.exists_common_extension` [lem-weil-common-extension-fields].
Algebraically closed fields are separably closed [def-pc-separably-closed]. The projections
from the common extension induce component bijections by
[lem-weil-pbc-sepclosed-field-components-bijection]. The pullback universal property
[def-pc-fibre-product] identifies their source schemes, proving independence of the field.
Next, for `t` over `s`, use the residue-field embedding from `κ(s)` to `κ(t)`
[def-weil-residue-field] to embed the two chosen closed fields into a common field over
`κ(s)`. The pullback universal property identifies both further base changes with the
same scheme over that field. Apply the same component bijections and compose them with
the homeomorphism induced by this identification. Their extended-natural cardinalities
agree, including the empty and infinite cases. Independence already proved makes this
exactly the claimed equality of geometric component counts. -/
theorem geometricComponentCount_baseChange {X S : Scheme.{u}} (f : X ⟶ S) :
    (∀ (s : S) (K L : Type u) [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]
      (i : S.residueField s ⟶ CommRingCat.of K)
      (j : S.residueField s ⟶ CommRingCat.of L),
      ENat.card (ConnectedComponents
        (pullback f (Spec.map i ≫ S.fromSpecResidueField s) : Scheme.{u})) =
      ENat.card (ConnectedComponents
        (pullback f (Spec.map j ≫ S.fromSpecResidueField s) : Scheme.{u}))) ∧
    (∀ (T : Scheme.{u}) (g : T ⟶ S) (t : T)
      (K L : Type u) [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]
      (i : S.residueField (g t) ⟶ CommRingCat.of K)
      (j : T.residueField t ⟶ CommRingCat.of L),
      ENat.card (ConnectedComponents
        (pullback (pullback.snd f g)
          (Spec.map j ≫ T.fromSpecResidueField t) : Scheme.{u})) =
      ENat.card (ConnectedComponents
        (pullback f (Spec.map i ≫ S.fromSpecResidueField (g t)) : Scheme.{u}))) := by
  sorry

end AlgebraicGeometry
