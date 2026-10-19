/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.Irreducible

import Sheaf.AlgebraicGeometry.ProductIrreducibleComponentsBijection
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.FieldTheory.FieldTensorUniqueMinimalPrime

/-!
# Geometric irreducible-fibre component counts and base change

Source: literature/stacks-project/more-morphisms.tex, Tag 0556
(blueprint: lem-trf-geometric-fibre-component-count-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The number of irreducible components of a fibre after a separably closed residue-field
extension is independent of that extension and is preserved by arbitrary base change.

Source: literature/stacks-project/more-morphisms.tex, Tag 0556
(blueprint: lem-trf-geometric-fibre-component-count-base-change).

Universe transport: the schemes and residue rings are in `Scheme.{max u v}`, while the
chosen fields are in `Type v`; `ULift.{u}` is the canonical transport used to form the
`CommRingCat` objects required by `Spec.map`. For two separably closed extensions of a
residue field, embed them into a common field using `Field.exists_common_extension`.
Since the base fields are separably closed,
`IsSepClosed.field_tensor_unique_minimalPrime` makes the common-field spectrum geometrically
irreducible. The product irreducible-component bijection
`product_irreducibleComponents_bijOn_image` then identifies the component sets after each
extension, including empty and infinite sets. For a base change, use the residue-field map
and the fibre-product universal property to identify the two further base changes over a
common field, and apply the same component bijections. -/
theorem geometricFibreComponentCount_baseChange {X Y : Scheme.{max u v}} (f : X ⟶ Y) :
    (∀ (t : Y) (K L : Type v) [Field K] [Field L] [IsSepClosed K] [IsSepClosed L]
      (i : Y.residueField t ⟶ CommRingCat.of (ULift.{u} K))
      (j : Y.residueField t ⟶ CommRingCat.of (ULift.{u} L)),
      ENat.card (irreducibleComponents
        ↥(pullback f (Spec.map i ≫ Y.fromSpecResidueField t))) =
      ENat.card (irreducibleComponents
        ↥(pullback f (Spec.map j ≫ Y.fromSpecResidueField t)))) ∧
    (∀ (Y' : Scheme.{max u v}) (g : Y' ⟶ Y) (t' : Y')
      (K L : Type v) [Field K] [Field L] [IsSepClosed K] [IsSepClosed L]
      (i : Y.residueField (g t') ⟶ CommRingCat.of (ULift.{u} K))
      (j : Y'.residueField t' ⟶ CommRingCat.of (ULift.{u} L)),
      ENat.card (irreducibleComponents
        ↥(pullback (pullback.snd f g)
          (Spec.map j ≫ Y'.fromSpecResidueField t'))) =
      ENat.card (irreducibleComponents
        ↥(pullback f
          (Spec.map i ≫ Y.fromSpecResidueField (g t'))))) := by
  sorry

end AlgebraicGeometry
