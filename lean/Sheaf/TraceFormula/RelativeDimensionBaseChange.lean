/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.PureDimension
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange

/-! # Pure relative dimension is preserved by base change

Source: Stacks Project, Morphisms, Tag 02NK (lemma-base-change-relative-dimension-d),
using Tag 02FY (lemma-fibre-dimension-after-base-change).
(blueprint: lem-trf-relative-dimension-base-change)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A locally finite type morphism whose nonempty fibres are pure of dimension `d`
remains so after arbitrary base change.  For a base-change morphism `g : S' ⟶ S`,
the base-changed morphism is the second pullback projection
`pullback.snd f g : pullback f g ⟶ S'`.

Source: Stacks Project, Morphisms, Tag 02NK (lemma-base-change-relative-dimension-d),
using Tag 02FY (lemma-fibre-dimension-after-base-change).

Proof: Let `s' : S'` and assume the fibre of `pullback.snd f g` at `s'` is
nonempty.  The locally-finite-type base-change lemma makes this morphism locally
of finite type.  The fibre-dimension-after-base-change identification compares
its local dimensions with those of the fibre of `f` at the image of `s'`.
The pure-dimension hypothesis, together with the locally algebraic local-dimension
criterion and the locally Noetherian component criterion, therefore makes every
irreducible component of this base-changed fibre have dimension `d`.  Empty fibres
are covered by the explicit nonempty premise.

(blueprint: lem-trf-relative-dimension-base-change)
-/
theorem pure_relative_dimension_base_change
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (d : ℕ)
    (hpure : ∀ s : S, Nonempty (f.fiber s) → (f.fiber s).IsPureDimension d)
    (g : S' ⟶ S) :
    ∀ s' : S', Nonempty ((pullback.snd f g).fiber s') →
      ((pullback.snd f g).fiber s').IsPureDimension d := by
  sorry

end AlgebraicGeometry
