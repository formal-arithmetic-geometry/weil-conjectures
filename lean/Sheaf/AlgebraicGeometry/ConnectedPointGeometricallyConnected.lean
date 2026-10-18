/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Algebraic.Defs
public import WeilConjectures.ZetaSeries
import Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible
import Sheaf.AlgebraicGeometry.GeometricallyConnectedImageCriterion

/-!
# Geometric connectedness from a residue-field point

Source: Stacks Project, Varieties, Tag 04KV,
`lemma-geometrically-connected-if-connected-and-point`
(blueprint: lem-trf-connected-point-geometrically-connected).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A connected scheme over a field is geometrically connected if the base field is
algebraically closed in the residue field of one of its points. Algebraicity and membership
in the base field both use the canonical embedding induced by the structure morphism.

Source: Stacks Project, Varieties, Tag 04KV,
`lemma-geometrically-connected-if-connected-and-point`
(blueprint: lem-trf-connected-point-geometrically-connected).

Proof:
1. Set `T = Spec κ(x)` and use the canonical morphism `X.fromSpecResidueField x : T ⟶ X`.
   Apply `lem-zl-field-extension-algebraically-closed-geometric` to the canonical extension
   `κ(x)/k`: the hypothesis says exactly that every algebraic element lies in the image of k.
   Thus T is geometrically irreducible. After every field extension its base change is
   irreducible, hence connected by `lem-pc-irreducible-space-connected`. By
   `def-pc-geometrically-irreducible`, T is geometrically connected over k.
2. The canonical morphism T → X is over k, and X is connected by assumption. Apply
   `lem-trf-geometrically-connected-image-criterion` (Stacks Tag 056R) to conclude that X is
   geometrically connected over k, meaning that its base change to every field extension is
   connected.
-/
theorem GeometricallyConnected.of_connectedSpace_of_isAlgebraic_residueField
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [ConnectedSpace X] (x : X)
    (h : ∀ a : X.residueField x,
      @IsAlgebraic k (X.residueField x) _ _
          ((X ↘ Spec (.of k)).residueFieldAlgebraMap x).toAlgebra a →
        ∃ b : k, (X ↘ Spec (.of k)).residueFieldAlgebraMap x b = a) :
    GeometricallyConnected (X ↘ Spec (.of k)) := by
  sorry

end AlgebraicGeometry
