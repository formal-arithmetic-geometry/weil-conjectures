/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Retracts as cokernels; matching invariant summands

In a preadditive category, a retract `X` of `Y` is the cokernel of the idempotent endomorphism
`𝟙 Y - r ≫ i` of `Y` (`CategoryTheory.Retract.isoCokernel`).

Two split monomorphisms onto "invariant summands" which are matched by an equivariant
isomorphism have isomorphic sources (`CategoryTheory.isIso_of_comp_eq_comp_of_coinvariant`), and
a retraction of a unit transports along functors together with its invariant-projector property
(`CategoryTheory.retraction_of_eq_comp_map_comp_of_coinvariant`).

A retract of a split monomorphism, for instance a morphism isomorphic to it as an arrow, is a
split monomorphism
(`CategoryTheory.RetractArrow.isSplitMono`, `CategoryTheory.Arrow.isSplitMono_of_iso`).
-/

@[expose] public section

namespace CategoryTheory.Retract

open Limits

variable {C : Type*} [Category* C] [Preadditive C] {X Y : C}

end CategoryTheory.Retract

namespace CategoryTheory

end CategoryTheory

namespace CategoryTheory.RetractArrow

variable {C : Type*} [Category* C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}

end CategoryTheory.RetractArrow

