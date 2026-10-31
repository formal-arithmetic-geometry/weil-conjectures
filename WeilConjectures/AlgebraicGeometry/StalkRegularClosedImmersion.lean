/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular closed immersions tested on the closed support

Source: ILO, Exposé XVI, Definition 2.3.1; Stacks Project, Tag 0638
(blueprint: def-per-stalk-regular-closed-immersion).

On Noetherian schemes the stalk criterion is equivalent to local generation by a regular
sequence. Testing only points of the source retains open-and-closed immersions in degree zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The ideal of a closed immersion is generated, at each point of its support, by a regular
sequence of length `c`. On Noetherian schemes this is the usual regular closed immersion of
constant codimension `c`, including zero. Source: ILO XVI 2.3.1; Stacks, Tag 0638
(blueprint: def-per-stalk-regular-closed-immersion). -/
def IsStalkRegularClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (c : ℕ) : Prop :=
  ∀ z : Z, ∃ r : List (X.presheaf.stalk (i z)),
    r.length = c ∧ RingTheory.Sequence.IsRegular (X.presheaf.stalk (i z)) r ∧
      Ideal.ofList r = RingHom.ker (i.stalkMap z).hom

end AlgebraicGeometry
