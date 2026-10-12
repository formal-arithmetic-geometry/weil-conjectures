/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProperLimitNoetherian
import Sheaf.AlgebraicGeometry.LimitFibreProducts
import Sheaf.AlgebraicGeometry.ProperBasic
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.FiniteType

/-! # Descent of a proper-fibre idempotent to a Noetherian model

Source: Stacks Project, Tag 0G7X, general case before applying the Noetherian case.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An idempotent on a proper fibre descends to a proper morphism over a locally
Noetherian base, together with the commuting maps on schemes and fibres.
Source: Stacks, Tag 0G7X, Steps 5--8. First restrict the base to an affine
neighbourhood of s and apply proper Noetherian approximation. The residue field of s
is the filtered colimit of the stage residue fields, so the fibre is the inverse limit
of the stage fibres with affine transitions. Global sections commute with that limit:
descend e to a stage, then descend its equation e * e = e to a later stage. The
Noetherian model is that stage and the projections provide p, r and q. Commutation
with the fibre embeddings is the defining property of the induced fibre projections.
This statement asks for no section on a neighbourhood of s.
(blueprint: lem-weil-pbc-stein-fibre-idempotent-descent) -/
theorem proper_fibre_idempotent_descent
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S)
    (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ∃ (W : S.Opens) (hs : s ∈ W) (Y T : Scheme.{u}) (g : Y ⟶ T)
      (_ : IsProper g) (_ : IsLocallyNoetherian T)
      (p : (f ⁻¹ᵁ W).toScheme ⟶ Y) (r : W.toScheme ⟶ T)
      (a : f.fiber s ⟶ (f ⁻¹ᵁ W).toScheme)
      (q : f.fiber s ⟶ g.fiber (r ⟨s, hs⟩)) (e₀ : Γ(g.fiber (r ⟨s, hs⟩), ⊤)),
      p ≫ g = (f ∣_ W) ≫ r ∧ a ≫ (f ⁻¹ᵁ W).ι = f.fiberι s ∧
      q ≫ g.fiberι (r ⟨s, hs⟩) = a ≫ p ∧
      IsIdempotentElem e₀ ∧ q.appTop e₀ = e := by
  sorry

end AlgebraicGeometry
