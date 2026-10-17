/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.PoincareDuality.Verdier
import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing

/-!
# Relative biduality for dualizable objects

Relative duality against `Ra^! 𝟙_S` has biduality on dualizable objects when that
relative dualizing complex is invertible. This is a conditional variant of the unrestricted
upstream biduality assertion; it does not assert that the hypotheses hold for an arbitrary base.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
  (a : X ⟶ S)

/-- Biduality relative to an invertible relative dualizing complex, on dualizable objects.

Source: the biduality argument of blueprint `sk-thm-sf-dual-perfect`, final proof paragraph,
implemented categorically by `MonoidalClosed.isIso_toIhomIhom_of_isDualizable`.

Proof: an invertible object `W` identifies `RHom(K,W)` with `RHom(K,𝟙) ⊗ W`.
Applying this twice identifies the double dual against `W` with the coefficient double dual.
The evaluation compatibility identifies the specified biduality map with coefficient
biduality, which is invertible for a dualizable `K`. Here `W = Ra^! 𝟙_S`, and
`verdierBiduality` and `toIhomIhom W K` are the same transpose of braided evaluation.

Edge cases: the identity orientation `W ≅ W` suffices; no smoothness or regularity of `S`
is inferred. Dualizability of `K` and invertibility of `W` are both explicit hypotheses.
(blueprint: lem-pod-relative-biduality-invertible) -/
theorem isIso_verdierBiduality_of_invertible_of_isDualizable
    (hω : IsInvertible (relativeDualizingComplex ℓ a))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hK : IsDualizable K) :
    IsIso (verdierBiduality ℓ a K) := by
  exact MonoidalClosed.isIso_toIhomIhom_of_isDualizable (Iso.refl _) hω hK

end AlgebraicGeometry.ProEtale.CondensedRing
