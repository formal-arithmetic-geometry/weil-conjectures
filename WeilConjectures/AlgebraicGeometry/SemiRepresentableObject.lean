/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject

/-!
# Semi-representable objects and hypercovers on the small étale site

Formal coproducts of étale `X`-schemes, their points, coverings, matching objects of simplicial
objects, and semi-representable hypercovers, used for refining hypercovers.
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace AlgebraicGeometry.Scheme

/-- Formal coproducts of étale `X`-schemes have finite limits. -/
noncomputable instance semiRepresentableHasFiniteLimits (X : Scheme.{u}) :
    HasFiniteLimits (FormalCoproduct.{w} X.Etale) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The `T`-valued points of a formal coproduct `L` of étale `X`-schemes: morphisms from the
representable formal coproduct on `T` to `L`. -/
abbrev semiRepresentablePoints {X : Scheme.{u}} (T : X.Etale)
    (L : FormalCoproduct.{w} X.Etale) :=
  (FormalCoproduct.incl X.Etale).obj T ⟶ L

/-- Postcomposition with a morphism `L ⟶ L'` on `T`-valued points. -/
def semiRepresentablePointsMap {X : Scheme.{u}} (T : X.Etale)
    {L L' : FormalCoproduct.{w} X.Etale} (f : L ⟶ L') :
    semiRepresentablePoints T L → semiRepresentablePoints T L' :=
  fun t => t ≫ f

/-- A morphism of formal coproducts of étale `X`-schemes is a covering if, over each component
of the target, the components of the source lying over it form an étale covering family. -/
def IsSemiRepresentableCovering {X : Scheme.{u}}
    {U V : FormalCoproduct.{w} X.Etale} (f : U ⟶ V) : Prop :=
  ∀ j : V.I,
    Sieve.ofArrows (fun i : {i : U.I // f.f i = j} => U.obj i.val)
      (fun i => f.φ i.val ≫ eqToHom (congrArg V.obj i.property)) ∈
        X.smallEtaleTopology (V.obj j)

/-- The boundary multiequalizers defining matching objects exist in formal coproducts of étale
`X`-schemes. -/
instance semiRepresentableHasMultiequalizer {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ) :
    HasMultiequalizer (SimplicialObject.matchingBoundaryIndex K n) := by
  have : Fintype (SimplicialObject.matchingBoundaryShape n).L :=
    inferInstanceAs (Fintype (Fin (n + 3)))
  have : Fintype (SimplicialObject.matchingBoundaryShape n).R :=
    inferInstanceAs (Fintype {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
  have : DecidableEq (SimplicialObject.matchingBoundaryShape n).L :=
    inferInstanceAs (DecidableEq (Fin (n + 3)))
  have : DecidableEq (SimplicialObject.matchingBoundaryShape n).R :=
    inferInstanceAs (DecidableEq {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
  infer_instance

/-- The matching object `M_n(K)` of a simplicial object in formal coproducts of étale
`X`-schemes: the terminal object for `n = 0`, `K_0 × K_0` for `n = 1`, and the boundary
multiequalizer otherwise. -/
noncomputable def semiRepresentableMatchingObject {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) :
    ℕ → FormalCoproduct.{w} X.Etale
  | 0 => (FormalCoproduct.incl X.Etale).obj (Etale.mk (𝟙 X))
  | 1 => ∏ᶜ fun _ : Fin 2 => K _⦋0⦌
  | n + 2 => multiequalizer (SimplicialObject.matchingBoundaryIndex K n)

/-- The matching map `K_n ⟶ M_n(K)` of a simplicial object in formal coproducts of étale
`X`-schemes, induced by the face maps. -/
noncomputable def semiRepresentableMatchingMap {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) :
    (n : ℕ) → K _⦋n⦌ ⟶ semiRepresentableMatchingObject K n
  | 0 => (FormalCoproduct.isTerminalIncl (Etale.mk (𝟙 X))
      ((Over.mkIdTerminal (X := X)).isTerminalOfObj (Etale.forget X) (Etale.mk (𝟙 X)))).from _
  | 1 => Pi.lift fun i : Fin 2 => K.δ i
  | n + 2 =>
      Multiequalizer.lift (SimplicialObject.matchingBoundaryIndex K n) _
        (fun i : Fin (n + 3) => K.δ i)
        (by
          rintro ⟨⟨a, b⟩, h⟩
          dsimp [SimplicialObject.matchingBoundaryIndex]
          have hb : b = (b.pred (Fin.ne_zero_of_lt h)).succ := (Fin.succ_pred _ _).symm
          have H : a.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ b.isLt)) ≤
              b.pred (Fin.ne_zero_of_lt h) := by
            rw [Fin.le_iff_val_le_val]
            have h' : a.val < b.val := h
            simp only [Fin.val_castLT, Fin.val_pred]
            omega
          have := (SimplicialObject.δ_comp_δ K H).symm
          rw [← hb] at this
          exact this)

/-- A semi-representable hypercover of `X`: a simplicial object in formal coproducts of étale
`X`-schemes whose matching maps are all coverings. -/
def IsSemiRepresentableHypercover {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) : Prop :=
  ∀ n : ℕ, IsSemiRepresentableCovering (semiRepresentableMatchingMap K n)

end AlgebraicGeometry.Scheme
