module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Logic.Relation

/-!
# Raw pure codegeneracy words and their replacements

Source: Stacks, simplicial.tex, Tags 0167(5) and 0168, the pure-codegeneracy part of
the presentation (blueprint: def-sfb-pure-codegeneracy-word).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace SimplexCategory

/-- Raw composable sequences of codegeneracies, including the empty sequence.
The indices are source and target degrees; each letter lowers the degree by one.
Source: Stacks, Tags 0167(5), 0168 (blueprint: def-sfb-pure-codegeneracy-word). -/
inductive CodegeneracyWord : ℕ → ℕ → Type
  | nil (a : ℕ) : CodegeneracyWord a a
  | snoc {a b : ℕ} (w : CodegeneracyWord a (b + 1)) (i : Fin (b + 1)) :
      CodegeneracyWord a b

namespace CodegeneracyWord

/-- Concatenate raw codegeneracy sequences in traversal order, first `w`, then `v`.
Source: Stacks, Tag 0168 (blueprint: def-sfb-pure-codegeneracy-word). -/
def comp {a b c : ℕ} (w : CodegeneracyWord a b) (v : CodegeneracyWord b c) :
    CodegeneracyWord a c :=
  match v with
  | .nil _ => w
  | .snoc v i => .snoc (comp w v) i

/-- Evaluate each letter as the canonical nondecreasing adjacent collapse.
Source: Stacks, Tags 0167(5), 0168 (blueprint: def-sfb-pure-codegeneracy-word). -/
def eval {a b : ℕ} (w : CodegeneracyWord a b) :
    SimplexCategory.mk a ⟶ SimplexCategory.mk b :=
  match w with
  | .nil _ => 𝟙 _
  | .snoc w i => eval w ≫ SimplexCategory.σ i

/-- One forward codegeneracy relation in any raw prefix and suffix:
`σ_j^n ∘ σ_i^(n+1)` is replaced by `σ_i^n ∘ σ_(j+1)^(n+1)` for `i ≤ j ≤ n`.
No coface letters or mixed moves are available.
Source: Stacks, Tag 0167(5) (blueprint: def-sfb-pure-codegeneracy-word). -/
inductive Step : {a b : ℕ} → CodegeneracyWord a b → CodegeneracyWord a b → Prop
  | context {a n b : ℕ} (before : CodegeneracyWord a (n + 2))
      (after : CodegeneracyWord n b) (i j : Fin (n + 1)) (hij : i ≤ j) :
      Step
        (comp (comp before (.snoc (.snoc (.nil (n + 2)) i.castSucc) j)) after)
        (comp (comp before (.snoc (.snoc (.nil (n + 2)) j.succ) i)) after)

/-- Finite transformations using the codegeneracy relation in either direction,
including zero steps. All words have the same endpoints and only lower degrees,
so every intermediate ordinal lies between those endpoints.
Source: Stacks, Tags 0167(5), 0168 (blueprint: def-sfb-pure-codegeneracy-word). -/
def Related {a b : ℕ} (w v : CodegeneracyWord a b) : Prop :=
  Relation.EqvGen Step w v

end CodegeneracyWord
end SimplexCategory
