module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Logic.Relation

/-!
# Raw pure coface words and their replacements

Source: Stacks, simplicial.tex, Tags 0167(1) and 0168, the pure-coface part of the
presentation (blueprint: def-sfb-pure-coface-word).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace SimplexCategory

/-- Raw composable sequences of cofaces, including the empty sequence. The indices
are the source and target degrees; each letter raises the degree by one.
Source: Stacks, Tags 0167(1), 0168 (blueprint: def-sfb-pure-coface-word). -/
inductive CofaceWord : ℕ → ℕ → Type
  | nil (a : ℕ) : CofaceWord a a
  | snoc {a b : ℕ} (w : CofaceWord a b) (i : Fin (b + 2)) : CofaceWord a (b + 1)

namespace CofaceWord

/-- Concatenate raw coface sequences in traversal order, first `w`, then `v`.
Source: Stacks, Tag 0168 (blueprint: def-sfb-pure-coface-word). -/
def comp {a b c : ℕ} (w : CofaceWord a b) (v : CofaceWord b c) : CofaceWord a c :=
  match v with
  | .nil _ => w
  | .snoc v i => .snoc (comp w v) i

/-- Evaluate each letter as the canonical increasing injection omitting its index.
Source: Stacks, Tags 0167(1), 0168 (blueprint: def-sfb-pure-coface-word). -/
def eval {a b : ℕ} (w : CofaceWord a b) : SimplexCategory.mk a ⟶ SimplexCategory.mk b :=
  match w with
  | .nil _ => 𝟙 _
  | .snoc w i => eval w ≫ SimplexCategory.δ i

/-- One forward coface relation in an arbitrary raw prefix and suffix. There are no
codegeneracy letters or mixed moves. Put `r = n + 1` and `J = j + 1` to recover
`δ_J^(r+1) ∘ δ_i^r = δ_i^(r+1) ∘ δ_(J-1)^r` with `i < J`.
Source: Stacks, Tag 0167(1) (blueprint: def-sfb-pure-coface-word). -/
inductive Step : {a b : ℕ} → CofaceWord a b → CofaceWord a b → Prop
  | context {a n b : ℕ} (before : CofaceWord a n) (after : CofaceWord (n + 2) b)
      (i j : Fin (n + 2)) (hij : i ≤ j) :
      Step
        (comp (comp before (.snoc (.snoc (.nil n) i) j.succ)) after)
        (comp (comp before (.snoc (.snoc (.nil n) j) i.castSucc)) after)

/-- Finite transformations by the coface relation in either direction. Every
intermediate word has the same endpoints, so all its degrees lie between them.
Source: Stacks, Tags 0167(1), 0168 (blueprint: def-sfb-pure-coface-word). -/
def Related {a b : ℕ} (w v : CofaceWord a b) : Prop :=
  Relation.EqvGen Step w v

end CofaceWord
end SimplexCategory
