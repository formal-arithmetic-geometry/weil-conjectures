module

public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # Evaluate an essentially constant pro-cone at an initial stage

Source: Stacks Project, Categories, Tag 05PU(2)(a)-(b), explicit inverse calculation
for a specified cone (blueprint: lem-trf-essential-pro-initial-evaluation).
-/

@[expose] public section

set_option autoImplicit false

universe uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Every specified cone and retraction/factorization witness for an essentially
constant pro-diagram gives an invertible cone leg at an initial object. Its inverse
is the initial transition to the witness stage followed by the specified retraction.

Source: Stacks Project, Categories, Tag 05PU(2)(a)-(b); an elementary consequence
for a specified cone, rather than a verbatim Stacks lemma
(blueprint: lem-trf-essential-pro-initial-evaluation).

Proof:
1. Naturality of the specified cone from def-pc-essentially-constant-pro-diagram
gives u_i followed by G(iota_j) equal to u_j. For j = j₀, postcompose with r and
use the given retraction identity. Thus u_i followed by w is the identity of X,
where w is G(iota_j₀) followed by r.
2. Apply the common-stage clause at j = i. Obtain a : k → j₀ and b : k → i
with G(b) = G(a) followed by r and u_i. Put c = iota_k : i → k.
Initiality gives c followed by b equal to the identity of i and c followed by a
equal to iota_j₀. Precompose the factorization with G(c) and use functoriality.
This gives w followed by u_i equal to the identity of G(i).
3. These two identities give invertibility with the displayed inverse. The formula
for every u_j was obtained in Step 1. The cone and the witness were arbitrary,
so the calculation applies to every specified cone and every witness. -/
theorem essentiallyConstantPro_initial_evaluation
    {J : Type uJ} {C : Type uC} [Category.{vJ} J] [Category.{vC} C]
    (G : J ⥤ C) (X : C) (i : J) (hi : IsInitial i)
    (h : IsEssentiallyConstantProDiagram G X) :
    ∀ (u : (Functor.const J).obj X ⟶ G) (j₀ : J) (r : G.obj j₀ ⟶ X),
      u.app j₀ ≫ r = 𝟙 X →
      (∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
        G.map b = G.map a ≫ r ≫ u.app j) →
      IsIso (u.app i) ∧
        u.app i ≫ (G.map (hi.to j₀) ≫ r) = 𝟙 X ∧
        (G.map (hi.to j₀) ≫ r) ≫ u.app i = 𝟙 (G.obj i) ∧
        ∀ j : J, u.app j = u.app i ≫ G.map (hi.to j) := by
  sorry

end CategoryTheory
