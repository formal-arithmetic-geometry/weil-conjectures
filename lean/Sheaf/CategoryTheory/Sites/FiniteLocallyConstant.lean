module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Finite locally constant set objects in a finite-cover topos

Source: literature/stacks-project/sites-modules.tex, Section 093P, Definition 093Q
(blueprint: def-trf-finite-locally-constant-set-sheaf).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An object is finite locally constant when a finite epimorphic family over the
terminal object trivializes its pullbacks to finite constant objects in the slices.
Source: Stacks Project, Sites, Section 093P, Definition 093Q
(blueprint: def-trf-finite-locally-constant-set-sheaf). -/
def IsFiniteLocallyConstant {E : Type u} [Category.{v} E]
    [HasCoproducts E] [HasFiniteLimits E] (F : E) : Prop :=
  ∃ (n : ℕ) (U : Fin n → E) (u : ∀ i, U i ⟶ ⊤_ E),
    Epi (Sigma.desc u) ∧
      ∀ i, ∃ (P : E) (p : P ⟶ F) (q : P ⟶ U i),
        IsPullback p q (terminal.from F) (u i) ∧
          ∃ (m : ℕ), Nonempty
            (Over.mk q ≅ Over.mk (Sigma.desc (fun _ : Fin m => 𝟙 (U i))))

end CategoryTheory
