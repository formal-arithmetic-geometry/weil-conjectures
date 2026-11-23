/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Site axioms for actual covering presieves

## References

* Stacks Project, Sites, Definition 00VH, including the clarification after
  axiom (3).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Precoverage

/-- The precoverage `J` satisfies the axioms of a site (isomorphisms cover, covering presieves
compose via `Presieve.bind`, and covering arrows admit covering pullbacks for some choice of
fibre products). Finite covering presieves are allowed.

Stacks Project, Sites, Definition 00VH. -/
def IsSiteForCoverings {C : Type u} [Category.{v} C] (J : Precoverage C) : Prop :=
  J.HasIsos ∧
  (∀ (X : C) (R : Presieve X)
    (T : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Presieve Y),
    R ∈ J X → (∀ (Y : C) (f : Y ⟶ X) (hf : R f), T f hf ∈ J Y) →
      R.bind (fun _ _ hf ↦ T _ hf) ∈ J X) ∧
  (∀ (I : Type (max u v)) (X : C) (U : I → C) (a : ∀ i, U i ⟶ X),
    Presieve.ofArrows U a ∈ J X → ∀ (Y : C) (b : Y ⟶ X),
      ∃ (P : I → C) (p : ∀ i, P i ⟶ Y) (q : ∀ i, P i ⟶ U i),
        (∀ i, IsPullback (p i) (q i) b (a i)) ∧ Presieve.ofArrows P p ∈ J Y)

end CategoryTheory.Precoverage
