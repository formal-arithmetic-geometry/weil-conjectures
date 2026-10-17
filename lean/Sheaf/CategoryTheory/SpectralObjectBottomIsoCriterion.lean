/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Order.WithBotTop
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! The five-lemma criterion for comparison of spectral objects.
Source: Stacks Project, Tag 015K, Remark 13.21.4.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

/-- A spectral-object morphism invertible on all bottom intervals is invertible.
Source: Stacks Project, Tag 015K, Remark 13.21.4 (long exact interval sequences).
(blueprint: lem-sp-spectral-object-bottom-iso-criterion).

Proof. Fix a <= b and degree n. Use the five consecutive terms of the long exact
sequence for bottom <= a <= b:
H^n(bottom,a), H^n(bottom,b), H^n(a,b), H^(n+1)(bottom,a),
H^(n+1)(bottom,b). Naturality of the morphism gives a map between the two exact
five-term sequences. The four outside vertical maps are isomorphisms by hypothesis,
so the abelian five lemma makes the middle map invertible. Every arrow in EInt
has the displayed form, hence every component of every hom natural transformation
is invertible. These give natural isomorphisms on each H^n. The connecting-arrow
commutativity of the original morphism gives that of its componentwise inverse
by cancelling the invertible components. Assemble the inverse spectral-object
morphism; the two inverse equations follow componentwise. -/
theorem isIso_of_bottom_intervals
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : SpectralObject C EInt} (f : X ⟶ Y)
    (h : ∀ (n : ℤ) (b : EInt),
      IsIso ((f.hom n).app (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ b))))) :
    IsIso f := by
  have hc (n : ℤ) (a b : EInt) (hab : a ≤ b) :
      IsIso ((f.hom n).app (mk₁ (homOfLE hab))) := by
    let p : (⊥ : EInt) ⟶ a := homOfLE bot_le
    let q : a ⟶ b := homOfLE hab
    let r : (⊥ : EInt) ⟶ b := homOfLE bot_le
    let ψ : X.composableArrows₅ p q r (Subsingleton.elim _ _) n (n + 1) rfl ⟶
        Y.composableArrows₅ p q r (Subsingleton.elim _ _) n (n + 1) rfl :=
      homMk₅ ((f.hom n).app (mk₁ p)) ((f.hom n).app (mk₁ r))
        ((f.hom n).app (mk₁ q)) ((f.hom (n + 1)).app (mk₁ p))
        ((f.hom (n + 1)).app (mk₁ r)) ((f.hom (n + 1)).app (mk₁ q))
        ((f.hom n).naturality _) ((f.hom n).naturality _)
        (f.comm n (n + 1) rfl p q) ((f.hom (n + 1)).naturality _)
        ((f.hom (n + 1)).naturality _)
    have := h n a
    have := h n b
    have := h (n + 1) a
    have := h (n + 1) b
    exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono' (by decide : 0 + 4 ≤ 5)
      (X.composableArrows₅_exact p q r (Subsingleton.elim _ _) n (n + 1) rfl)
      (Y.composableArrows₅_exact p q r (Subsingleton.elim _ _) n (n + 1) rfl)
      ψ 0 1 2 3 4 rfl rfl rfl rfl rfl
      (by change Epi ((f.hom n).app (mk₁ p)); exact inferInstance)
      (by change IsIso ((f.hom n).app (mk₁ r)); exact h n b)
      (by change IsIso ((f.hom (n + 1)).app (mk₁ p)); exact h (n + 1) a)
      (by change Mono ((f.hom (n + 1)).app (mk₁ r)); exact inferInstance)
  have (n : ℤ) (D : ComposableArrows EInt 1) : IsIso ((f.hom n).app D) := by
    obtain ⟨a, b, g, rfl⟩ := mk₁_surjective D
    exact hc n a b (leOfHom g)
  have (n : ℤ) : IsIso (f.hom n) := NatIso.isIso_of_isIso_app _
  let e := isoMk (fun n ↦ asIso (f.hom n)) (fun n₀ n₁ hn {_ _ _} f₀ g₀ ↦
    f.comm n₀ n₁ hn f₀ g₀)
  change IsIso e.hom
  infer_instance

end CategoryTheory.Abelian.SpectralObject
