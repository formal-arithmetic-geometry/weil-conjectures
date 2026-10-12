module

public import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.CategoryTheory.Filtered.Final
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit

@[expose] public section

universe uI vI uJ vJ uC vC

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

/-! # Essential constancy under initial restriction

Source: Stacks Project, Categories, Lemma Tag 0A1T (lemma-initial-essentially-constant),
the pro form of Lemma Tag 0A1S (blueprint: lem-pur-essential-constant-cofinal-0a1s).
-/

/-- Let `H : I ⥤ J` be an initial functor (Mathlib's `Functor.Initial`: every comma category
`CostructuredArrow H j` is nonempty and connected, Stacks' initial) between cofiltered
categories and `M : J ⥤ C`. Then `M` is essentially constant with value `X` as a pro-object
iff `H ⋙ M` is, with the same value. More precisely, if `u : X ⟶ M` is a cone exhibiting `M`
as essentially constant (an index `j₀`, a retraction `r` of `u.app j₀`, and the common-stage
clause of `IsEssentiallyConstantProDiagram`), then the restricted cone `H.whiskerLeft u`,
with components `u.app (H.obj i)`, exhibits `H ⋙ M` as essentially constant; and if `v`
exhibits `H ⋙ M` as essentially constant, there is a cone `u` exhibiting `M` as essentially
constant with `H.whiskerLeft u = v`, i.e. `u.app (H.obj i) = v.app i` for all `i`.

Proof (in words). Step 1: for every `W`, apply the limit criterion for initial functors to
`j ↦ Hom(M j, W)` in `Setᵒᵖ`; the comparison `κ_W : colim_i Hom(M(H i), W) →
colim_j Hom(M j, W)`, `[ψ]_i ↦ [ψ]_{H i}`, is bijective. Step 2: if `M` is essentially
constant with cone `u`, `[ψ]_j ↦ ψ ∘ u_j` is bijective (Hom-colimit lemma), so is
`β_W : [ψ]_i ↦ ψ ∘ u_{H i}`; with `[r']_{i₀} = β_X⁻¹(id_X)` the criterion 05PY gives that
`H ⋙ M` is essentially constant with cone maps `u'_i`, and applying `β` shows
`u'_i = u_{H i}`. Step 3: conversely, if `H ⋙ M` is essentially constant with cone `v`,
`γ_W : [ψ]_i ↦ ψ ∘ v_i` is bijective; with `[r]_{i₀} = γ_X⁻¹(id_X)` and `κ_W`,
`φ ↦ [φ ∘ r]_{H i₀}` is bijective, and 05PY gives `M` essentially constant with cone `u`.
Step 4: injectivity of `κ_W` and `r ∘ v_{i₀} = id` give `u_{H i} = v_i`.

Source: Stacks Project, Categories, Lemma Tag 0A1T
(blueprint: lem-pur-essential-constant-cofinal-0a1s). -/
theorem initial_iff_essentiallyConstantProDiagram
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsCofiltered I] [IsCofiltered J]
    (H : I ⥤ J) [H.Initial] (M : J ⥤ C) (X : C) :
    (IsEssentiallyConstantProDiagram M X ↔
      IsEssentiallyConstantProDiagram (H ⋙ M) X) ∧
    (∀ u : (Functor.const J).obj X ⟶ M,
      (∃ j₀ : J, ∃ r : M.obj j₀ ⟶ X, u.app j₀ ≫ r = 𝟙 X ∧
        ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
          M.map b = M.map a ≫ r ≫ u.app j) →
      ∃ i₀ : I, ∃ r : M.obj (H.obj i₀) ⟶ X, u.app (H.obj i₀) ≫ r = 𝟙 X ∧
        ∀ i : I, ∃ k : I, ∃ a : k ⟶ i₀, ∃ b : k ⟶ i,
          M.map (H.map b) = M.map (H.map a) ≫ r ≫ u.app (H.obj i)) ∧
    (∀ v : (Functor.const I).obj X ⟶ H ⋙ M,
      (∃ i₀ : I, ∃ r : M.obj (H.obj i₀) ⟶ X, v.app i₀ ≫ r = 𝟙 X ∧
        ∀ i : I, ∃ k : I, ∃ a : k ⟶ i₀, ∃ b : k ⟶ i,
          M.map (H.map b) = M.map (H.map a) ≫ r ≫ v.app i) →
      ∃ u : (Functor.const J).obj X ⟶ M,
        (∃ j₀ : J, ∃ r : M.obj j₀ ⟶ X, u.app j₀ ≫ r = 𝟙 X ∧
          ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
            M.map b = M.map a ≫ r ≫ u.app j) ∧
        ∀ i : I, u.app (H.obj i) = v.app i) := by
  sorry

end CategoryTheory
