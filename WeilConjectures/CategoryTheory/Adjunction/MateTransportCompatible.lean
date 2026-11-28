/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Compatibility of a base change square with a tensor-type comparison

Let `adj₁ : N₁ ⊣ R₁` and `adj₂ : N₂ ⊣ R₂` be adjunctions with `N₁ : D₁ ⥤ D₁'` and
`N₂ : D₂ ⥤ D₂'` (think of derived extension of scalars `Ψ` and restriction of scalars `Res`), and
let `ϑᵢ : Tᵢ ⟶ Nᵢ ⋙ Rᵢ` be natural transformations from endofunctors `Tᵢ` of `Dᵢ` (think of the
identification of `Res ∘ Ψ` with the tensor product with a fixed object). For functors
`F : D₁ ⥤ D₂` and `F' : D₁' ⥤ D₂'`, a 2-cell `α : N₁ ⋙ F' ⟶ F ⋙ N₂` and a 2-cell
`a : T₁ ⋙ F ⟶ F ⋙ T₂`, we say that `α` and `a` are *transport compatible*
(`CategoryTheory.Adjunction.TransportCompatible`) if
```
F' (ϑ₁♯ X) ≫ α X = α (T₁ X) ≫ N₂ (a X) ≫ ϑ₂♯ (F X),
```
where `ϑᵢ♯ X = Nᵢ (ϑᵢ X) ≫ ε` is the transpose of `ϑᵢ X` along `Nᵢ ⊣ Rᵢ`. This is the hypothesis
of `CategoryTheory.Adjunction.map_comp_mateEquiv_app_comp_map_of_transpose`.

The predicate is stable under composition (`CategoryTheory.Adjunction.TransportCompatible.comp`),
under passing to right adjoints (`CategoryTheory.Adjunction.TransportCompatible.rightAdjoint`) and
to left adjoints (`CategoryTheory.Adjunction.TransportCompatible.leftAdjoint`) through mates, and
under replacing `Tᵢ` by isomorphic functors
(`CategoryTheory.Adjunction.TransportCompatible.of_iso`).

## Main results

- `CategoryTheory.Adjunction.TransportCompatible`: the compatibility predicate.
- `CategoryTheory.Adjunction.TransportCompatible.comp`,
  `CategoryTheory.Adjunction.TransportCompatible.rightAdjoint`,
  `CategoryTheory.Adjunction.TransportCompatible.leftAdjoint`,
  `CategoryTheory.Adjunction.TransportCompatible.of_iso`: its stability properties.
- `CategoryTheory.Adjunction.isIso_mateEquiv_symm_of_isIso_mateEquiv`: the left adjoint mate of
  a 2-cell whose other mate is invertible is invertible.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

section Transpose

variable {D D' : Type*} [Category* D] [Category* D'] {N : D ⥤ D'} {R : D' ⥤ D} (adj : N ⊣ R)
  {T : D ⥤ D} (ϑ : T ⟶ N ⋙ R)

/-- The transpose `N (T X) ⟶ N X` along `N ⊣ R` of `ϑ X : T X ⟶ R (N X)`. -/
@[simps]
def transposeNatTrans : T ⋙ N ⟶ N where
  app X := N.map (ϑ.app X) ≫ adj.counit.app (N.obj X)
  naturality X Y f := by
    have h := ϑ.naturality f
    dsimp at h ⊢
    rw [← N.map_comp_assoc, h, N.map_comp, Category.assoc, counit_naturality]
    simp only [Category.assoc]

end Transpose

section Def

variable {D₁ D₁' D₂ D₂' : Type*} [Category* D₁] [Category* D₁'] [Category* D₂] [Category* D₂']
  {N₁ : D₁ ⥤ D₁'} {R₁ : D₁' ⥤ D₁} (adj₁ : N₁ ⊣ R₁) {N₂ : D₂ ⥤ D₂'} {R₂ : D₂' ⥤ D₂}
  (adj₂ : N₂ ⊣ R₂) {T₁ : D₁ ⥤ D₁} {T₂ : D₂ ⥤ D₂} (ϑ₁ : T₁ ⟶ N₁ ⋙ R₁) (ϑ₂ : T₂ ⟶ N₂ ⋙ R₂)

/-- The 2-cells `α : N₁ ⋙ F' ⟶ F ⋙ N₂` and `a : T₁ ⋙ F ⟶ F ⋙ T₂` are *transport compatible*
with respect to `ϑᵢ : Tᵢ ⟶ Nᵢ ⋙ Rᵢ` if `F' (ϑ₁♯ X) ≫ α X = α (T₁ X) ≫ N₂ (a X ≫ ϑ₂ (F X)) ≫ ε`,
where `ϑ₁♯ X = N₁ (ϑ₁ X) ≫ ε` is the transpose of `ϑ₁ X`. -/
def TransportCompatible (F : D₁ ⥤ D₂) (F' : D₁' ⥤ D₂') (α : N₁ ⋙ F' ⟶ F ⋙ N₂)
    (a : T₁ ⋙ F ⟶ F ⋙ T₂) : Prop :=
  ∀ X, F'.map (N₁.map (ϑ₁.app X) ≫ adj₁.counit.app (N₁.obj X)) ≫ α.app X =
    α.app (T₁.obj X) ≫ N₂.map (a.app X ≫ ϑ₂.app (F.obj X)) ≫ adj₂.counit.app (N₂.obj (F.obj X))

variable {adj₁ adj₂ ϑ₁ ϑ₂}

lemma TransportCompatible.app {F : D₁ ⥤ D₂} {F' : D₁' ⥤ D₂'} {α : N₁ ⋙ F' ⟶ F ⋙ N₂}
    {a : T₁ ⋙ F ⟶ F ⋙ T₂} (h : TransportCompatible adj₁ adj₂ ϑ₁ ϑ₂ F F' α a) (X : D₁) :
    F'.map ((transposeNatTrans adj₁ ϑ₁).app X) ≫ α.app X =
      α.app (T₁.obj X) ≫ N₂.map (a.app X) ≫ (transposeNatTrans adj₂ ϑ₂).app (F.obj X) := by
  simpa using h X

lemma TransportCompatible.of_app {F : D₁ ⥤ D₂} {F' : D₁' ⥤ D₂'} {α : N₁ ⋙ F' ⟶ F ⋙ N₂}
    {a : T₁ ⋙ F ⟶ F ⋙ T₂}
    (h : ∀ X, F'.map ((transposeNatTrans adj₁ ϑ₁).app X) ≫ α.app X =
      α.app (T₁.obj X) ≫ N₂.map (a.app X) ≫ (transposeNatTrans adj₂ ϑ₂).app (F.obj X)) :
    TransportCompatible adj₁ adj₂ ϑ₁ ϑ₂ F F' α a := fun X ↦ by
  simpa using h X

end Def

section Comp

variable {D₁ D₁' D₂ D₂' D₃ D₃' : Type*} [Category* D₁] [Category* D₁'] [Category* D₂]
  [Category* D₂'] [Category* D₃] [Category* D₃']
  {N₁ : D₁ ⥤ D₁'} {R₁ : D₁' ⥤ D₁} {adj₁ : N₁ ⊣ R₁} {N₂ : D₂ ⥤ D₂'} {R₂ : D₂' ⥤ D₂}
  {adj₂ : N₂ ⊣ R₂} {N₃ : D₃ ⥤ D₃'} {R₃ : D₃' ⥤ D₃} {adj₃ : N₃ ⊣ R₃}
  {T₁ : D₁ ⥤ D₁} {T₂ : D₂ ⥤ D₂} {T₃ : D₃ ⥤ D₃} {ϑ₁ : T₁ ⟶ N₁ ⋙ R₁} {ϑ₂ : T₂ ⟶ N₂ ⋙ R₂}
  {ϑ₃ : T₃ ⟶ N₃ ⋙ R₃}

/-- **Transport compatibility of a composite.** If `(α, a)` is compatible for `F` and `(β, b)`
for `G`, then the pasted 2-cells are compatible for `F ⋙ G`. -/
lemma TransportCompatible.comp {F : D₁ ⥤ D₂} {F' : D₁' ⥤ D₂'} {G : D₂ ⥤ D₃} {G' : D₂' ⥤ D₃'}
    {α : N₁ ⋙ F' ⟶ F ⋙ N₂} {a : T₁ ⋙ F ⟶ F ⋙ T₂} {β : N₂ ⋙ G' ⟶ G ⋙ N₃}
    {b : T₂ ⋙ G ⟶ G ⋙ T₃} (h₁ : TransportCompatible adj₁ adj₂ ϑ₁ ϑ₂ F F' α a)
    (h₂ : TransportCompatible adj₂ adj₃ ϑ₂ ϑ₃ G G' β b)
    {γ : N₁ ⋙ F' ⋙ G' ⟶ (F ⋙ G) ⋙ N₃} {c : T₁ ⋙ F ⋙ G ⟶ (F ⋙ G) ⋙ T₃}
    (hγ : ∀ X, γ.app X = G'.map (α.app X) ≫ β.app (F.obj X))
    (hc : ∀ X, c.app X = G.map (a.app X) ≫ b.app (F.obj X)) :
    TransportCompatible adj₁ adj₃ ϑ₁ ϑ₃ (F ⋙ G) (F' ⋙ G') γ c := by
  refine TransportCompatible.of_app fun X ↦ ?_
  have e₁ := congrArg G'.map (h₁.app X)
  have e₂ := h₂.app (F.obj X)
  have e₃ := β.naturality (a.app X)
  dsimp at e₂ e₃ ⊢
  rw [hγ, hγ, hc, ← Functor.map_comp_assoc, e₁]
  simp only [Functor.map_comp, Category.assoc]
  rw [e₂, reassoc_of% e₃]

end Comp

section RightAdjoint

variable {D₁ D₁' D₂ D₂' : Type*} [Category* D₁] [Category* D₁'] [Category* D₂] [Category* D₂']
  {N₁ : D₁ ⥤ D₁'} {R₁ : D₁' ⥤ D₁} {adj₁ : N₁ ⊣ R₁} {N₂ : D₂ ⥤ D₂'} {R₂ : D₂' ⥤ D₂}
  {adj₂ : N₂ ⊣ R₂} {T₁ : D₁ ⥤ D₁} {T₂ : D₂ ⥤ D₂} {ϑ₁ : T₁ ⟶ N₁ ⋙ R₁} {ϑ₂ : T₂ ⟶ N₂ ⋙ R₂}
  {G : D₁ ⥤ D₂} {F : D₂ ⥤ D₁} (adj : G ⊣ F) {G' : D₁' ⥤ D₂'} {F' : D₂' ⥤ D₁'} (adj' : G' ⊣ F')
  {α : N₁ ⋙ G' ⟶ G ⋙ N₂} {a : T₁ ⋙ G ⟶ G ⋙ T₂}

/-- **Transport compatibility of mates, inverse-free form.** If `(α, a)` is compatible for the
left adjoint `G`, then the mates `β : F ⋙ N₁ ⟶ N₂ ⋙ F'` of `α` and `p : F ⋙ T₁ ⟶ T₂ ⋙ F` of `a`
satisfy `N₁ (p M) ≫ β (T₂ M) ≫ F' (ϑ₂♯ M) = ϑ₁♯ (F M) ≫ β M`. -/
lemma TransportCompatible.map_mateEquiv_comp_mateEquiv
    (h : TransportCompatible adj₁ adj₂ ϑ₁ ϑ₂ G G' α a) (M : D₂) :
    N₁.map ((mateEquiv adj adj a).app M) ≫ (mateEquiv adj adj' α).app (T₂.obj M) ≫
        F'.map ((transposeNatTrans adj₂ ϑ₂).app M) =
      (transposeNatTrans adj₁ ϑ₁).app (F.obj M) ≫ (mateEquiv adj adj' α).app M := by
  apply (adj'.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc]
  have hβ₁ := mateEquiv_counit adj adj' α M
  have hβ₂ := mateEquiv_counit adj adj' α (T₂.obj M)
  have hp := mateEquiv_counit adj adj a M
  have hc := h.app (F.obj M)
  have hn₁ := (transposeNatTrans adj₂ ϑ₂).naturality (adj.counit.app M)
  have hn₂ := α.naturality ((mateEquiv adj adj a).app M)
  dsimp at hβ₁ hβ₂ hp hc hn₁ hn₂ ⊢
  rw [counit_naturality, reassoc_of% hβ₂, hβ₁, reassoc_of% hc,
    ← hn₁, reassoc_of% hn₂, ← N₂.map_comp_assoc, hp, N₂.map_comp, Category.assoc]

/-- **Transport compatibility passes to right adjoints.** If `(α, a)` is compatible for the left
adjoint `G` and the mates `β` of `α` and `p` of `a` are invertible, then `(β⁻¹, p⁻¹)` is
compatible for the right adjoint `F`. -/
lemma TransportCompatible.rightAdjoint (h : TransportCompatible adj₁ adj₂ ϑ₁ ϑ₂ G G' α a)
    [IsIso (mateEquiv adj adj' α)] [IsIso (mateEquiv adj adj a)] :
    TransportCompatible adj₂ adj₁ ϑ₂ ϑ₁ F F' (inv (mateEquiv adj adj' α))
      (inv (mateEquiv adj adj a)) := by
  refine TransportCompatible.of_app fun M ↦ ?_
  have e := h.map_mateEquiv_comp_mateEquiv adj adj' M
  simp only [NatIso.isIso_inv_app]
  rw [← cancel_epi ((mateEquiv adj adj' α).app (T₂.obj M)), IsIso.hom_inv_id_assoc,
    ← cancel_epi (N₁.map ((mateEquiv adj adj a).app M)), reassoc_of% e, IsIso.hom_inv_id,
    Category.comp_id, ← N₁.map_comp_assoc, IsIso.hom_inv_id, N₁.map_id, Category.id_comp]

end RightAdjoint

section LeftAdjoint

variable {D₁ D₁' D₂ D₂' : Type*} [Category* D₁] [Category* D₁'] [Category* D₂] [Category* D₂']
  {N₁ : D₁ ⥤ D₁'} {R₁ : D₁' ⥤ D₁} {adj₁ : N₁ ⊣ R₁} {N₂ : D₂ ⥤ D₂'} {R₂ : D₂' ⥤ D₂}
  {adj₂ : N₂ ⊣ R₂} {T₁ : D₁ ⥤ D₁} {T₂ : D₂ ⥤ D₂} {ϑ₁ : T₁ ⟶ N₁ ⋙ R₁} {ϑ₂ : T₂ ⟶ N₂ ⋙ R₂}
  {F : D₂ ⥤ D₁} {G : D₁ ⥤ D₂} (adj : F ⊣ G) {F' : D₂' ⥤ D₁'} {G' : D₁' ⥤ D₂'} (adj' : F' ⊣ G')
  {α : N₁ ⋙ G' ⟶ G ⋙ N₂} {a : T₁ ⋙ G ⟶ G ⋙ T₂}

/-- **Transport compatibility passes to left adjoints.** If `(α, a)` is compatible for the right
adjoint `G` and both are invertible, then the left adjoint mates of `α⁻¹` and `a⁻¹` are
compatible for the left adjoint `F`. -/
lemma TransportCompatible.leftAdjoint (h : TransportCompatible adj₁ adj₂ ϑ₁ ϑ₂ G G' α a)
    [IsIso α] [IsIso a] :
    TransportCompatible adj₂ adj₁ ϑ₂ ϑ₁ F F' ((mateEquiv adj adj').symm (inv α))
      ((mateEquiv adj adj).symm (inv a)) := by
  refine TransportCompatible.of_app fun X ↦ ?_
  apply (adj'.homEquiv _ _).injective
  rw [← cancel_mono (α.app (F.obj X))]
  simp only [homEquiv_unit, Functor.map_comp, Category.assoc]
  have hα₁ := unit_mateEquiv_symm adj adj' (inv α) X
  have hα₂ := unit_mateEquiv_symm adj adj' (inv α) (T₂.obj X)
  have ha := unit_mateEquiv_symm adj adj (inv a) X
  have hc := h.app (F.obj X)
  have hn₁ := (transposeNatTrans adj₂ ϑ₂).naturality (adj.unit.app X)
  have hn₂ := α.naturality (((mateEquiv adj adj).symm (inv a)).app X)
  have hn₃ := adj'.unit.naturality ((transposeNatTrans adj₂ ϑ₂).app X)
  simp only [NatIso.isIso_inv_app] at hα₁ hα₂ ha
  dsimp at hα₁ hα₂ ha hc hn₁ hn₂ hn₃ ⊢
  rw [← reassoc_of% hn₃, ← reassoc_of% hα₁, IsIso.inv_hom_id, Category.comp_id,
    ← reassoc_of% hα₂, hc, reassoc_of% hn₂, IsIso.inv_hom_id_assoc, ← N₂.map_comp_assoc, ← ha,
    N₂.map_comp, Category.assoc, ← N₂.map_comp_assoc (inv _), IsIso.inv_hom_id, N₂.map_id,
    Category.id_comp, hn₁]

end LeftAdjoint

section OfIso

variable {D₁ D₁' D₂ D₂' : Type*} [Category* D₁] [Category* D₁'] [Category* D₂] [Category* D₂']
  {N₁ : D₁ ⥤ D₁'} {R₁ : D₁' ⥤ D₁} {adj₁ : N₁ ⊣ R₁} {N₂ : D₂ ⥤ D₂'} {R₂ : D₂' ⥤ D₂}
  {adj₂ : N₂ ⊣ R₂} {T₁ T₁' : D₁ ⥤ D₁} {T₂ T₂' : D₂ ⥤ D₂} {ϑ₁ : T₁ ⟶ N₁ ⋙ R₁}
  {ϑ₂ : T₂ ⟶ N₂ ⋙ R₂}

/-- **Changing the endofunctors.** If `(α, a)` is compatible with respect to `ϑᵢ : Tᵢ ⟶ Nᵢ ⋙ Rᵢ`
and `a' : T₁' ⋙ F ⟶ F ⋙ T₂'` corresponds to `a` through `eᵢ : Tᵢ' ⟶ Tᵢ`, then `(α, a')` is
compatible with respect to `eᵢ ≫ ϑᵢ`. -/
lemma TransportCompatible.of_hom (e₁ : T₁' ⟶ T₁) (e₂ : T₂' ⟶ T₂) {F : D₁ ⥤ D₂}
    {F' : D₁' ⥤ D₂'} {α : N₁ ⋙ F' ⟶ F ⋙ N₂} {a : T₁ ⋙ F ⟶ F ⋙ T₂}
    (h : TransportCompatible adj₁ adj₂ ϑ₁ ϑ₂ F F' α a) {a' : T₁' ⋙ F ⟶ F ⋙ T₂'}
    (ha : ∀ X, a'.app X ≫ e₂.app (F.obj X) = F.map (e₁.app X) ≫ a.app X) :
    TransportCompatible adj₁ adj₂ (e₁ ≫ ϑ₁) (e₂ ≫ ϑ₂) F F' α a' := fun X ↦ by
  have e := h X
  have hn := α.naturality (e₁.app X)
  have ha' := congrArg N₂.map (ha X)
  simp only [Functor.map_comp, Category.assoc] at e ha'
  dsimp at hn ⊢
  simp only [Functor.map_comp, Category.assoc]
  rw [e, reassoc_of% hn, ← reassoc_of% ha']

end OfIso

section Iterated

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D}
  {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)

/-- The left adjoint mate `F₁ ⋙ L₂ ⟶ L₁ ⋙ F₂` of `β : R₁ ⋙ F₂ ⟶ F₁ ⋙ R₂` is an isomorphism as
soon as the other mate `U₂ ⋙ R₁ ⟶ R₂ ⋙ U₁` of `β` is: the iterated mate is a conjugate
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`). -/
lemma isIso_mateEquiv_symm_of_isIso_mateEquiv (β : TwoSquare R₁ F₂ F₁ R₂)
    [IsIso (mateEquiv adj₄ adj₃ β)] : IsIso ((mateEquiv adj₁ adj₂).symm β) := by
  have e := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ ((mateEquiv adj₁ adj₂).symm β)
  rw [Equiv.apply_symm_apply] at e
  have : IsIso (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)
      ((mateEquiv adj₁ adj₂).symm β)) := by
    rw [← e]
    infer_instance
  exact conjugateEquiv_of_iso (adj₁.comp adj₄) (adj₃.comp adj₂) _

end Iterated

end CategoryTheory.Adjunction
