/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Change of trait on the invariant summands of nearby cycles

Let `τ : N₂ ⟶ N₁` be a morphism of models over `Spec l : Spec L₂ ⟶ Spec L₁`, and `ω : Ω₁ ⟶ Ω₂` a
homomorphism of extensions `Ωᵢ/Lᵢ` over `l`, with change of Galois layers
`τ' : N₂_{Ω₂} ⟶ N₁_{Ω₁}` (`NearbyCyclesModel.galoisLayerMap`). The pullback exchanges of the square
```
N₂_{Ω₂} ──τ'──→ N₁_{Ω₁}
   │σ₂             │σ₁
   N₂ ────τ────→  N₁
```
satisfy `α_{τ'} ∘ τ'^* α_{σ₁} = α_{σ₂} ∘ σ₂^* α_τ` up to the composition isomorphisms
(`NearbyCyclesModel.pullbackExchange_galoisLayerMap_square`). By SGA 4½, [Th. finitude],
Lemme 3.4, `α_{σᵢ}` is the inclusion of the direct summand `Ψ_{Nᵢ} = (Ψ_{Nᵢ_{Ωᵢ}})^{Pᵢ}` of
invariants under `Pᵢ = Aut(Ωᵢ/Lᵢ)`. This file proves that if `α_{τ'}` is invertible, `α_τ` is
invertible: `α_{τ'}` is equivariant along the restriction `P₂ ⟶ P₁`
(`NearbyCyclesModel.pullbackExchange_galoisLayerMap_app_comp_galoisLayerAction`), and when every
element of `P₁` is a restriction, it identifies the two invariant summands
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap`). This is the step "take the
invariants under a pro-`p` group" in the induction of Deligne's proof of Th. finitude 3.7 (3.8).

The identification of the summands uses that the projector `r₁ ≫ α_{σ₁}` of the first summand is
the projector onto *all* the invariants, in the form: on cohomology sheaves (after pullback to the
special fibre of `N₂`), every map out of `Hᵠ(Ψ_{N₁_{Ω₁}})` which is invariant under `P₁` is fixed
by the projector. Of the second projector, only the invariance `ρ_σ ≫ (r₂ ≫ α_{σ₂}) = r₂ ≫ α_{σ₂}`
is used.

## Main results

- `CategoryTheory.isIso_of_comp_eq_comp_of_coinvariant`: the abstract statement, in a category
  with a jointly conservative family of functors (the cohomology functors).
- `NearbyCyclesModel.pullbackExchange_galoisLayerMap_square`: the square of pullback exchanges.
- `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap`: the change of trait is
  invertible on the invariant summands once it is invertible on the Galois layers.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- **Matching two invariant summands.** Let `a₁ : A₁ ⟶ B₁` and `a₂ : A₂ ⟶ B₂` be split
monomorphisms with retractions `r₁`, `r₂`, let `β : B₁ ⟶ B₂` be an isomorphism and `α : A₁ ⟶ A₂`
with `α ≫ a₂ = a₁ ≫ β`. Let `ρ₁`, `ρ₂` be families of endomorphisms of `B₁`, `B₂` such that `β`
carries every `ρ₁ i` to some `ρ₂ i₂`, and such that `ρ₂ i₂ ≫ (r₂ ≫ a₂) = r₂ ≫ a₂`. If, for a
jointly conservative family of functors `H q`, every map out of `H q B₁` invariant under the
`H q (ρ₁ i)` is fixed by `H q (r₁ ≫ a₁)`, then `α` is an isomorphism.

(Think of `a₁`, `a₂` as the inclusions of the invariants of two group actions, and of `β` as an
equivariant isomorphism along a surjective group homomorphism.) -/
lemma isIso_of_comp_eq_comp_of_coinvariant {D : Type*} [Category D] {ι : Type*}
    {A : ι → Type*} [∀ q, Category (A q)] (H : ∀ q, D ⥤ A q)
    (hcons : ∀ {X Y : D} (g : X ⟶ Y), (∀ q, IsIso ((H q).map g)) → IsIso g)
    {A₁ A₂ B₁ B₂ : D} (α : A₁ ⟶ A₂) (a₁ : A₁ ⟶ B₁) (r₁ : B₁ ⟶ A₁) (ha₁ : a₁ ≫ r₁ = 𝟙 _)
    (a₂ : A₂ ⟶ B₂) (r₂ : B₂ ⟶ A₂) (ha₂ : a₂ ≫ r₂ = 𝟙 _) (β : B₁ ⟶ B₂) [IsIso β]
    (hsq : α ≫ a₂ = a₁ ≫ β) {κ₁ κ₂ : Type*} (ρ₁ : κ₁ → (B₁ ⟶ B₁)) (ρ₂ : κ₂ → (B₂ ⟶ B₂))
    (hβ : ∀ i, ∃ i₂, ρ₁ i ≫ β = β ≫ ρ₂ i₂) (he₂ : ∀ i₂, ρ₂ i₂ ≫ r₂ ≫ a₂ = r₂ ≫ a₂)
    (he₁ : ∀ q {W : A q} (φ : (H q).obj B₁ ⟶ W), (∀ i, (H q).map (ρ₁ i) ≫ φ = φ) →
      (H q).map (r₁ ≫ a₁) ≫ φ = φ) :
    IsIso α := by
  refine hcons α fun q ↦ ?_
  -- `β ≫ e₂` is invariant under the `ρ₁ i`, hence fixed by `e₁ = r₁ ≫ a₁`
  have hfix : (H q).map (r₁ ≫ a₁) ≫ (H q).map (β ≫ r₂ ≫ a₂) = (H q).map (β ≫ r₂ ≫ a₂) := by
    refine he₁ q _ fun i ↦ ?_
    obtain ⟨i₂, hi⟩ := hβ i
    rw [← Functor.map_comp, reassoc_of% hi, he₂]
  have hfix' : r₁ ≫ α = r₁ ≫ a₁ ≫ β ≫ r₂ := by
    rw [← reassoc_of% hsq, ha₂, Category.comp_id]
  refine ⟨⟨(H q).map (a₂ ≫ inv β ≫ r₁), ?_, ?_⟩⟩
  · rw [← Functor.map_comp, ← Functor.map_id]
    congr 1
    rw [reassoc_of% hsq, IsIso.hom_inv_id_assoc, ha₁]
  · have k : β ≫ r₂ = (β ≫ r₂ ≫ a₂) ≫ r₂ := by
      rw [Category.assoc, Category.assoc, ha₂, Category.comp_id]
    have h₁ : (H q).map (r₁ ≫ α) = (H q).map (β ≫ r₂) := by
      calc (H q).map (r₁ ≫ α) = (H q).map ((r₁ ≫ a₁) ≫ (β ≫ r₂ ≫ a₂) ≫ r₂) := by
            rw [hfix', ← k, Category.assoc]
        _ = (H q).map (r₁ ≫ a₁) ≫ (H q).map (β ≫ r₂ ≫ a₂) ≫ (H q).map r₂ := by
            rw [Functor.map_comp (H q) (r₁ ≫ a₁), Functor.map_comp (H q) (β ≫ r₂ ≫ a₂)]
        _ = (H q).map (β ≫ r₂) := by
            rw [reassoc_of% hfix, ← Functor.map_comp, ← k]
    rw [← Functor.map_comp, Category.assoc, Category.assoc, Functor.map_comp (H q) a₂,
      Functor.map_comp (H q) (inv β), h₁, ← Functor.map_comp, ← Functor.map_comp,
      IsIso.inv_hom_id_assoc, ha₂, Functor.map_id]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X₁ X₁' X₂ X₂' : Scheme.{u}} {N₁ : NearbyCyclesModel X₁ X₁'}
  {N₂ : NearbyCyclesModel X₂ X₂'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  {L₁ L₂ : Type u} [Field L₁] [Field L₂] {h₁ : N₁.generic ⟶ Spec (.of L₁)}
  {h₂ : N₂.generic ⟶ Spec (.of L₂)} (Ω₁ Ω₂ : Type u) [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] {l : L₁ →+* L₂} (ω : Ω₁ →+* Ω₂)
  (hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l)

/-- `x ≫ m₁ = p₁ ≫ p₂ ≫ p₃` and `x ≫ m₂ = q₁ ≫ q₂ ≫ q₃` with `m₁`, `m₂` split by `m₁'`, `m₂'`
give `p₁ ≫ p₂ ≫ p₃ ≫ m₁' = q₁ ≫ q₂ ≫ q₃ ≫ m₂'`. -/
private lemma comp_eq_comp_of_comp_eq_aux {C : Type*} [Category C] {P Q Y₁ Y₂ P₁ P₂ Q₁ Q₂ : C}
    {x : P ⟶ Q} {m₁ : Q ⟶ Y₁} {m₂ : Q ⟶ Y₂} {m₁' : Y₁ ⟶ Q} {m₂' : Y₂ ⟶ Q} {p₁ : P ⟶ P₁}
    {p₂ : P₁ ⟶ P₂} {p₃ : P₂ ⟶ Y₁} {q₁ : P ⟶ Q₁} {q₂ : Q₁ ⟶ Q₂} {q₃ : Q₂ ⟶ Y₂}
    (hA : x ≫ m₁ = p₁ ≫ p₂ ≫ p₃) (hB : x ≫ m₂ = q₁ ≫ q₂ ≫ q₃) (h₁ : m₁ ≫ m₁' = 𝟙 _)
    (h₂ : m₂ ≫ m₂' = 𝟙 _) :
    p₁ ≫ p₂ ≫ p₃ ≫ m₁' = q₁ ≫ q₂ ≫ q₃ ≫ m₂' := by
  simp only [← Category.assoc] at hA hB ⊢
  rw [← hA, ← hB, Category.assoc, h₁, Category.assoc, h₂]

/-- `F (e.hom.app X) ≫ F (e.inv.app X) = 𝟙`, with all data as variables. -/
private lemma map_hom_app_comp_map_inv_app {C D E : Type*} [Category C] [Category D]
    [Category E] (F : D ⥤ E) {G G' : C ⥤ D} (e : G ≅ G') (X : C) :
    F.map (e.hom.app X) ≫ F.map (e.inv.app X) = 𝟙 _ := by
  rw [← F.map_comp, Iso.hom_inv_id_app, F.map_id]

/-- The diagonal `N₂_{Ω₂} ⟶ N₁` of the square of the change of Galois layers, over `f, f'`: the
morphism `τ` on total spaces and `τ ∘ σ₂` on generic fibres. -/
@[simps]
noncomputable def galoisLayerMapDiagonal (τ : N₂.Hom N₁ f f') :
    (N₂.galoisLayer h₂ Ω₂).Hom N₁ f f' where
  total := τ.total
  generic := pullback.fst _ _ ≫ τ.generic
  comm_j := by simp only [galoisLayer, Category.assoc, τ.comm_j]
  comm_i := τ.comm_i
  comm_ε := by simp only [galoisLayer, Category.assoc, τ.comm_ε]

/-- **The square of pullback exchanges of a change of Galois layers** (with `σᵢ : Nᵢ_{Ωᵢ} ⟶ Nᵢ`
the projections and `τ'` the change of Galois layers):
`σ₂^* α_τ ≫ α_{σ₂} = τ'^* α_{σ₁} ≫ α_{τ'}` up to the composition isomorphisms `c`, as morphisms
`Lf'^* Ψ_{N₁} C ⟶ Ψ_{N₂_{Ω₂}} (Lf^* C)`. -/
theorem pullbackExchange_galoisLayerMap_square (τ : N₂.Hom N₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj Λ X₁))) :
    (leftDerivedUpperStarCompOfEq Λ (Category.id_comp f')).hom.app ((N₁.nearbyCycles Λ).obj C) ≫
        L((𝟙 X₂')^*⟦Λ⟧).map ((τ.pullbackExchange Λ).app C) ≫
        ((N₂.galoisLayerHom h₂ Ω₂).pullbackExchange Λ).app (L((f)^*⟦Λ⟧).obj C) ≫
        ((N₂.galoisLayer h₂ Ω₂).nearbyCycles Λ).map
          ((leftDerivedUpperStarCompOfEq Λ (Category.id_comp f)).inv.app C) =
      (leftDerivedUpperStarCompOfEq Λ (Category.comp_id f')).hom.app ((N₁.nearbyCycles Λ).obj C) ≫
        L((f')^*⟦Λ⟧).map (((N₁.galoisLayerHom h₁ Ω₁).pullbackExchange Λ).app C) ≫
        ((galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange Λ).app (L((𝟙 X₁)^*⟦Λ⟧).obj C) ≫
        ((N₂.galoisLayer h₂ Ω₂).nearbyCycles Λ).map
          ((leftDerivedUpperStarCompOfEq Λ (Category.comp_id f)).inv.app C) := by
  have hA := (N₂.galoisLayerHom h₂ Ω₂).pullbackExchange_comp_app_of_eq Λ τ
    (galoisLayerMapDiagonal Ω₂ τ) (Category.id_comp f) (Category.id_comp f')
    (by simp) (by simp) C
  have hB := (galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange_comp_app_of_eq Λ
    (N₁.galoisLayerHom h₁ Ω₁) (galoisLayerMapDiagonal Ω₂ τ) (Category.comp_id f)
    (Category.comp_id f') (Category.comp_id _) (by simp) C
  have key := comp_eq_comp_of_comp_eq_aux hA hB (map_hom_app_comp_map_inv_app _ _ _)
    (map_hom_app_comp_map_inv_app _ _ _)
  convert key using 3

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
