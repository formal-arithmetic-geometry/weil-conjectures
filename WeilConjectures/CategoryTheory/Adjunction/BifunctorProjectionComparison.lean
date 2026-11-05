/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Products.Basic
public import WeilConjectures.PoincareDuality.Abstract

/-!
# The projection comparison of an adjunction along bifunctors

Let `adj : P ⊣ S` be an adjunction with `P : C ⥤ D`, let `T_C : C × C ⥤ C` and
`T_D : D × D ⥤ D` be bifunctors (tensor products, written `⊗`), and let
`μ : T_C (S a, S b) ⟶ S (T_D (a, b))` be a natural transformation (a lax structure of `S`).
The *projection comparison* `P (M ⊗ S N) ⟶ P M ⊗ N`
(`CategoryTheory.Adjunction.bifunctorProjectionComparison`) is the transpose of
`M ⊗ S N ⟶ S P M ⊗ S N ⟶ S (P M ⊗ N)`. When `T_C`, `T_D` are the tensor products of monoidal
categories and `μ` is the lax monoidal structure of `S`, this is
`CategoryTheory.Adjunction.projectionComparison`.

We show that functors `N_C : C ⥤ C'` and `N_D : D ⥤ D'` to monoidal categories, carrying the
bifunctors to the tensor products and `μ` to the lax monoidal structure of the right adjoint
`S'` of an adjunction `P' ⊣ S'`, up to a natural transformation `γ : S ⋙ N_C ⟶ N_D ⋙ S'`,
carry the projection comparison of `adj` to that of `P' ⊣ S'`, up to the mate
`β : N_C ⋙ P' ⟶ P ⋙ N_D` of `γ`
(`CategoryTheory.Adjunction.mateEquiv_symm_app_comp_map_bifunctorProjectionComparison`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] {P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S)
  {T_C : C × C ⥤ C} {T_D : D × D ⥤ D} (μ : S.prod S ⋙ T_C ⟶ T_D ⋙ S)

/-- The projection comparison `P (T_C (M, S N)) ⟶ T_D (P M, N)` of an adjunction `P ⊣ S` along
bifunctors `T_C`, `T_D` and a natural transformation `μ : T_C (S a, S b) ⟶ S (T_D (a, b))`: the
transpose of `T_C (M, S N) ⟶ T_C (S P M, S N) ⟶ S (T_D (P M, N))`. -/
noncomputable def bifunctorProjectionComparison (M : C) (N : D) :
    P.obj (T_C.obj (M, S.obj N)) ⟶ T_D.obj (P.obj M, N) :=
  (adj.homEquiv _ _).symm (T_C.map (Prod.mkHom (adj.unit.app M) (𝟙 (S.obj N))) ≫
    μ.app (P.obj M, N))

/-- The projection comparison along bifunctors is natural in both variables. -/
@[reassoc]
lemma bifunctorProjectionComparison_naturality {M M' : C} {N N' : D} (f : M ⟶ M')
    (g : N ⟶ N') :
    adj.bifunctorProjectionComparison μ M N ≫ T_D.map (Prod.mkHom (P.map f) g) =
      P.map (T_C.map (Prod.mkHom f (S.map g))) ≫ adj.bifunctorProjectionComparison μ M' N' := by
  rw [bifunctorProjectionComparison, bifunctorProjectionComparison,
    ← homEquiv_naturality_right_symm, ← homEquiv_naturality_left_symm, Category.assoc]
  congr 1
  have hμ := μ.naturality (Prod.mkHom (P.map f) g)
  dsimp at hμ
  erw [<- hμ]
  rw [<- T_C.map_comp_assoc, <- T_C.map_comp_assoc]
  congr 2
  ext
  · simp
  · simp

variable {C' D' : Type*} [Category* C'] [Category* D'] [MonoidalCategory C']
  [MonoidalCategory D'] {P' : C' ⥤ D'} {S' : D' ⥤ C'} (adj' : P' ⊣ S') [S'.LaxMonoidal]
  {N_C : C ⥤ C'} {N_D : D ⥤ D'}

/-- **Transport of the projection comparison.** Let `γ : S ⋙ N_C ⟶ N_D ⋙ S'` be compatible with
`μ` and the lax monoidal structure of `S'`, up to comparisons `τ_C`, `τ_D` of the bifunctors with
the tensor products. Then, up to `τ_C`, `τ_D`, `γ` and the mate `β : N_C ⋙ P' ⟶ P ⋙ N_D` of `γ`,
`N_D` carries the projection comparison `q` of `P ⊣ S` along `μ` to the projection comparison `q'`
of `P' ⊣ S'`:
```
P' N_C (M ⊗ S N) ──β──▶ N_D P (M ⊗ S N) ──N_D(q)──▶ N_D (P M ⊗ N) ──τ_D──▶ N_D P M ⊗ N_D N
      │                                                                          ▲
 P'(τ_C ≫ 1 ⊗ γ)                                                              β ⊗ 1
      ▼                                                                          │
P' (N_C M ⊗ S' N_D N) ────────────────────q'──────────────────────▶ P' N_C M ⊗ N_D N
```
-/
lemma mateEquiv_symm_app_comp_map_bifunctorProjectionComparison (γ : S ⋙ N_C ⟶ N_D ⋙ S')
    (τ_C : T_C ⋙ N_C ≅ N_C.prod N_C ⋙ tensor C') (τ_D : T_D ⋙ N_D ≅ N_D.prod N_D ⋙ tensor D')
    (hμ : ∀ a b : D, N_C.map (μ.app (a, b)) ≫ γ.app (T_D.obj (a, b)) ≫
        S'.map (τ_D.hom.app (a, b)) =
      τ_C.hom.app (S.obj a, S.obj b) ≫ (γ.app a ⊗ₘ γ.app b) ≫
        Functor.LaxMonoidal.μ S' (N_D.obj a) (N_D.obj b))
    (M : C) (N : D) :
    ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ γ)).natTrans.app (T_C.obj (M, S.obj N)) ≫
        N_D.map (adj.bifunctorProjectionComparison μ M N) ≫ τ_D.hom.app (P.obj M, N) =
      P'.map (τ_C.hom.app (M, S.obj N) ≫ N_C.obj M ◁ γ.app N) ≫
        adj'.projectionComparison (N_C.obj M) (N_D.obj N) ≫
        ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ γ)).natTrans.app M ▷ N_D.obj N := by
  set β := (mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ γ)
  have hβ (X : C) : adj'.unit.app _ ≫ S'.map (β.natTrans.app X) =
      N_C.map (adj.unit.app X) ≫ γ.app (P.obj X) :=
    (unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ γ) X).symm
  apply (adj'.homEquiv _ _).injective
  rw [homEquiv_naturality_left, homEquiv_naturality_right, homEquiv_naturality_right,
    homEquiv_unit, hβ, projectionComparison]
  erw [Equiv.apply_symm_apply]
  have hγ := γ.naturality (adj.bifunctorProjectionComparison μ M N)
  dsimp at hγ
  have hp : adj.unit.app _ ≫ S.map (adj.bifunctorProjectionComparison μ M N) =
      T_C.map (Prod.mkHom (adj.unit.app M) (𝟙 (S.obj N))) ≫ μ.app (P.obj M, N) := by
    refine (adj.homEquiv_unit _ _ _).symm.trans ?_
    rw [bifunctorProjectionComparison]
    exact Equiv.apply_symm_apply _ _
  have hτ := τ_C.hom.naturality (Prod.mkHom (adj.unit.app M) (𝟙 (S.obj N)))
  dsimp at hτ
  have hμ' := Functor.LaxMonoidal.μ_natural_left S' (β.natTrans.app M) (N_D.obj N)
  simp only [Category.assoc]
  rw [S'.map_comp, <- reassoc_of% hγ, <- N_C.map_comp_assoc, hp, N_C.map_comp_assoc,
    hμ (P.obj M) N, reassoc_of% hτ]
  erw [<- hμ']
  rw [<- comp_whiskerRight_assoc, hβ]
  simp [tensorHom_def, whisker_exchange_assoc]

/-- If the base change `β` of the extensions by zero is an isomorphism and `γ` is an isomorphism at
`N`, then `N_D` carries the projection comparison along `μ` to an isomorphism as soon as the
projection comparison of `P' ⊣ S'` is an isomorphism. -/
lemma isIso_map_bifunctorProjectionComparison (γ : S ⋙ N_C ⟶ N_D ⋙ S')
    (τ_C : T_C ⋙ N_C ≅ N_C.prod N_C ⋙ tensor C') (τ_D : T_D ⋙ N_D ≅ N_D.prod N_D ⋙ tensor D')
    (hμ : ∀ a b : D, N_C.map (μ.app (a, b)) ≫ γ.app (T_D.obj (a, b)) ≫
        S'.map (τ_D.hom.app (a, b)) =
      τ_C.hom.app (S.obj a, S.obj b) ≫ (γ.app a ⊗ₘ γ.app b) ≫
        Functor.LaxMonoidal.μ S' (N_D.obj a) (N_D.obj b))
    [IsIso ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ γ)).natTrans] (M : C) (N : D)
    [IsIso (γ.app N)] [IsIso (adj'.projectionComparison (N_C.obj M) (N_D.obj N))] :
    IsIso (N_D.map (adj.bifunctorProjectionComparison μ M N)) := by
  have h := adj.mateEquiv_symm_app_comp_map_bifunctorProjectionComparison μ adj' γ τ_C τ_D hμ M N
  have : IsIso (((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ γ)).natTrans.app
      (T_C.obj (M, S.obj N)) ≫ N_D.map (adj.bifunctorProjectionComparison μ M N) ≫
        τ_D.hom.app (P.obj M, N)) := by
    rw [h]
    infer_instance
  have := IsIso.of_isIso_comp_left (((mateEquiv adj adj').symm
    (TwoSquare.mk _ _ _ _ γ)).natTrans.app (T_C.obj (M, S.obj N)))
    (N_D.map (adj.bifunctorProjectionComparison μ M N) ≫ τ_D.hom.app (P.obj M, N))
  exact IsIso.of_isIso_comp_right _ (τ_D.hom.app (P.obj M, N))

variable [∀ M N, IsIso (adj.bifunctorProjectionComparison μ M N)]

/-- The projection formula `T_D (P M, N) ≅ P (T_C (M, S N))`, the inverse of the projection
comparison along `μ` when it is an isomorphism. -/
noncomputable def bifunctorProjectionIso :
    P.prod (𝟭 D) ⋙ T_D ≅ (𝟭 C).prod S ⋙ T_C ⋙ P :=
  NatIso.ofComponents (fun MN ↦ (asIso (adj.bifunctorProjectionComparison μ MN.1 MN.2)).symm)
    (fun {MN MN'} fg ↦ by
      dsimp
      rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
      exact adj.bifunctorProjectionComparison_naturality μ fg.1 fg.2)

@[simp]
lemma bifunctorProjectionIso_hom_app (M : C) (N : D) :
    (adj.bifunctorProjectionIso μ).hom.app (M, N) =
      inv (adj.bifunctorProjectionComparison μ M N) :=
  rfl

/-- **Transport of the projection formula.** Under the hypotheses of
`CategoryTheory.Adjunction.mateEquiv_symm_app_comp_map_bifunctorProjectionComparison`, for an
isomorphism `β` lifting the mate of `γ`, `N_D` carries the projection formula
`T_D (P M, N) ≅ P (T_C (M, S N))` to the inverse of the projection comparison of `P' ⊣ S'`, up to
`τ_C`, `τ_D`, `β` and `γ`. -/
lemma map_bifunctorProjectionIso_hom_app (γ : S ⋙ N_C ⟶ N_D ⋙ S')
    (τ_C : T_C ⋙ N_C ≅ N_C.prod N_C ⋙ tensor C') (τ_D : T_D ⋙ N_D ≅ N_D.prod N_D ⋙ tensor D')
    (hμ : ∀ a b : D, N_C.map (μ.app (a, b)) ≫ γ.app (T_D.obj (a, b)) ≫
        S'.map (τ_D.hom.app (a, b)) =
      τ_C.hom.app (S.obj a, S.obj b) ≫ (γ.app a ⊗ₘ γ.app b) ≫
        Functor.LaxMonoidal.μ S' (N_D.obj a) (N_D.obj b))
    (β : N_C ⋙ P' ≅ P ⋙ N_D)
    (hβ : β.hom = ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ γ)).natTrans) (M : C) (N : D)
    [IsIso (adj'.projectionComparison (N_C.obj M) (N_D.obj N))] :
    N_D.map ((adj.bifunctorProjectionIso μ).hom.app (M, N)) ≫ β.inv.app _ ≫
        P'.map (τ_C.hom.app (M, S.obj N) ≫ N_C.obj M ◁ γ.app N) =
      τ_D.hom.app (P.obj M, N) ≫ β.inv.app M ▷ N_D.obj N ≫
        inv (adj'.projectionComparison (N_C.obj M) (N_D.obj N)) := by
  have h := adj.mateEquiv_symm_app_comp_map_bifunctorProjectionComparison μ adj' γ τ_C τ_D hμ M N
  rw [← hβ] at h
  rw [bifunctorProjectionIso_hom_app, Functor.map_inv, IsIso.inv_comp_eq,
    ← cancel_epi (β.hom.app _), Iso.hom_inv_id_app_assoc]
  dsimp only [Functor.prod_obj, Functor.id_obj]
  rw [reassoc_of% h,
    ← comp_whiskerRight_assoc, Iso.hom_inv_id_app]
  simp

end CategoryTheory.Adjunction
