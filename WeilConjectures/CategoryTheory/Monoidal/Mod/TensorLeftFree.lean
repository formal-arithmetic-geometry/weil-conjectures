/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular

/-!
# Tensoring with a free module of finite rank preserves monomorphisms

For a module `M` over a commutative monoid `A` in an abelian monoidal category which is free of
finite rank, `M ≅ Aⁿ`, the functor `- ⊗_A M` preserves monomorphisms
(`CategoryTheory.Mod.mono_tensorLeft_map_of_iso_biproduct`): `- ⊗_A ⨁ᵢ Mᵢ` is the direct sum of
the `- ⊗_A Mᵢ`, and `- ⊗_A A ≅ 𝟭`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {A : C}
  [MonObj A] [IsCommMonObj A]
  [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

/-- `- ⊗_A ·` as an additive map on morphisms. -/
@[simps]
noncomputable def tensorLeftMapAddHom (M M' : Mod C A) :
    (M ⟶ M') →+ (tensorLeft M ⟶ tensorLeft M') where
  toFun := tensorLeftMap
  map_zero' := by
    have h := tensorLeftMap_add (0 : M ⟶ M') 0
    rwa [add_zero, left_eq_add] at h
  map_add' := tensorLeftMap_add

omit [∀ (X : C), PreservesColimitsOfSize.{v, v, v, v, u, u} (MonoidalCategory.tensorRight X)] in
lemma sum_tensorLeftMap_π_comp_tensorLeftMap_ι {n : ℕ} (M : Fin n → Mod C A) :
    ∑ i, tensorLeftMap (biproduct.π M i) ≫ tensorLeftMap (biproduct.ι M i) =
      𝟙 (tensorLeft (⨁ M)) := by
  simp_rw [← tensorLeftMap_comp]
  calc ∑ i, tensorLeftMap (biproduct.π M i ≫ biproduct.ι M i) =
      tensorLeftMapAddHom (⨁ M) (⨁ M) (∑ i, biproduct.π M i ≫ biproduct.ι M i) := by
        rw [map_sum]; rfl
    _ = 𝟙 _ := by rw [biproduct.total]; exact tensorLeftMap_id _

omit [∀ (X : C), PreservesColimitsOfSize.{v, v, v, v, u, u} (MonoidalCategory.tensorRight X)] in
/-- `- ⊗_A ⨁ᵢ Mᵢ` preserves monomorphisms if each `- ⊗_A Mᵢ` does. -/
lemma mono_tensorLeft_biproduct_map {n : ℕ} (M : Fin n → Mod C A) {N N' : Mod C A}
    (f : N ⟶ N') (h : ∀ i, Mono ((tensorLeft (M i)).map f)) :
    Mono ((tensorLeft (⨁ M)).map f) := by
  refine Preadditive.mono_of_cancel_zero _ fun {Z} g hg ↦ ?_
  have htot := sum_tensorLeftMap_π_comp_tensorLeftMap_ι M
  have hi (i : Fin n) : g ≫ (tensorLeftMap (biproduct.π M i)).app N = 0 := by
    have := h i
    rw [← cancel_mono ((tensorLeft (M i)).map f), Category.assoc,
      ← (tensorLeftMap (biproduct.π M i)).naturality, ← Category.assoc, hg, zero_comp,
      zero_comp]
  rw [← Category.comp_id g, ← NatTrans.id_app, ← htot, NatTrans.app_sum, Preadditive.comp_sum]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [NatTrans.comp_app, ← Category.assoc, hi, zero_comp]

omit [∀ (X : C), PreservesColimitsOfSize.{v, v, v, v, u, u} (MonoidalCategory.tensorRight X)] in
/-- `- ⊗_A M` preserves monomorphisms for `M` free of finite rank. -/
lemma mono_tensorLeft_map_of_iso_biproduct {M : Mod C A} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ regular A) {N N' : Mod C A} (f : N ⟶ N') [Mono f] :
    Mono ((tensorLeft M).map f) := by
  have : Mono ((tensorLeft (⨁ fun _ : Fin n ↦ regular A)).map f) :=
    mono_tensorLeft_biproduct_map _ f fun _ ↦ by
      rw [← NatIso.naturality_2 tensorLeftRegularIso f]
      infer_instance
  have e' : tensorLeft M ≅ tensorLeft (⨁ fun _ : Fin n ↦ regular A) :=
    { hom := tensorLeftMap e.hom
      inv := tensorLeftMap e.inv
      hom_inv_id := by rw [← tensorLeftMap_comp, e.hom_inv_id, tensorLeftMap_id]
      inv_hom_id := by rw [← tensorLeftMap_comp, e.inv_hom_id, tensorLeftMap_id] }
  rw [← NatIso.naturality_2 e' f]
  infer_instance

section RegularLeft

variable (M : Mod C A)

/-- The action `A ⊗ M ⟶ M` as a morphism of `A`-modules, `A` acting on `A ⊗ M` through the
first factor. -/
def leftActHom : (tensorRight A M.X).obj (regular A) ⟶ M :=
  homMk (M := (tensorRight A M.X).obj (regular A)) (N := M) (act (A := A) M.X) (by
    change ((α_ A A M.X).inv ≫ μ[A] ▷ M.X) ≫ act (A := A) M.X =
      A ◁ act (A := A) M.X ≫ act (A := A) M.X
    rw [Category.assoc, mul_act, Iso.inv_hom_id_assoc])

omit [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v, v, u} C]
  [∀ (X : C), PreservesColimitsOfSize.{v, v, v, v, u, u} (MonoidalCategory.tensorLeft X)]
  [∀ (X : C), PreservesColimitsOfSize.{v, v, v, v, u, u} (MonoidalCategory.tensorRight X)] in
lemma tensorRightMap_act_comp_leftActHom :
    (tensorRightMap A (act (A := A) M.X)).app (regular A) ≫ leftActHom M =
      (tensorRightRightAct A M.X).app (regular A) ≫ leftActHom M := by
  ext
  change A ◁ act (A := A) M.X ≫ act (A := A) M.X =
    ((α_ A A M.X).inv ≫ ((β_ A A).hom ≫ μ[A]) ▷ M.X) ≫ act (A := A) M.X
  rw [IsCommMonObj.mul_comm, Category.assoc, mul_act, Iso.inv_hom_id_assoc]

/-- The cofork `A ⊗ (A ⊗ M) ⇉ A ⊗ M ⟶ M` of the action. -/
noncomputable abbrev leftActCofork :=
  Cofork.ofπ (leftActHom M) (tensorRightMap_act_comp_leftActHom M)

/-- The underlying cofork in `C` of the action is a (split) coequalizer, split by
`m ↦ 1 ⊗ m` and `a ⊗ m ↦ 1 ⊗ a ⊗ m`. -/
noncomputable def isColimitMapCoconeLeftActCofork :
    IsColimit ((forget A).mapCocone (leftActCofork M)) := by
  refine (isColimitMapCoconeCoforkEquiv _ _).symm ?_
  let s : M.X ⟶ A ⊗ M.X := (λ_ M.X).inv ≫ η[A] ▷ M.X
  let t : A ⊗ M.X ⟶ A ⊗ (A ⊗ M.X) := (λ_ (A ⊗ M.X)).inv ≫ η[A] ▷ (A ⊗ M.X)
  have hs : s ≫ act (A := A) M.X = 𝟙 _ := by simp [s]
  have ht₁ : t ≫ A ◁ act (A := A) M.X = act (A := A) M.X ≫ s := by
    simp only [t, s, Category.assoc]
    rw [← whisker_exchange, ← Category.assoc, ← leftUnitor_inv_naturality, Category.assoc]
  have ht₂ : t ≫ (α_ A A M.X).inv ≫ ((β_ A A).hom ≫ μ[A]) ▷ M.X = 𝟙 _ := by
    rw [IsCommMonObj.mul_comm]
    simp only [t, leftUnitor_tensor_inv, Category.assoc, associator_inv_naturality_left_assoc,
      Iso.hom_inv_id_assoc, ← comp_whiskerRight, MonObj.one_mul, Iso.inv_hom_id,
      id_whiskerRight]
  refine Cofork.IsColimit.mk _ (fun σ ↦ s ≫ σ.π) (fun σ ↦ ?_) (fun σ m hm ↦ ?_)
  · change act (A := A) M.X ≫ s ≫ σ.π = σ.π
    have hc := σ.condition
    change A ◁ act (A := A) M.X ≫ σ.π =
      ((α_ A A M.X).inv ≫ ((β_ A A).hom ≫ μ[A]) ▷ M.X) ≫ σ.π at hc
    rw [← Category.assoc, ← ht₁, Category.assoc, hc, ← Category.assoc, ← Category.assoc,
      Category.assoc t, ht₂, Category.id_comp]
  · change m = s ≫ σ.π
    rw [← hm]
    change m = s ≫ act (A := A) M.X ≫ m
    rw [← Category.assoc, hs, Category.id_comp]

variable [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)]

/-- The action cofork is a coequalizer in `A`-modules, forgetting to `C` reflecting colimits. -/
noncomputable def isColimitLeftActCofork : IsColimit (leftActCofork M) :=
  isColimitOfReflects (forget A) (isColimitMapCoconeLeftActCofork M)

/-- The cocone on the diagram defining `A ⊗_A M` given by the action. -/
noncomputable abbrev leftActCocone : Cocone ((tensorLeftDiagram A M).flip.obj (regular A)) :=
  (Cocone.precompose (diagramIsoParallelPair _).hom).obj (leftActCofork M)

/-- **Tensoring the regular module with `M` gives `M`**: `A ⊗_A M ≅ M` through the action. -/
noncomputable def tensorLeftObjRegularIso : (tensorLeft M).obj (regular A) ≅ M :=
  (colimit.isColimit ((tensorLeftDiagram A M).flip.obj (regular A))).coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv _ (leftActCofork M)).symm (isColimitLeftActCofork M) :
      IsColimit (leftActCocone M))

end RegularLeft

section IhomFree

omit [∀ (X : C), PreservesColimitsOfSize.{v, v, v, v, u, u} (MonoidalCategory.tensorRight X)] in
lemma tensorLeftMap_ι_comp_tensorLeftMap_π {n : ℕ} (M : Fin n → Mod C A) (i j : Fin n) :
    tensorLeftMap (biproduct.ι M i) ≫ tensorLeftMap (biproduct.π M j) =
      if h : i = j then eqToHom (by subst h; rfl) else 0 := by
  rw [← tensorLeftMap_comp, biproduct.ι_π]
  split_ifs with h
  · subst h
    simp [tensorLeftMap_id]
  · exact (tensorLeftMapAddHom _ _).map_zero

lemma ihomMap_π_comp_ihomMap_ι {n : ℕ} (M : Fin n → Mod C A) (i j : Fin n) :
    ihomMap (biproduct.π M j) ≫ ihomMap (biproduct.ι M i) =
      if h : i = j then eqToHom (by subst h; rfl) else 0 := by
  rw [← ihomMap_comp, biproduct.ι_π]
  split_ifs with h
  · subst h
    simp [ihomMap_id]
  · exact (ihomMapAddHom _ _).map_zero

/-- **For a free module of finite rank, `Hom_A(Aⁿ, -) ≅ - ⊗_A Aⁿ`**: both are `(-)ⁿ`. -/
noncomputable def ihomIsoTensorLeftFree (n : ℕ) :
    ihom (⨁ fun _ : Fin n ↦ regular A) ≅ tensorLeft (⨁ fun _ : Fin n ↦ regular A) where
  hom := ∑ i, ihomMap (biproduct.ι (fun _ : Fin n ↦ regular A) i) ≫ ihomRegularIso.hom ≫
    tensorLeftRegularIso.inv ≫ tensorLeftMap (biproduct.ι (fun _ : Fin n ↦ regular A) i)
  inv := ∑ i, tensorLeftMap (biproduct.π (fun _ : Fin n ↦ regular A) i) ≫
    tensorLeftRegularIso.hom ≫ ihomRegularIso.inv ≫
      ihomMap (biproduct.π (fun _ : Fin n ↦ regular A) i)
  hom_inv_id := by
    rw [Preadditive.sum_comp]
    simp_rw [Preadditive.comp_sum, Category.assoc]
    have (i j : Fin n) : ihomMap (biproduct.ι (fun _ : Fin n ↦ regular A) i) ≫
        ihomRegularIso.hom ≫ tensorLeftRegularIso.inv ≫
        tensorLeftMap (biproduct.ι (fun _ : Fin n ↦ regular A) i) ≫
        tensorLeftMap (biproduct.π (fun _ : Fin n ↦ regular A) j) ≫
          tensorLeftRegularIso.hom ≫ ihomRegularIso.inv ≫
            ihomMap (biproduct.π (fun _ : Fin n ↦ regular A) j) =
        if i = j then ihomMap (biproduct.ι (fun _ : Fin n ↦ regular A) i) ≫
            ihomMap (biproduct.π (fun _ : Fin n ↦ regular A) i) else 0 := by
      rw [← Category.assoc (tensorLeftMap _), tensorLeftMap_ι_comp_tensorLeftMap_π]
      split_ifs with h
      · subst h
        simp
      · simp
    simp_rw [this]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact sum_ihomMap_ι_comp_ihomMap_π _
  inv_hom_id := by
    rw [Preadditive.sum_comp]
    simp_rw [Preadditive.comp_sum, Category.assoc]
    have (i j : Fin n) : tensorLeftMap (biproduct.π (fun _ : Fin n ↦ regular A) i) ≫
        tensorLeftRegularIso.hom ≫ ihomRegularIso.inv ≫
        ihomMap (biproduct.π (fun _ : Fin n ↦ regular A) i) ≫
        ihomMap (biproduct.ι (fun _ : Fin n ↦ regular A) j) ≫ ihomRegularIso.hom ≫
          tensorLeftRegularIso.inv ≫ tensorLeftMap (biproduct.ι (fun _ : Fin n ↦ regular A) j) =
        if j = i then tensorLeftMap (biproduct.π (fun _ : Fin n ↦ regular A) i) ≫
            tensorLeftMap (biproduct.ι (fun _ : Fin n ↦ regular A) i) else 0 := by
      rw [← Category.assoc (ihomMap _), ihomMap_π_comp_ihomMap_ι]
      split_ifs with h
      · subst h
        simp
      · simp
    simp_rw [this]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact sum_tensorLeftMap_π_comp_tensorLeftMap_ι _

end IhomFree

end CategoryTheory.Mod
