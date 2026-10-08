/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-!

# The projection formula and the linear lift of a left adjoint to module objects

Let `adj : P ⊣ S` be an adjunction with `S : D ⥤ C` strong monoidal (for instance `P = j_!` and
`S = j^*` for an open immersion `j`, or `P = f_!` and `S = f^*` in a six-functor formalism).
The *projection formula map*
```
P (S L ⊗ M) ⟶ L ⊗ P M
```
(`Adjunction.projectionFormulaMap`) is the adjoint of `S L ⊗ M ⟶ S L ⊗ S P M ⟶ S (L ⊗ P M)`,
given by the unit of `adj` and the lax structure of `S`. It is natural in `L` and `M` and
compatible with the unit and the associativity constraints
(`Adjunction.projectionFormulaMap_unit`, `Adjunction.projectionFormulaMap_assoc`); these
coherences are formal consequences of the monoidal structure of `S`. The *projection formula*
is the statement that it is an isomorphism (`Adjunction.HasProjectionFormula`); it is a
property of the geometric situation, not of the formalism.

When the projection formula holds, `P` lifts to module objects: for an algebra object `B : D`,
an `S B`-module object `M` makes `P M` a `B`-module object, with action
```
B ⊗ P M ≅ P (S B ⊗ M) ⟶ P M
```
(`Adjunction.projectionFormulaModObj`), and this is a functor
`Adjunction.mapModLeft adj B : Mod C (S.obj B) ⥤ Mod D B`, the *linear lift* of `P`. It is
left adjoint to the transport `S.mapMod : Mod D B ⥤ Mod C (S.obj B)` of module objects along the
strong monoidal `S` (`Adjunction.mapModLeftAdjunction`): the projection formula map is exactly
what is needed to transpose `B`-linearity into `S B`-linearity along `adj`. It commutes with
the forgetful functors, and it is exact when `P` is.

Combined with the change of scalars of
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, this gives the exceptional
pushforward on module objects over a coefficient ring sheaf: `f_! = (linear f_!) ∘ Res_{α_f}`,
see `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Limits Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S) [S.Monoidal]

/-! ### The projection formula map -/

/-- The projection formula map `P (S L ⊗ M) ⟶ L ⊗ P M` of an adjunction `P ⊣ S` with `S`
monoidal: the adjoint of `S L ⊗ M ⟶ S L ⊗ S P M ⟶ S (L ⊗ P M)`. -/
noncomputable def projectionFormulaMap (L : D) (M : C) : P.obj (S.obj L ⊗ M) ⟶ L ⊗ P.obj M :=
  (adj.homEquiv _ _).symm (S.obj L ◁ adj.unit.app M ≫ Functor.LaxMonoidal.μ S L (P.obj M))

lemma homEquiv_projectionFormulaMap (L : D) (M : C) :
    adj.homEquiv _ _ (adj.projectionFormulaMap L M) =
      S.obj L ◁ adj.unit.app M ≫ Functor.LaxMonoidal.μ S L (P.obj M) := by
  simp [projectionFormulaMap]

/-- The projection formula map is natural in `L`. -/
@[reassoc]
lemma projectionFormulaMap_natural_left {L L' : D} (f : L ⟶ L') (M : C) :
    P.map (S.map f ▷ M) ≫ adj.projectionFormulaMap L' M =
      adj.projectionFormulaMap L M ≫ f ▷ P.obj M := by
  apply (adj.homEquiv _ _).injective
  rw [homEquiv_naturality_left, homEquiv_naturality_right, homEquiv_projectionFormulaMap,
    homEquiv_projectionFormulaMap, Category.assoc, ← μ_natural_left, ← whisker_exchange_assoc]
  rfl

/-- The projection formula map is natural in `M`. -/
@[reassoc]
lemma projectionFormulaMap_natural_right (L : D) {M M' : C} (g : M ⟶ M') :
    P.map (S.obj L ◁ g) ≫ adj.projectionFormulaMap L M' =
      adj.projectionFormulaMap L M ≫ L ◁ P.map g := by
  apply (adj.homEquiv _ _).injective
  rw [homEquiv_naturality_left, homEquiv_naturality_right, homEquiv_projectionFormulaMap,
    homEquiv_projectionFormulaMap, Category.assoc, ← μ_natural_right,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [adj.unit_naturality]

/-- The projection formula map is compatible with the unit: for `L = 𝟙`, it is the
identification `P (S 𝟙 ⊗ M) ≅ P M ≅ 𝟙 ⊗ P M`. -/
@[reassoc]
lemma projectionFormulaMap_unit (M : C) :
    adj.projectionFormulaMap (𝟙_ D) M ≫ (λ_ (P.obj M)).hom =
      P.map (Functor.OplaxMonoidal.η S ▷ M ≫ (λ_ M).hom) := by
  apply (adj.homEquiv _ _).injective
  rw [homEquiv_naturality_right, homEquiv_projectionFormulaMap, ← Category.comp_id (P.map _),
    homEquiv_naturality_left, homEquiv_id, Category.assoc,
    ← Category.id_comp (Functor.LaxMonoidal.μ S (𝟙_ D) _),
    ← Functor.Monoidal.whiskerRight_η_ε (F := S), Category.assoc, Category.assoc,
    ← Functor.LaxMonoidal.left_unitality]
  erw [whisker_exchange_assoc, leftUnitor_naturality]
  simp only [Category.assoc]
  rfl

/-- The projection formula map is compatible with the associativity constraints. -/
@[reassoc]
lemma projectionFormulaMap_assoc (L L' : D) (M : C) :
    adj.projectionFormulaMap (L ⊗ L') M ≫ (α_ L L' (P.obj M)).hom =
      P.map (δ S L L' ▷ M ≫ (α_ (S.obj L) (S.obj L') M).hom) ≫
        adj.projectionFormulaMap L (S.obj L' ⊗ M) ≫ L ◁ adj.projectionFormulaMap L' M := by
  apply (adj.homEquiv _ _).injective
  rw [homEquiv_naturality_right, homEquiv_naturality_left, homEquiv_naturality_right,
    homEquiv_projectionFormulaMap, homEquiv_projectionFormulaMap]
  simp only [Category.assoc]
  rw [← μ_natural_right, ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [← adj.homEquiv_unit, homEquiv_projectionFormulaMap]
  rw [← cancel_epi (Functor.LaxMonoidal.μ S L L' ▷ M), Functor.Monoidal.whiskerRight_μ_δ_assoc]
  erw [← whisker_exchange_assoc, Functor.LaxMonoidal.associativity,
    associator_naturality_right_assoc]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]

/-! ### The projection formula -/

/-- An adjunction `P ⊣ S` with `S` monoidal *satisfies the projection formula* if the
projection formula maps `P (S L ⊗ M) ⟶ L ⊗ P M` are isomorphisms. -/
class HasProjectionFormula : Prop where
  isIso (L : D) (M : C) : IsIso (adj.projectionFormulaMap L M)

attribute [instance] HasProjectionFormula.isIso

/-! ### The linear lift of `P` to module objects -/

section MapModLeft

variable [adj.HasProjectionFormula] (B : D) [MonObj B]

/-- The action of `B` on `P M` for an `S B`-module object `M`, through the projection
formula: `B ⊗ P M ≅ P (S B ⊗ M) ⟶ P M`. -/
noncomputable def projectionFormulaSMul (M : C) [ModObj (S.obj B) M] : B ⊗ P.obj M ⟶ P.obj M :=
  inv (adj.projectionFormulaMap B M) ≫ P.map γ[S.obj B,M]

@[reassoc]
lemma projectionFormulaMap_projectionFormulaSMul (M : C) [ModObj (S.obj B) M] :
    adj.projectionFormulaMap B M ≫ adj.projectionFormulaSMul B M = P.map γ[S.obj B,M] := by
  simp [projectionFormulaSMul]

@[reassoc]
lemma whiskerRight_inv_projectionFormulaMap {L L' : D} (f : L ⟶ L') (M : C) :
    f ▷ P.obj M ≫ inv (adj.projectionFormulaMap L' M) =
      inv (adj.projectionFormulaMap L M) ≫ P.map (S.map f ▷ M) := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, ← projectionFormulaMap_natural_left, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

@[reassoc]
lemma whiskerLeft_inv_projectionFormulaMap (L : D) {M M' : C} (g : M ⟶ M') :
    L ◁ P.map g ≫ inv (adj.projectionFormulaMap L M') =
      inv (adj.projectionFormulaMap L M) ≫ P.map (S.obj L ◁ g) := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, ← projectionFormulaMap_natural_right, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- For an `S B`-module object `M`, `P M` is a `B`-module object through the projection
formula. -/
@[instance_reducible]
noncomputable def projectionFormulaModObj (M : C) [ModObj (S.obj B) M] : ModObj B (P.obj M) where
  smul := adj.projectionFormulaSMul B M
  one_smul := by
    change η[B] ▷ P.obj M ≫ adj.projectionFormulaSMul B M = (λ_ (P.obj M)).hom
    have h : S.map η[B] ▷ M ≫ γ[S.obj B,M] = Functor.OplaxMonoidal.η S ▷ M ≫ (λ_ M).hom := by
      rw [← ModObj.one_smul_self (S.obj B) M, Functor.obj.η_def, comp_whiskerRight,
        Category.assoc, ← Category.assoc (Functor.OplaxMonoidal.η S ▷ M),
        Functor.Monoidal.whiskerRight_η_ε, Category.id_comp]
    rw [projectionFormulaSMul, whiskerRight_inv_projectionFormulaMap_assoc, ← P.map_comp, h,
      ← projectionFormulaMap_unit, IsIso.inv_hom_id_assoc]
  mul_smul := by
    change μ[B] ▷ P.obj M ≫ adj.projectionFormulaSMul B M =
      (α_ B B (P.obj M)).hom ≫ B ◁ adj.projectionFormulaSMul B M ≫ adj.projectionFormulaSMul B M
    have h : S.map μ[B] ▷ M ≫ γ[S.obj B,M] = (δ S B B ▷ M ≫ (α_ _ _ _).hom) ≫
        S.obj B ◁ γ[S.obj B,M] ≫ γ[S.obj B,M] := by
      rw [Category.assoc, ← ModObj.mul_smul_self (S.obj B) M, Functor.obj.μ_def,
        comp_whiskerRight, Category.assoc, ← Category.assoc (δ S B B ▷ M),
        Functor.Monoidal.whiskerRight_δ_μ, Category.id_comp]
    have h' : inv (adj.projectionFormulaMap (B ⊗ B) M) ≫
        P.map (δ S B B ▷ M ≫ (α_ (S.obj B) (S.obj B) M).hom) =
          (α_ B B (P.obj M)).hom ≫ B ◁ inv (adj.projectionFormulaMap B M) ≫
            inv (adj.projectionFormulaMap B (S.obj B ⊗ M)) := by
      rw [IsIso.inv_comp_eq, projectionFormulaMap_assoc_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, IsIso.hom_inv_id,
        MonoidalCategory.whiskerLeft_id, Category.id_comp, IsIso.hom_inv_id, Category.comp_id]
    rw [projectionFormulaSMul, whiskerRight_inv_projectionFormulaMap_assoc, ← P.map_comp, h,
      P.map_comp, ← Category.assoc, h', P.map_comp]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      whiskerLeft_inv_projectionFormulaMap_assoc]

lemma projectionFormulaModObj_smul (M : C) [ModObj (S.obj B) M] :
    (adj.projectionFormulaModObj B M).smul = adj.projectionFormulaSMul B M := rfl

/-- The linear lift of `P` to module objects: an `S B`-module object `M` is sent to `P M` with
the `B`-action induced by the projection formula. -/
noncomputable def mapModLeft : Mod C (S.obj B) ⥤ Mod D B where
  obj M := letI := adj.projectionFormulaModObj B M.X; ⟨P.obj M.X⟩
  map {M N} f :=
    letI := adj.projectionFormulaModObj B M.X
    letI := adj.projectionFormulaModObj B N.X
    Mod.Hom.mk' (P.map f.hom) (by
      change adj.projectionFormulaSMul B M.X ≫ P.map f.hom =
        B ◁ P.map f.hom ≫ adj.projectionFormulaSMul B N.X
      rw [projectionFormulaSMul, projectionFormulaSMul, Category.assoc, ← P.map_comp,
        Mod.smul_hom, P.map_comp, whiskerLeft_inv_projectionFormulaMap_assoc])
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

lemma mapModLeft_obj_X (M : Mod C (S.obj B)) : ((adj.mapModLeft B).obj M).X = P.obj M.X := rfl

lemma mapModLeft_map_hom {M N : Mod C (S.obj B)} (f : M ⟶ N) :
    ((adj.mapModLeft B).map f).hom = P.map f.hom := rfl

lemma mapModLeft_obj_smul (M : Mod C (S.obj B)) :
    γ[B,((adj.mapModLeft B).obj M).X] = adj.projectionFormulaSMul B M.X := rfl

/-- The linear lift of `P` commutes with the forgetful functors. -/
lemma mapModLeft_comp_forget : adj.mapModLeft B ⋙ Mod.forget B = Mod.forget (S.obj B) ⋙ P := rfl

/-! ### The adjunction `mapModLeft ⊣ mapMod` -/

variable {B}

/-- A map `P M ⟶ N` is `B`-linear iff its adjoint `M ⟶ S N` is `S B`-linear, for the
action of `B` on `P M` through the projection formula and of `S B` on `S N` through the lax
structure of `S`. -/
lemma projectionFormulaSMul_comp_eq_iff (M : Mod C (S.obj B)) (N : Mod D B)
    (φ : P.obj M.X ⟶ N.X) :
    adj.projectionFormulaSMul B M.X ≫ φ = B ◁ φ ≫ γ[B,N.X] ↔
      γ[S.obj B,M.X] ≫ adj.homEquiv M.X N.X φ =
        S.obj B ◁ adj.homEquiv M.X N.X φ ≫ Functor.LaxMonoidal.μ S B N.X ≫ S.map γ[B,N.X] := by
  rw [projectionFormulaSMul, Category.assoc, IsIso.inv_comp_eq,
    ← (adj.homEquiv _ _).apply_eq_iff_eq,
    homEquiv_naturality_left, homEquiv_naturality_right, S.map_comp,
    homEquiv_projectionFormulaMap, Category.assoc, ← μ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [← adj.homEquiv_unit]
  exact Iff.rfl

/-- The linear lift of `P` is left adjoint to the transport of module objects along `S`: a
`B`-linear map `P M ⟶ N` is the same as an `S B`-linear map `M ⟶ S N`. -/
noncomputable def mapModLeftAdjunction : adj.mapModLeft B ⊣ S.mapMod (R := B) :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun φ := Mod.Hom.mk' (adj.homEquiv M.X N.X φ.hom)
            ((adj.projectionFormulaSMul_comp_eq_iff M N φ.hom).1 (Mod.smul_hom φ))
          invFun ψ := Mod.Hom.mk' ((adj.homEquiv M.X N.X).symm ψ.hom)
            ((adj.projectionFormulaSMul_comp_eq_iff M N _).2
              (by simp only [Equiv.apply_symm_apply]; exact Mod.smul_hom ψ))
          left_inv φ := by ext; simp
          right_inv ψ := by ext; simp }
      homEquiv_naturality_left_symm _ _ := Mod.hom_ext _ _ (adj.homEquiv_naturality_left_symm _ _)
      homEquiv_naturality_right _ _ := Mod.hom_ext _ _ (adj.homEquiv_naturality_right _ _) }

instance : (adj.mapModLeft B).IsLeftAdjoint := (adj.mapModLeftAdjunction (B := B)).isLeftAdjoint

/-! ### Additivity and exactness -/

section Preadditive

variable [Preadditive C] [Preadditive D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  [P.Additive]

instance additive_mapModLeft : (adj.mapModLeft B).Additive where
  map_add := by intros; ext; simp [mapModLeft_map_hom]

end Preadditive

section Exact

variable [Abelian C] [Abelian D] [MonoidalPreadditive C] [MonoidalPreadditive D] [P.Additive]
  [PreservesFiniteColimits (tensorLeft (S.obj B))] [PreservesFiniteColimits (tensorLeft B)]

/-- If `P` is left exact, then so is its linear lift: finite limits of module objects are
computed in the ambient categories on both sides. -/
instance preservesFiniteLimits_mapModLeft [PreservesFiniteLimits P] :
    PreservesFiniteLimits (adj.mapModLeft B) where
  preservesFiniteLimits J _ _ :=
    have : PreservesLimitsOfShape J (adj.mapModLeft B ⋙ Mod.forget B) :=
      inferInstanceAs (PreservesLimitsOfShape J (Mod.forget (S.obj B) ⋙ P))
    have : ReflectsLimitsOfShape J (Mod.forget B : Mod D B ⥤ D) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    preservesLimitsOfShape_of_reflects_of_preserves (adj.mapModLeft B) (Mod.forget B)

/-- If `P` is right exact, then so is its linear lift. -/
instance preservesFiniteColimits_mapModLeft [PreservesFiniteColimits P] :
    PreservesFiniteColimits (adj.mapModLeft B) where
  preservesFiniteColimits J _ _ :=
    have : PreservesColimitsOfShape J (adj.mapModLeft B ⋙ Mod.forget B) :=
      inferInstanceAs (PreservesColimitsOfShape J (Mod.forget (S.obj B) ⋙ P))
    have : ReflectsColimitsOfShape J (Mod.forget B : Mod D B ⥤ D) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    preservesColimitsOfShape_of_reflects_of_preserves (adj.mapModLeft B) (Mod.forget B)

end Exact

end MapModLeft

end CategoryTheory.Adjunction
