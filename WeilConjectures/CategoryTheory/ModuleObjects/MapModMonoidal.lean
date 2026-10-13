/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric

/-!

# Monoidality of `mapMod` and of change of scalars along an isomorphism

Let `C` and `D` be braided monoidal categories with coequalizers preserved by tensoring on either
side, so that the module objects over a commutative algebra object carry the relative tensor
product `⊗_R` (`WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`). This file shows that the
two operations out of which the pullback of module objects over a coefficient ring sheaf is
built are strong monoidal for `⊗_R`:

* **Transport along a braided functor.** For a braided (strong monoidal) functor `F : C ⥤ D`
  preserving coequalizers and a commutative algebra object `R : C`, the functor
  `F.mapMod : Mod C R ⥤ Mod D (F.obj R)` is strong monoidal
  (`Functor.mapModCoreMonoidal`, `Functor.monoidal_mapMod`). The comparison
  `F M ⊗_{F R} F N ≅ F (M ⊗_R N)` is induced on the coequalizers presenting both sides by the
  tensorator `μ F M N : F M ⊗ F N ≅ F (M ⊗ N)`: the coequalizer presenting `M ⊗_R N` is
  preserved by `F`, and `μ F` identifies the image of its parallel pair with the parallel pair
  presenting `F M ⊗_{F R} F N`. The braiding of `F` is needed because the right action of `R`
  on a module object involves the braiding of `C`.
* **Restriction of scalars along an isomorphism.** For an isomorphism `ψ : S ⟶ R` of
  commutative algebra objects, `Mod.comap ψ : Mod C R ⥤ Mod C S` is strong monoidal
  (`Mod.comapCoreMonoidal`, `Mod.monoidal_comap`): the coequalizers presenting `M ⊗_R N` and
  `M ⊗_S N` are coequalizers of parallel pairs differing by the isomorphism `M ⊗ ψ ⊗ N`, and
  the comparison is the identity of `M ⊗ N` on the projections. Consequently the extension of
  scalars along an isomorphism `φ` of commutative algebra objects, which is the restriction of
  scalars along `φ⁻¹` (`Mod.extendScalarsIsoComapInv`), is strong monoidal
  (`Mod.monoidal_extendScalars`).

## Main definitions

- `Mod.tensorDesc`: a morphism out of `M ⊗_R N` from an `R`-balanced morphism out of `M ⊗ N`.
- `Functor.mapModTensorIso`, `Functor.mapModCoreMonoidal`, `Functor.monoidal_mapMod`: the strong
  monoidal structure of `F.mapMod`.
- `Mod.comapTensorIso`, `Mod.comapCoreMonoidal`, `Mod.monoidal_comap`: the strong monoidal
  structure of `Mod.comap ψ` along an isomorphism `ψ`.
- `Mod.monoidal_extendScalars`: the strong monoidal structure of `Mod.extendScalars φ` along an
  isomorphism `φ`.

## Sorried input

The data (the comparison isomorphisms) is constructed; the following properties are `sorry`ed:

- the balancing conditions `Functor.mapMod_μ_balanced`, `Functor.mapMod_δ_balanced`,
  `Mod.comap_tensorπ_balanced` and `Mod.tensorπ_comap_balanced` making the comparison maps
  well defined on the coequalizers;
- the linearity of the comparison maps (`Functor.mapModTensorIso_linear`,
  `Mod.comapTensorIso_linear`);
- the coherence axioms of `Functor.CoreMonoidal` (naturality, associativity and unitality of the
  comparison isomorphisms) for `Functor.mapModCoreMonoidal` and `Mod.comapCoreMonoidal`.

All of them are checked after precomposition with the projections onto the coequalizers
(`Mod.tensorπ`), where they reduce to the coherences of `μ F` and of the algebra structures.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory BraidedCategory MonObj Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

namespace Mod

variable {R : C} [MonObj R] [IsCommMonObj R]

/-- A morphism out of the relative tensor product `M ⊗_R N`, from a morphism out of `M ⊗ N`
which is balanced for the two actions of `R`. -/
noncomputable def tensorDesc (M N : Mod C R) {W : C} (k : M.X ⊗ N.X ⟶ W)
    (hk : ((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X ≫ k = ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) ≫ k) :
    (M ⊗ N).X ⟶ W :=
  Cofork.IsColimit.desc (isColimitTensorπ M N) k hk

@[reassoc (attr := simp)]
lemma tensorπ_tensorDesc (M N : Mod C R) {W : C} (k : M.X ⊗ N.X ⟶ W) (hk) :
    tensorπ M N ≫ tensorDesc M N k hk = k := by
  unfold tensorDesc
  exact Cofork.IsColimit.π_desc' (isColimitTensorπ M N) k hk

end Mod

/-! ### Transport of module objects along a braided functor -/

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [HasCoequalizers D] [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

open scoped Obj

namespace Functor

variable (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- The composite `F M ⊗ F N ⟶ F (M ⊗ N) ⟶ F (M ⊗_R N)` is balanced for the two actions of
`F R`, the right action of `F R` on `F M` being `F` of the right action of `R` on `M` since `F`
is braided. -/
lemma mapMod_μ_balanced (M N : Mod C R) :
    ((β_ (F.mapMod.obj M).X (F.obj R)).hom ≫ γ[F.obj R, (F.mapMod.obj M).X]) ▷
        (F.mapMod.obj N).X ≫ LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorπ M N) =
      ((α_ (F.mapMod.obj M).X (F.obj R) (F.mapMod.obj N).X).hom ≫
        (F.mapMod.obj M).X ◁ γ[F.obj R, (F.mapMod.obj N).X]) ≫
          LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorπ M N) :=
  sorry

/-- The composite `F (M ⊗ N) ⟶ F M ⊗ F N ⟶ F M ⊗_{F R} F N` coequalizes the image under `F` of
the parallel pair presenting `M ⊗_R N`. -/
lemma mapMod_δ_balanced (M N : Mod C R) :
    F.map (((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X) ≫ OplaxMonoidal.δ F M.X N.X ≫
        Mod.tensorπ (F.mapMod.obj M) (F.mapMod.obj N) =
      F.map ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) ≫ OplaxMonoidal.δ F M.X N.X ≫
        Mod.tensorπ (F.mapMod.obj M) (F.mapMod.obj N) :=
  sorry

/-- The image under `F` of the coequalizer presenting `M ⊗_R N` is a coequalizer, `F`
preserving coequalizers. -/
noncomputable def isColimitMapTensorπ (M N : Mod C R) :=
  isColimitCoforkMapOfIsColimit F (Mod.tensorπ_condition M N) (Mod.isColimitTensorπ M N)

/-- The comparison `F M ⊗_{F R} F N ≅ F (M ⊗_R N)` of the underlying objects, induced by the
tensorator `μ F M N` on the coequalizers presenting both sides. -/
noncomputable def mapModTensorIsoX (M N : Mod C R) :
    (F.mapMod.obj M ⊗ F.mapMod.obj N).X ≅ (F.mapMod.obj (M ⊗ N)).X where
  hom := Mod.tensorDesc _ _ (LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorπ M N))
    (F.mapMod_μ_balanced M N)
  inv := Cofork.IsColimit.desc (F.isColimitMapTensorπ M N)
    (OplaxMonoidal.δ F M.X N.X ≫ Mod.tensorπ (F.mapMod.obj M) (F.mapMod.obj N))
    (F.mapMod_δ_balanced M N)
  hom_inv_id := by
    rw [← cancel_epi (Mod.tensorπ (F.mapMod.obj M) (F.mapMod.obj N)), Mod.tensorπ_tensorDesc_assoc,
      Category.assoc, Category.comp_id]
    erw [Cofork.IsColimit.π_desc' (F.isColimitMapTensorπ M N)]
    rw [Monoidal.μ_δ_assoc]
  inv_hom_id := by
    refine Cofork.IsColimit.hom_ext (F.isColimitMapTensorπ M N) ?_
    erw [Cofork.IsColimit.π_desc'_assoc (F.isColimitMapTensorπ M N)]
    rw [Category.assoc, Mod.tensorπ_tensorDesc, Monoidal.δ_μ_assoc]
    exact (Category.comp_id _).symm

/-- The comparison `F M ⊗_{F R} F N ⟶ F (M ⊗_R N)` is `F R`-linear. -/
lemma mapModTensorIso_linear (M N : Mod C R) :
    γ[F.obj R, (F.mapMod.obj M ⊗ F.mapMod.obj N).X] ≫ (F.mapModTensorIsoX M N).hom =
      F.obj R ◁ (F.mapModTensorIsoX M N).hom ≫ γ[F.obj R, (F.mapMod.obj (M ⊗ N)).X] :=
  sorry

/-- The comparison isomorphism `F M ⊗_{F R} F N ≅ F (M ⊗_R N)` of `F R`-module objects. -/
noncomputable def mapModTensorIso (M N : Mod C R) :
    F.mapMod.obj M ⊗ F.mapMod.obj N ≅ F.mapMod.obj (M ⊗ N) :=
  Mod.isoMk (F.mapModTensorIsoX M N) (F.mapModTensorIso_linear M N)

@[simp]
lemma mapModTensorIso_hom_hom (M N : Mod C R) :
    (F.mapModTensorIso M N).hom.hom = (F.mapModTensorIsoX M N).hom :=
  rfl

@[reassoc (attr := simp)]
lemma tensorπ_mapModTensorIso_hom_hom (M N : Mod C R) :
    Mod.tensorπ (F.mapMod.obj M) (F.mapMod.obj N) ≫ (F.mapModTensorIso M N).hom.hom =
      LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorπ M N) :=
  Mod.tensorπ_tensorDesc _ _ _ _

/-- The unit comparison `𝟙 ≅ F.mapMod 𝟙`: both are `F R` with its algebra structure. -/
noncomputable def mapModUnitIso :
    𝟙_ (Mod D (F.obj R)) ≅ F.mapMod.obj (𝟙_ (Mod C R)) :=
  Mod.isoMk (Iso.refl (F.obj R)) (by
    change MonObj.mul ≫ 𝟙 _ = _ ◁ 𝟙 _ ≫ (LaxMonoidal.μ F R R ≫ F.map MonObj.mul)
    simp only [Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rfl)

/-- The transport `F.mapMod : Mod C R ⥤ Mod D (F.obj R)` of module objects along a braided
functor preserving coequalizers is strong monoidal for the relative tensor products, with
comparison isomorphisms `Functor.mapModTensorIso` and `Functor.mapModUnitIso`. -/
noncomputable def mapModCoreMonoidal : (F.mapMod (R := R)).CoreMonoidal where
  εIso := F.mapModUnitIso
  μIso := F.mapModTensorIso
  μIso_hom_natural_left := sorry
  μIso_hom_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry

/-- The transport `F.mapMod` of module objects along a braided functor preserving coequalizers
is strong monoidal. -/
noncomputable instance monoidal_mapMod : (F.mapMod (R := R)).Monoidal :=
  F.mapModCoreMonoidal.toMonoidal

lemma mapMod_μ_hom (M N : Mod C R) :
    (LaxMonoidal.μ (F.mapMod (R := R)) M N).hom = (F.mapModTensorIsoX M N).hom :=
  rfl

end Functor

/-! ### Change of scalars along an isomorphism -/

namespace Mod

section Comap

variable {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (ψ : S ⟶ R)
  [IsMonHom ψ] [IsIso ψ]

/-- The projection `M ⊗ N ⟶ M ⊗_R N` is balanced for the two actions of `S` on the
restrictions of scalars of `M` and `N`. -/
lemma tensorπ_comap_balanced (M N : Mod C R) :
    ((β_ ((comap ψ).obj M).X S).hom ≫ γ[S,((comap ψ).obj M).X]) ▷ ((comap ψ).obj N).X ≫
        tensorπ M N =
      ((α_ ((comap ψ).obj M).X S ((comap ψ).obj N).X).hom ≫
        ((comap ψ).obj M).X ◁ γ[S,((comap ψ).obj N).X]) ≫ tensorπ M N :=
  sorry

/-- The projection `M ⊗ N ⟶ M ⊗_S N` of the restrictions of scalars is balanced for the two
actions of `R`, `ψ` being an isomorphism. -/
lemma comap_tensorπ_balanced (M N : Mod C R) :
    ((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X ≫ tensorπ ((comap ψ).obj M) ((comap ψ).obj N) =
      ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) ≫ tensorπ ((comap ψ).obj M) ((comap ψ).obj N) :=
  sorry

/-- The comparison `M ⊗_S N ≅ M ⊗_R N` of the underlying objects for an isomorphism
`ψ : S ⟶ R`: both are coequalizers of parallel pairs out of `M ⊗ S ⊗ N` and `M ⊗ R ⊗ N`
differing by `M ⊗ ψ ⊗ N`, and the comparison is the identity of `M ⊗ N` on the
projections. -/
noncomputable def comapTensorIsoX (M N : Mod C R) :
    ((comap ψ).obj M ⊗ (comap ψ).obj N).X ≅ ((comap ψ).obj (M ⊗ N)).X where
  hom := tensorDesc _ _ (tensorπ M N) (tensorπ_comap_balanced ψ M N)
  inv := tensorDesc M N (tensorπ ((comap ψ).obj M) ((comap ψ).obj N))
    (comap_tensorπ_balanced ψ M N)
  hom_inv_id := by
    rw [← cancel_epi (tensorπ ((comap ψ).obj M) ((comap ψ).obj N)), tensorπ_tensorDesc_assoc]
    erw [tensorπ_tensorDesc]
    rw [Category.comp_id]
  inv_hom_id := by
    rw [← cancel_epi (tensorπ M N), tensorπ_tensorDesc_assoc]
    erw [tensorπ_tensorDesc, Category.comp_id]

/-- The comparison `M ⊗_S N ⟶ M ⊗_R N` is `S`-linear. -/
lemma comapTensorIso_linear (M N : Mod C R) :
    γ[S, ((comap ψ).obj M ⊗ (comap ψ).obj N).X] ≫ (comapTensorIsoX ψ M N).hom =
      S ◁ (comapTensorIsoX ψ M N).hom ≫ γ[S, ((comap ψ).obj (M ⊗ N)).X] :=
  sorry

/-- The comparison isomorphism `ψ^* M ⊗_S ψ^* N ≅ ψ^* (M ⊗_R N)` of `S`-module objects for an
isomorphism `ψ : S ⟶ R` of commutative algebra objects. -/
noncomputable def comapTensorIso (M N : Mod C R) :
    (comap ψ).obj M ⊗ (comap ψ).obj N ≅ (comap ψ).obj (M ⊗ N) :=
  isoMk (comapTensorIsoX ψ M N) (comapTensorIso_linear ψ M N)

@[reassoc (attr := simp)]
lemma tensorπ_comapTensorIso_hom_hom (M N : Mod C R) :
    tensorπ ((comap ψ).obj M) ((comap ψ).obj N) ≫ (comapTensorIso ψ M N).hom.hom =
      tensorπ M N :=
  tensorπ_tensorDesc _ _ _ _

/-- The unit comparison `S ≅ ψ^* R` of `S`-module objects, given by `ψ`. -/
noncomputable def comapUnitIso : 𝟙_ (Mod C S) ≅ (comap ψ).obj (𝟙_ (Mod C R)) :=
  isoMk (asIso ψ) (by
    change MonObj.mul ≫ ψ = S ◁ ψ ≫ (ψ ▷ R ≫ MonObj.mul)
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

/-- Restriction of scalars along an isomorphism `ψ : S ⟶ R` of commutative algebra objects is
strong monoidal for the relative tensor products, with comparison isomorphisms
`Mod.comapTensorIso` and `Mod.comapUnitIso`. -/
noncomputable def comapCoreMonoidal : (comap ψ : Mod C R ⥤ Mod C S).CoreMonoidal where
  εIso := comapUnitIso ψ
  μIso := comapTensorIso ψ
  μIso_hom_natural_left := sorry
  μIso_hom_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry

/-- Restriction of scalars along an isomorphism of commutative algebra objects is strong
monoidal. -/
noncomputable instance monoidal_comap : (comap ψ : Mod C R ⥤ Mod C S).Monoidal :=
  (comapCoreMonoidal ψ).toMonoidal

end Comap

section ExtendScalars

variable [MonoidalClosed C] [HasEqualizers C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]
  [IsIso φ]

/-- Extension of scalars along an isomorphism `φ : R ⟶ S` of commutative algebra objects is
strong monoidal for the relative tensor products: it is the restriction of scalars along `φ⁻¹`
(`Mod.extendScalarsIsoComapInv`), which is strong monoidal (`Mod.monoidal_comap`), and the
monoidal structure is transported along this isomorphism. -/
noncomputable instance monoidal_extendScalars : (extendScalars φ).Monoidal :=
  Functor.Monoidal.transport (extendScalarsIsoComapInv φ).symm

end ExtendScalars

end Mod

end CategoryTheory
