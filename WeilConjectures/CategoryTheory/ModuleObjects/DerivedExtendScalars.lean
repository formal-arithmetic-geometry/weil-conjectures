/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

/-!

# The derived extension of scalars

Let `C` be a closed symmetric monoidal Grothendieck abelian category with functorial flat
resolutions, as in `WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`, and let
`φ : R ⟶ S` be a morphism of commutative algebra objects of `C`. Extension of scalars
`S ⊗_R - : Mod C R ⥤ Mod C S` is right exact but not exact, and its *derived* version is the
total left derived functor
```
S ⊗ᴸ_R - = L(extendScalars φ) : D(Mod_R(C)) ⥤ D(Mod_S(C)),
```
computed by applying `S ⊗_R -` to a K-flat resolution. It is the generic
`Functor.leftDerivedFunctor` of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`
applied to `Mod.extendScalars φ`; the only functor-specific input is that extension of scalars
preserves quasi-isomorphisms between K-flat complexes (`Mod.preservesKFlatQuasiIso`).

Restriction of scalars `Mod.comap φ : Mod C S ⥤ Mod C R` is exact (kernels and cokernels of
module objects are computed in `C` on both sides, `Mod.preservesFiniteLimits_comap` and
`Mod.preservesFiniteColimits_comap`), so its right derived functor is the levelwise functor
`(comap φ).mapDerivedCategory` (`Mod.rightDerivedComapIsoMapDerivedCategory`). The adjunction
between extension and restriction of scalars derives to the adjunction
```
S ⊗ᴸ_R - ⊣ D(comap φ)
```
(`Mod.derivedExtendRestrictAdjunction`, `Mod.derivedExtendMapDerivedCategoryAdjunction`).

## The key input

`Mod.preservesKFlatQuasiIso`: if `f : K ⟶ L` is a quasi-isomorphism between K-flat complexes of
`R`-modules, then `S ⊗_R f` is a quasi-isomorphism. It suffices that `S ⊗_R P` is acyclic for
every acyclic K-flat complex `P` (`Functor.PreservesKFlatQuasiIso.mk'`). Restricted to `R`,
`S ⊗_R P` is the relative tensor product of the `R`-module `S` with `P`
(`Mod.extendScalarsCompComapIso`), which is acyclic since `P` is K-flat and acyclic
(`CochainComplex.acyclic_tensorRight_of_kFlat`); restriction of scalars is exact and faithful,
hence detects acyclicity.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

/-! ### Exactness of restriction of scalars -/

section Exact

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]
  [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]

/-- Restriction of scalars is left exact: limits of module objects are computed in `C` on
both sides. -/
instance preservesFiniteLimits_comap : PreservesFiniteLimits (comap φ : Mod C S ⥤ Mod C R) where
  preservesFiniteLimits J _ _ :=
    have : PreservesLimitsOfShape J ((comap φ : Mod C S ⥤ Mod C R) ⋙ forget R) :=
      inferInstanceAs (PreservesLimitsOfShape J (forget S : Mod C S ⥤ C))
    have : ReflectsLimitsOfShape J (forget R : Mod C R ⥤ C) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    preservesLimitsOfShape_of_reflects_of_preserves (comap φ) (forget R)

/-- Restriction of scalars is right exact: colimits of module objects are computed in `C` on
both sides. -/
instance preservesFiniteColimits_comap :
    PreservesFiniteColimits (comap φ : Mod C S ⥤ Mod C R) where
  preservesFiniteColimits J _ _ :=
    have : PreservesColimitsOfShape J ((comap φ : Mod C S ⥤ Mod C R) ⋙ forget R) :=
      inferInstanceAs (PreservesColimitsOfShape J (forget S : Mod C S ⥤ C))
    have : ReflectsColimitsOfShape J (forget R : Mod C R ⥤ C) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    preservesColimitsOfShape_of_reflects_of_preserves (comap φ) (forget R)

end Exact

/-! ### Restricted extension of scalars as a tensor product -/

section TensorRegular

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [IsCommMonObj R] in
/-- The right action of `R` on `S` through `φ`, written with the braiding, is
`s ⊗ r ↦ s φ(r)` since `S` is commutative. -/
lemma braiding_comap_regular_smul :
    (β_ ((comap φ).obj (regular S)).X R).hom ≫ γ[R, ((comap φ).obj (regular S)).X] =
      S ◁ φ ≫ μ[S] := by
  change (β_ S R).hom ≫ φ ▷ S ≫ μ[S] = _
  rw [← braiding_naturality_right_assoc, IsCommMonObj.mul_comm]

variable (M : Mod C R)

/-- The underlying objects of `S ⊗_R M` (extension of scalars) and of the relative tensor
product of `R`-modules `S ⊗_R M` agree: both are coequalizers of the same parallel pair. -/
noncomputable def extendScalarsObjIsoTensorX :
    ((comap φ).obj (extendScalarsObj φ M)).X ≅ ((comap φ).obj (regular S) ⊗ M).X where
  hom := extendDescHom φ (tensorObjπ ((comap φ).obj (regular S)) M) (by
    have h := tensorObjπ_condition ((comap φ).obj (regular S)) M
    rw [braiding_comap_regular_smul] at h
    exact h)
  inv := Cofork.IsColimit.desc (isColimitTensorπ ((comap φ).obj (regular S)) M) (extendπ φ M) (by
    rw [braiding_comap_regular_smul]
    exact extendπ_condition φ M)
  hom_inv_id := by
    rw [← cancel_epi (extendπ φ M)]
    erw [extendπ_extendDescHom_assoc, Cofork.IsColimit.π_desc']
    rw [Category.comp_id]
  inv_hom_id := by
    rw [← cancel_epi (tensorObjπ ((comap φ).obj (regular S)) M)]
    erw [Cofork.IsColimit.π_desc'_assoc, extendπ_extendDescHom]
    rw [Category.comp_id]

@[reassoc (attr := simp)]
lemma extendπ_extendScalarsObjIsoTensorX_hom :
    extendπ φ M ≫ (extendScalarsObjIsoTensorX φ M).hom =
      tensorObjπ ((comap φ).obj (regular S)) M :=
  extendπ_extendDescHom _ _ _

lemma extendScalarsObjIsoTensorX_linear :
    γ[R, ((comap φ).obj (extendScalarsObj φ M)).X] ≫ (extendScalarsObjIsoTensorX φ M).hom =
      R ◁ (extendScalarsObjIsoTensorX φ M).hom ≫ γ[R, ((comap φ).obj (regular S) ⊗ M).X] := by
  rw [← cancel_epi (R ◁ extendπ φ M), ← MonoidalCategory.whiskerLeft_comp_assoc,
    extendπ_extendScalarsObjIsoTensorX_hom, whiskerLeft_tensorπ_smul]
  change R ◁ extendπ φ M ≫ φ ▷ _ ≫ γ[S, (extendScalarsObj φ M).X] ≫ _ =
    (α_ R S M.X).inv ≫ (φ ▷ S ≫ μ[S]) ▷ M.X ≫ tensorObjπ ((comap φ).obj (regular S)) M
  rw [whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc,
    extendπ_extendScalarsObjIsoTensorX_hom, associator_inv_naturality_left_assoc,
    comp_whiskerRight_assoc]

/-- **Restricted extension of scalars is a tensor product**: the restriction to `R` of
`S ⊗_R M` is the relative tensor product of the `R`-modules `S` and `M`. -/
noncomputable def extendScalarsCompComapIso :
    extendScalars φ ⋙ comap φ ≅ MonoidalCategory.tensorLeft ((comap φ).obj (regular S)) :=
  NatIso.ofComponents
    (fun M ↦ isoMk (extendScalarsObjIsoTensorX φ M) (extendScalarsObjIsoTensorX_linear φ M))
    fun {M N} f ↦ by
      refine Mod.hom_ext _ _ ?_
      rw [Mod.comp_hom', Mod.comp_hom', ← cancel_epi (extendπ φ M)]
      change extendπ φ M ≫ (extendScalarsMap φ f).hom ≫ _ = _
      simp only [extendπ_extendScalarsMap_assoc, isoMk_hom, homMk_hom,
        extendπ_extendScalarsObjIsoTensorX_hom, extendπ_extendScalarsObjIsoTensorX_hom_assoc]
      exact (tensorObjπ_whiskerLeft f).symm

end TensorRegular

/-! ### The derived extension of scalars -/

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- `ℤ`-indexed colimits of module objects are exact: `Mod C R` is Grothendieck abelian. -/
instance hasExactColimitsOfShape_int : HasExactColimitsOfShape ℤ (Mod C R) :=
  have := AB5OfSize_of_univLE.{0, 0} (Mod C R)
  inferInstance

/-- Extension of scalars sends quasi-isomorphisms between K-flat complexes of `R`-modules to
quasi-isomorphisms; see the module docstring for the argument. -/
/-- Extension of scalars sends acyclic K-flat complexes to acyclic complexes. -/
lemma acyclic_extendScalars_of_kFlat (K : CochainComplex (Mod C R) ℤ)
    (hK : (HomologicalComplex.quasiIso (Mod C R) (.up ℤ)).kFlat K) (hK' : K.Acyclic) :
    (((extendScalars φ).mapHomologicalComplex _).obj K).Acyclic := by
  let := HasDerivedCategory.standard (Mod C R)
  have h := CochainComplex.acyclic_tensorRight_of_kFlat K hK hK' ((comap φ).obj (regular S))
  intro i
  have hi : (((extendScalars φ ⋙ comap φ).mapHomologicalComplex _).obj K).ExactAt i :=
    (h i).of_iso ((NatIso.mapHomologicalComplex (extendScalarsCompComapIso φ ≪≫
      BraidedCategory.tensorLeftIsoTensorRight _) _).app K).symm
  rw [HomologicalComplex.exactAt_iff] at hi ⊢
  exact (ShortComplex.exact_map_iff_of_faithful
    ((((extendScalars φ).mapHomologicalComplex _).obj K).sc i) (comap φ)).1 hi

instance preservesKFlatQuasiIso : (extendScalars φ).PreservesKFlatQuasiIso :=
  Functor.PreservesKFlatQuasiIso.mk' _ (acyclic_extendScalars_of_kFlat φ)

open scoped CategoryTheory.Functor in
/-- The derived extension of scalars `S ⊗ᴸ_R - : D(Mod_R(C)) ⥤ D(Mod_S(C))`, the total left
derived functor of `S ⊗_R -`, computed on K-flat resolutions.

It is not a definition of its own: it is the generic `Functor.leftDerivedFunctor`, written
`L(-)`, applied to `Mod.extendScalars φ`. -/
noncomputable example : DerivedCategory (Mod C R) ⥤ DerivedCategory (Mod C S) :=
  L(extendScalars φ)

/-- The derived adjunction `S ⊗ᴸ_R - ⊣ R(comap φ)` between the derived extension of scalars
and the right derived functor of restriction of scalars. -/
noncomputable def derivedExtendRestrictAdjunction :
    (extendScalars φ).leftDerivedFunctor ⊣ (comap φ).rightDerivedFunctor :=
  (extendRestrictAdjunction φ).derivedAdjunction

/-- Since restriction of scalars is exact, its right derived functor is the levelwise
functor `D(comap φ)`. -/
noncomputable def rightDerivedComapIsoMapDerivedCategory :
    (comap φ : Mod C S ⥤ Mod C R).rightDerivedFunctor ≅ (comap φ).mapDerivedCategory :=
  (comap φ).rightDerivedFunctorIsoMapDerivedCategory

/-- The derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` between the derived extension of scalars
and the levelwise restriction of scalars on the derived categories. -/
noncomputable def derivedExtendMapDerivedCategoryAdjunction :
    (extendScalars φ).leftDerivedFunctor ⊣ (comap φ).mapDerivedCategory :=
  (derivedExtendRestrictAdjunction φ).ofNatIsoRight (rightDerivedComapIsoMapDerivedCategory φ)

end CategoryTheory.Mod
