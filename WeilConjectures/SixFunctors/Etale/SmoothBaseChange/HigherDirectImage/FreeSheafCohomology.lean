/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.Curve.Reductions
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure

import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

/-!
# Free sheaves under extension by zero and pullback, and cohomology

For an étale `v : V ⟶ Y`, extension by zero sends the free sheaf `Λ[T]` on an étale
`V`-scheme `T` to the free sheaf on `T → V → Y`, and the derived adjunction `v_! ⊣ v^*`
identifies `Hom((v_! M)[0], N[0]⟦q⟧)` with `Hom(M[0], (v^* N)[0]⟦q⟧)`. Combined with
`h^* Λ[W] ≅ Λ[W ×_X Y]`, this computes `Hom((h^* Λ[W])[0], N[0]⟦q⟧)` as the étale cohomology
`Hᵠ(W ×_X Y, N|)` of the scheme `W ×_X Y`. The file also states that étale cohomology of a
quasi-compact quasi-separated scheme commutes with filtered colimits.

## Main definitions

- `AlgebraicGeometry.Etale.etaleLowerShriekFreeSheafIso`: `v_! Λ[T] ≅ Λ[T → V → Y]`.
- `AlgebraicGeometry.Etale.shiftedHomFunctor`: the functor `N ↦ Hom(A[0], N[0]⟦q⟧)`.
- `AlgebraicGeometry.Etale.etaleLowerShriekShiftedHomIso`: the derived adjunction `v_! ⊣ v^*`
  on shifted maps out of a sheaf in degree `0`.
- `AlgebraicGeometry.Etale.shiftedHomFunctorUpperStarFreeSheafIso`:
  `Hom((h^* Λ[W])[0], N[0]⟦q⟧) ≅ Hᵠ(W ×_X Y, N|)`.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_H_forget₂_succ_of_injective`: on a quasi-compact
  quasi-separated scheme, injective sheaves of `Λ`-modules have acyclic underlying abelian sheaves.
- `AlgebraicGeometry.Etale.shiftedHomFunctorFreeSheafIso`: on such a scheme,
  `Hom(Λ_Z[0], N[0]⟦n⟧)` is the cohomology of the underlying abelian sheaf of `N`.
- `AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject`:
  étale cohomology of a quasi-compact quasi-separated scheme commutes with filtered colimits.
-/

@[expose] public section

universe u w

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

open Scheme Etale

section FreeSheaf

variable {X Y : Scheme.{u}}

end FreeSheaf

section Restriction

variable {Y V : Scheme.{u}} (v : V ⟶ Y) (hv : Etale v)

end Restriction

section Acyclicity

open Presheaf

variable {C : Type (u + 1)} [Category.{u} C] (P : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ)

/-- The presheaf of `Λ`-modules `Y ↦ ∏_{W, g : W ⟶ Y} P(W)`, with restriction by precomposition:
the `Λ`-linear version of `CategoryTheory.Presheaf.cofree`. -/
noncomputable def Etale.moduleCofree : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj Y := ModuleCat.of Λ (∀ (W : C) (_ : W ⟶ Y.unop), P.obj (op W))
  map {Y Y'} h := ModuleCat.ofHom
    { toFun c W g := c W (g ≫ h.unop)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id _ := by
    ext
    simp
  map_comp _ _ := by
    ext
    simp

/-- The embedding of a presheaf of `Λ`-modules into its cofree presheaf, `p ↦ (g ↦ P(g) p)`. -/
noncomputable def Etale.toModuleCofree : P ⟶ Etale.moduleCofree Λ P where
  app Y := ModuleCat.ofHom
    { toFun p W g := P.map g.op p
      map_add' _ _ := funext fun _ ↦ funext fun _ ↦ map_add _ _ _
      map_smul' _ _ := funext fun _ ↦ funext fun _ ↦ map_smul _ _ _ }
  naturality Y Y' h := by
    refine ModuleCat.hom_ext (LinearMap.ext fun p ↦ funext fun W ↦ funext fun g ↦ ?_)
    change P.map g.op (P.map h p) = P.map (g ≫ h.unop).op p
    rw [op_comp, P.map_comp]
    rfl

instance : Mono (Etale.toModuleCofree Λ P) := by
  have (Y : Cᵒᵖ) : Mono ((Etale.toModuleCofree Λ P).app Y) :=
    (ModuleCat.mono_iff_injective _).2 fun p p' h ↦ by
      have := congrFun (congrFun h Y.unop) (𝟙 _)
      change P.map (𝟙 _).op p = P.map (𝟙 _).op p' at this
      simpa using this
  exact NatTrans.mono_of_mono_app _


/-- The Čech complexes of the underlying abelian presheaf of an injective presheaf of
`Λ`-modules are exact in positive degrees: it is a retract of the cofree abelian presheaf, as
the presheaf of `Λ`-modules is a retract of its `Λ`-linear cofree presheaf. -/
lemma Etale.exactAt_cechComplex_forget₂_of_injective [Injective P] {V : C}
    [HasFiniteProducts (Over V)] {ι : Type*} (U : ι → Over V) (q : ℕ) :
    ((cechComplex U).obj (P ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).ExactAt
      (q + 1) := by
  let r := Injective.factorThru (𝟙 P) (Etale.toModuleCofree Λ P)
  have hr : Etale.toModuleCofree Λ P ≫ r = 𝟙 P := Injective.comp_factorThru _ _
  let b : cofree (P ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⟶
      P ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
    { app Y := AddCommGrpCat.ofHom
        (show (∀ (W : C) (_ : W ⟶ Y.unop), P.obj (op W)) →+ P.obj Y from
          (r.app Y).hom.toAddMonoidHom)
      naturality Y Y' h := by
        ext c
        exact ConcreteCategory.congr_hom (r.naturality h) c }
  have hab : toCofree _ ≫ b = 𝟙 _ := by
    ext Y p
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hr Y) p
  set ι' := (cechComplex U).map
    (toCofree (P ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
  set ρ := (cechComplex U).map b
  have hιρ (k : ℕ) (c : ((cechComplex U).obj
      (P ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).X k) : ρ.f k (ι'.f k c) = c := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, hab,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ConcreteCategory.id_apply]
  rw [exactAt_cechComplex_iff]
  intro c hc
  obtain ⟨b', hb'⟩ := (exactAt_cechComplex_iff U _ q).1 (exactAt_cechComplex_cofree U _ q)
    (ι'.f (q + 1) c) ((ConcreteCategory.congr_hom (ι'.comm (q + 1) (q + 2)) c).trans
        ((congrArg (ι'.f (q + 2)) hc).trans (map_zero _)))
  exact ⟨ρ.f q b', (ConcreteCategory.congr_hom (ρ.comm q (q + 1)) b').trans
    ((congrArg (ρ.f (q + 1)) hb').trans (hιρ _ c))⟩

end Acyclicity

section Comparison

variable {Z : Scheme.{u}}

variable (Z) in
attribute [local instance] Abelian.Ext.subsingleton_of_injective in
end Comparison

end AlgebraicGeometry
