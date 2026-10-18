/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.Algebra.Category.ModuleCat.FlatLazard
public import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality
public import WeilConjectures.CategoryTheory.Abelian.HomologyFilteredColimit
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-!
# The projection map at flat modules placed in degree zero

Let `F : Mod_Λ ⥤ D` be an exact strong monoidal functor to a monoidal Grothendieck abelian
category, preserving flat objects and left adjoint, let `Γ : D ⥤ Mod_Λ` be a left exact functor
whose derived functors `RᵠΓ` commute with filtered colimits, and let `adj : D(F) ⊣ RΓ`. For `E`
bounded below and `M` a flat `Λ`-module, the projection map
`τ_E : RΓ E ⊗ᴸ M[0] ⟶ RΓ (E ⊗ᴸ D(F) M[0])`
(`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`) is an isomorphism
(`CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_of_flat`).

Indeed it is an isomorphism at the unit, hence at the finite free modules `Λ^k`, and both sides,
in a fixed degree `n`, commute with filtered colimits of flat modules: writing `RΓ E` as `Q(L)`
for a K-flat complex `L`, the source is `Hⁿ(L ⊗ M)`; writing `E` as `Q(I)` for a bounded below
complex `I` of injective objects, the target is `Hⁿ(Γ(I ⊗ F M))`, the complex `I ⊗ F M` being a
bounded below complex of `Γ`-acyclic objects. By Lazard's theorem
(`ModuleCat.FinFreeOver.isColimitCocone`), a flat module is a filtered colimit of finite free
modules.
-/

@[expose] public section

universe u u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory

section Biproduct

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  [HasFiniteBiproducts A] [HasFiniteBiproducts B]
  {P R : A ⥤ B} [P.Additive] [R.Additive]

/-- A natural transformation between additive functors is an isomorphism at a finite biproduct
if it is an isomorphism at its summands. -/
lemma NatTrans.isIso_app_biproduct (τ : P ⟶ R) {J : Type} [Finite J] (f : J → A)
    [HasBiproduct f] (h : ∀ j, IsIso (τ.app (f j))) : IsIso (τ.app (⨁ f)) := by
  have e : τ.app (⨁ f) = (P.mapBiproduct f).hom ≫
      (biproduct.mapIso fun j ↦ asIso (τ.app (f j))).hom ≫ (R.mapBiproduct f).inv := by
    rw [← cancel_epi (P.mapBiproduct f).inv]
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    simp [Functor.mapBiproduct, ← R.map_comp]
  rw [e]
  infer_instance

end Biproduct

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The finite free module `R^k` is a biproduct of `k` copies of `R`. -/
noncomputable def finsuppIsoBiproduct (k : ℕ) :
    ModuleCat.of R (Fin k →₀ R) ≅ ⨁ fun _ : Fin k ↦ ModuleCat.of R R :=
  (Finsupp.linearEquivFunOnFinite R R (Fin k)).toModuleIso ≪≫
    (ModuleCat.biproductIsoPi fun _ : Fin k ↦ ModuleCat.of R R).symm

end ModuleCat

namespace Functor

/-- For a complex `L`, the functor `M ↦ L ⊗ M` (tensoring termwise on the right) from `C` to
cochain complexes. -/
@[simps]
noncomputable def tensorRightComplex {C : Type*} [Category* C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] (L : CochainComplex C ℤ) :
    C ⥤ CochainComplex C ℤ where
  obj M := (((curriedTensor C).flip.obj M).mapHomologicalComplex (.up ℤ)).obj L
  map f := (NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map f) (.up ℤ)).app L
  map_id M := by
    ext
    simp
  map_comp f g := by
    ext
    simp

instance {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
    (L : CochainComplex C ℤ) (n : ℤ) [MonoidalClosed C] (J : Type*) [Category* J] :
    PreservesColimitsOfShape J (tensorRightComplex L ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
  preservesColimitsOfShape_of_natIso (F := tensorLeft (L.X n)) (NatIso.ofComponents
    (fun _ ↦ Iso.refl _) (by intros; simp))

instance {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
    [MonoidalClosed C] (L : CochainComplex C ℤ) (J : Type*) [Category* J] :
    PreservesColimitsOfShape J (tensorRightComplex L) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun _ ↦ inferInstance

end Functor

end CategoryTheory
