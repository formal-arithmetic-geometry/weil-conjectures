/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective

/-!
# Morphisms out of an object placed in the lowest degree

Let `X` be an object of the derived category `D(C)` of an abelian category `C` whose homology
vanishes in degrees `< n`. For every object `M` of `C`, taking `n`-th homology is a surjection
from morphisms `M[-n] ⟶ X` in `D(C)` onto morphisms `M ⟶ Hⁿ(X)` in `C`
(`DerivedCategory.surjective_homSingleToHomology_of_isGE`).

We also record that a distinguished triangle `T` whose first morphism induces isomorphisms on
the `n`-th and `(n+1)`-st homology, after applying an exact functor `F`, has a third object
whose `n`-th homology is killed by `F`
(`DerivedCategory.isZero_map_homologyFunctor_obj₃_of_isIso`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If the homology of `X` vanishes in degrees `< n`, every morphism `M ⟶ Hⁿ(X)` is the
`n`-th homology of a morphism `M[-n] ⟶ X`: represent `X` by a complex `L` with `Lⁱ = 0` for
`i < n`, whose `n`-th homology is the object of cycles in degree `n`. -/
lemma surjective_homSingleToHomology_of_isGE (M : C) (n : ℤ) (X : DerivedCategory C)
    [X.IsGE n] : Function.Surjective (homSingleToHomology M n X) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE n
  intro g
  have hd : L.d (n - 1) n = 0 := (L.isZero_of_isStrictlyGE n (n - 1) (by omega)).eq_of_src _ _
  have : IsIso (L.homologyπ n) := L.isIso_homologyπ (n - 1) n (by simp) hd
  let t := (g ≫ (homologyFunctor C n).map e.hom ≫ (homologyFunctorFactors C n).hom.app L) ≫
    inv (L.homologyπ n)
  have ht (j : ℤ) (_ : (ComplexShape.up ℤ).Rel n j) : (t ≫ L.iCycles n) ≫ L.d n j = 0 := by
    simp
  refine ⟨Q.map (HomologicalComplex.mkHomFromSingle (t ≫ L.iCycles n) ht) ≫ e.inv, ?_⟩
  rw [homSingleToHomology_comp, ← cancel_mono ((homologyFunctor C n).map e.hom),
    Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id,
    ← cancel_mono ((homologyFunctorFactors C n).hom.app L),
    homSingleToHomology_Q_map_mkHomFromSingle]
  have : L.liftCycles (t ≫ L.iCycles n) (n + 1) (by simp) (ht _ rfl) = t := by
    rw [← cancel_mono (L.iCycles n), HomologicalComplex.liftCycles_i]
  rw [this]
  simp [t]

/-- If the homology of `X` vanishes in degrees `< n` and `Hⁿ(X)` receives a nonzero morphism
from `M`, then there is a nonzero morphism `M[-n] ⟶ X`. -/
lemma exists_ne_zero_hom_singleFunctor_of_isGE {M : C} {n : ℤ} {X : DerivedCategory C}
    [X.IsGE n] (φ : M ⟶ (homologyFunctor C n).obj X) (hφ : φ ≠ 0) :
    ∃ g : (singleFunctor C n).obj M ⟶ X, g ≠ 0 := by
  obtain ⟨g, rfl⟩ := surjective_homSingleToHomology_of_isGE M n X φ
  refine ⟨g, fun h ↦ hφ ?_⟩
  simp [h, homSingleToHomology]

/-- Let `T` be a distinguished triangle of `D(C)` and `F : C ⥤ D` an exact functor. If `F`
turns the maps `Hⁿ(T.mor₁)` and `Hⁿ⁺¹(T.mor₁)` into isomorphisms, then `F(Hⁿ(T.obj₃)) = 0`, by
the exactness of `F(Hⁿ(T.obj₂)) ⟶ F(Hⁿ(T.obj₃)) ⟶ F(Hⁿ⁺¹(T.obj₁))`. -/
lemma isZero_map_homologyFunctor_obj₃_of_isIso {D : Type*} [Category* D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : Pretriangulated.Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n : ℤ)
    (h₀ : IsIso (F.map ((homologyFunctor C n).map T.mor₁)))
    (h₁ : IsIso (F.map ((homologyFunctor C (n + 1)).map T.mor₁))) :
    IsZero (F.obj ((homologyFunctor C n).obj T.obj₃)) := by
  refine ((HomologySequence.exact₃ T hT n (n + 1)).map F).isZero_of_both_zeros ?_ ?_
  · rw [← cancel_epi (F.map ((homologyFunctor C n).map T.mor₁)), comp_zero]
    simp only [ShortComplex.map_f, ← F.map_comp, ← Functor.map_comp,
      Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero]
  · rw [← cancel_mono (F.map ((homologyFunctor C (n + 1)).map T.mor₁)), zero_comp]
    simp only [ShortComplex.map_g, ← F.map_comp, HomologySequence.δ_comp T hT n (n + 1),
      Functor.map_zero]

end DerivedCategory
