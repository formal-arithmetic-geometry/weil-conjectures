/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-! # Upper cohomological bounds reflected by Nakayama

Source: current blueprint, sk-lem-finite.proof.md, integral Complement, top-cohomology
Nakayama argument (blueprint: lem-sf-derived-nakayama-upper-bound).
-/

@[expose] public section
set_option autoImplicit false
universe v u
open CategoryTheory MonoidalCategory MonObj Limits
namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

private theorem top_reduction_zero (K : DerivedCategory (Mod C R)) (b : ℤ)
    [K.IsLE b] (a : ℤ) (hab : a < b)
    [((extendScalars φ).leftDerivedFunctor.obj K).IsLE a] :
    IsZero ((extendScalars φ).obj ((DerivedCategory.homologyFunctor _ b).obj K)) := by
  obtain ⟨L, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  have : (L.truncGE b).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact IsZero.of_epi ((L.πTruncGE b).f i) (L.isZero_of_isStrictlyLE b i hi)
  obtain ⟨A, ⟨e'⟩⟩ := (L.truncGE b).exists_iso_single b
  let π : L ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj A :=
    L.πTruncGE b ≫ e'.hom
  have : IsIso (HomologicalComplex.homologyMap π b) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  let eA : (DerivedCategory.homologyFunctor _ b).obj K ≅ A :=
    (DerivedCategory.homologyFunctor _ b).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ b).app L ≪≫
      asIso (HomologicalComplex.homologyMap π b) ≪≫
      HomologicalComplex.singleObjHomologySelfIso _ b A
  refine IsZero.of_iso ?_ ((extendScalars φ).mapIso eA)
  let adj := extendRestrictAdjunction φ
  suffices hη : adj.unit.app A = 0 by
    rw [IsZero.iff_id_eq_zero, ← adj.left_triangle_components A, hη, Functor.map_zero,
      zero_comp]
  let g := (HomologicalComplex.single _ (ComplexShape.up ℤ) b).map (adj.unit.app A)
  have hQ : DerivedCategory.Q.map (π ≫ g) = 0 := by
    let X := DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (comap φ) (ComplexShape.up ℤ) b).inv.app
          ((extendScalars φ).obj A)) ≫
      (comap φ).mapDerivedCategoryFactors.inv.app
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj ((extendScalars φ).obj A))
    let f := e.hom ≫ DerivedCategory.Q.map (π ≫ g) ≫ X
    have hf : f = 0 := by
      let adj' := derivedExtendMapDerivedCategoryAdjunction φ
      have hz : (adj'.homEquiv _ _).symm f = 0 :=
        DerivedCategory.TStructure.t.zero _ a b hab
      rw [← (adj'.homEquiv _ _).apply_symm_apply f, hz,
        Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
    rw [← cancel_epi e.hom, ← cancel_mono X, Limits.comp_zero, Limits.zero_comp,
      Category.assoc]
    exact hf
  have h1 := DerivedCategory.homologyFunctorFactors_hom_naturality (π ≫ g) b
  rw [hQ, Functor.map_zero, Limits.zero_comp, HomologicalComplex.homologyMap_comp] at h1
  have h2 : HomologicalComplex.homologyMap g b = 0 := by
    rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ b).hom.app L ≫
      HomologicalComplex.homologyMap π b), Limits.comp_zero, Category.assoc, ← h1]
  have h3 := HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℤ) b
    (adj.unit.app A)
  rw [h2, Limits.zero_comp] at h3
  rw [← cancel_epi (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) b A).hom,
    Limits.comp_zero]
  exact h3.symm

/-- Extension of scalars reflects upper bounds on bounded-above complexes whose
cohomology satisfies an abelian Nakayama criterion.

Source: the top-cohomology argument in the integral clause of the blueprint
sk-lem-finite.proof.md; the truncation argument of derived extension-of-scalars Nakayama.

Proof: if n is above the proposed bound, the adjoint of the map from K to its top
cohomology tensored with S vanishes by t-structure orthogonality. Taking degree n
homology shows that S tensor H^n(K) is zero. Abelian Nakayama kills H^n(K), lowering
the upper bound by one. Descending induction from any existing upper bound reaches
b. The induction keeps the bound max(b,n), so it also handles an initial bound below b.
(blueprint: lem-sf-derived-nakayama-upper-bound)
-/
theorem isLE_of_leftDerivedFunctor_extendScalars_isLE
    (P : ObjectProperty (Mod C R))
    (hP : ∀ M, P M → IsZero ((extendScalars φ).obj M) → IsZero M)
    (K : DerivedCategory (Mod C R)) (hK : DerivedCategory.TStructure.t.minus K)
    (hKP : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor _ n).obj K))
    (b : ℤ) [((extendScalars φ).leftDerivedFunctor.obj K).IsLE b] : K.IsLE b := by
  obtain ⟨c, hc⟩ := hK
  have step (n : ℤ) (hn : K.IsLE (max b n)) : K.IsLE (max b (n - 1)) := by
    by_cases hbn : b < n
    · have hn' : K.IsLE n := by simpa only [max_eq_right hbn.le] using hn
      have hz : IsZero ((DerivedCategory.homologyFunctor _ n).obj K) :=
        hP _ (hKP n) (top_reduction_zero φ K n b hbn)
      have hlow : K.IsLE (n - 1) := by
        rw [DerivedCategory.isLE_iff]
        intro i hi
        rcases eq_or_lt_of_le (show n ≤ i by omega) with rfl | hni
        · exact hz
        · exact DerivedCategory.isZero_of_isLE K n i hni
      exact DerivedCategory.TStructure.t.isLE_of_le K (n - 1) (max b (n - 1))
        (le_max_right _ _)
    · simpa only [max_eq_left (by omega : n ≤ b),
        max_eq_left (by omega : n - 1 ≤ b)] using hn
  have hb : K.IsLE (max b c) := by
    have : K.IsLE c := hc
    exact DerivedCategory.TStructure.t.isLE_of_le K c (max b c) (le_max_right _ _)
  have hdesc : ∀ n : ℤ, n ≤ c → K.IsLE (max b n) :=
    Int.leInductionDown hb (fun n _ hn ↦ step n hn)
  simpa only [max_eq_left (min_le_left b c)] using hdesc (min b c) (min_le_right _ _)

end CategoryTheory.Mod
