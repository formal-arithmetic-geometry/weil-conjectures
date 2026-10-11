/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The homology of the derived single functor on maps of complexes

The canonical isomorphism `H⁰(A[0]) ≅ A` of `DerivedCategory.singleFunctorCompHomologyFunctorIso`
computes the map induced in degree-`0` homology by a morphism of complexes
`f : A[0] ⟶ M`: it is the map `A ⟶ Z⁰(M) ⟶ H⁰(M)` induced by `f` on cycles, up to the
isomorphism `DerivedCategory.singleCyclesHom A : A ≅ Z⁰(A[0])`, which is natural in `A`.

## Main definitions

- `DerivedCategory.singleCyclesHom`: the isomorphism `A ⟶ Z⁰(A[0])`.

## Main statements

- `DerivedCategory.singleFunctorCompHomologyFunctorIso_inv_app_comp_map_Q_map`:
  the degree-`0` homology of `Q(f)` for `f : A[0] ⟶ M`, computed on cycles.
- `DerivedCategory.exists_ne_zero_hom_singleFunctor_obj`: an object with nonzero `H⁰` has a
  nonzero map to `I[0]` for an injective coseparator `I`.
-/

@[expose] public section

open CategoryTheory

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The degree-`0` homology of `Q(f)` for `f : A[0] ⟶ M`, through `homologyMap f 0`. -/
lemma singleFunctorCompHomologyFunctorIso_inv_app_comp_map_Q_map_homologyMap
    {A : C} {M : CochainComplex C ℤ} (f : (CochainComplex.singleFunctor C 0).obj A ⟶ M) :
    (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
      (homologyFunctor C 0).map (Q.map f) =
    ((singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
      (homologyFunctorFactors C 0).hom.app _) ≫
      HomologicalComplex.homologyMap f 0 ≫ (homologyFunctorFactors C 0).inv.app M := by
  have := (homologyFunctorFactors C 0).hom.naturality f
  simp only [Functor.comp_map] at this
  simp only [Category.assoc]
  congr 1
  erw [← reassoc_of% this, Iso.hom_inv_id_app, Category.comp_id]

/-- The isomorphism `A ≅ Z⁰(A[0])` from an object to the degree-`0` cycles of the single
complex, through which the homology of the derived single functor is computed. -/
noncomputable def singleCyclesHom (A : C) :
    A ⟶ ((HomologicalComplex.single C (.up ℤ) 0).obj A).cycles 0 :=
  (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
    (homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso _ 0 A).hom ≫
        (HomologicalComplex.singleObjCyclesSelfIso _ 0 A).inv

instance (A : C) : IsIso (singleCyclesHom A) := by
  dsimp [singleCyclesHom]; infer_instance

/-- The degree-`0` homology of `Q(f)` for `f : A[0] ⟶ M` is the map induced on cycles, followed
by `Z⁰(M) ⟶ H⁰(M)`. -/
lemma singleFunctorCompHomologyFunctorIso_inv_app_comp_map_Q_map
    {A : C} {M : CochainComplex C ℤ} (f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ M) :
    (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
      (homologyFunctor C 0).map (Q.map f) =
    singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0 ≫ M.homologyπ 0 ≫
      (homologyFunctorFactors C 0).inv.app M := by
  rw [singleFunctorCompHomologyFunctorIso_inv_app_comp_map_Q_map_homologyMap f]
  simp only [singleCyclesHom, Category.assoc]
  congr 2
  rw [← cancel_epi (((HomologicalComplex.single C (.up ℤ) 0).obj A).homologyπ 0),
    HomologicalComplex.homologyπ_naturality_assoc]
  simp

/-- `DerivedCategory.singleCyclesHom` is natural. -/
lemma singleCyclesHom_naturality {A A' : C} (φ : A' ⟶ A) :
    singleCyclesHom A' ≫ HomologicalComplex.cyclesMap
      ((HomologicalComplex.single C (.up ℤ) 0).map φ) 0 = φ ≫ singleCyclesHom A := by
  have h₁ := (singleFunctorCompHomologyFunctorIso C 0).inv.naturality φ
  have h₂ := (homologyFunctorFactors C 0).hom.naturality
    ((HomologicalComplex.single C (.up ℤ) 0).map φ)
  simp only [Functor.id_map, Functor.comp_map] at h₁ h₂
  simp only [singleCyclesHom, Category.assoc,
    HomologicalComplex.singleObjCyclesSelfIso_inv_naturality]
  rw [← HomologicalComplex.singleObjHomologySelfIso_hom_naturality_assoc, reassoc_of% h₁]
  erw [reassoc_of% h₂]
  rfl



/-- A morphism of complexes `K ⟶ I[0]` built from a map `ψ : H⁰(K) ⟶ I` to an injective object:
extend `ψ` along `H⁰(K) ⟶ coker(d⁻¹)` and precompose with `K⁰ ⟶ coker(d⁻¹)`. -/
noncomputable def homToSingleOfHomology (K : CochainComplex C ℤ) {I : C} [Injective I]
    (ψ : K.homology 0 ⟶ I) : K ⟶ (HomologicalComplex.single C (.up ℤ) 0).obj I :=
  HomologicalComplex.mkHomToSingle (K.pOpcycles 0 ≫ Injective.factorThru ψ (K.homologyι 0))
    (fun i _ ↦ by rw [HomologicalComplex.d_pOpcycles_assoc, Limits.zero_comp])

omit [HasDerivedCategory C] in
lemma iCycles_comp_homToSingleOfHomology_f (K : CochainComplex C ℤ) {I : C} [Injective I]
    (ψ : K.homology 0 ⟶ I) :
    K.iCycles 0 ≫ (homToSingleOfHomology K ψ).f 0 =
      K.homologyπ 0 ≫ ψ ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 I).inv := by
  simp [homToSingleOfHomology, ← HomologicalComplex.homology_π_ι_assoc]

/-- If `ψ : H⁰(K) ⟶ I` is nonzero, so is the morphism `Q(K) ⟶ I[0]` of the derived category
induced by `DerivedCategory.homToSingleOfHomology`: its degree-`0` homology is `ψ`. -/
lemma Q_map_homToSingleOfHomology_ne_zero (K : CochainComplex C ℤ) {I : C} [Injective I]
    {ψ : K.homology 0 ⟶ I} (hψ : ψ ≠ 0) : Q.map (homToSingleOfHomology K ψ) ≠ 0 := by
  intro h
  let M := (HomologicalComplex.single C (.up ℤ) 0).obj I
  have hM : IsIso (M.homologyπ 0) := M.isIso_homologyπ (-1) 0 (by simp) (by simp [M])
  have h₁ : HomologicalComplex.homologyMap (homToSingleOfHomology K ψ) 0 = 0 := by
    have := (homologyFunctorFactors C 0).hom.naturality (homToSingleOfHomology K ψ)
    simp only [Functor.comp_map, h, Functor.map_zero, Limits.zero_comp] at this
    simpa using (((homologyFunctorFactors C 0).app K).inv ≫= this).symm
  have h₂ : HomologicalComplex.cyclesMap (homToSingleOfHomology K ψ) 0 = 0 := by
    rw [← cancel_mono (M.homologyπ 0), Limits.zero_comp,
      ← HomologicalComplex.homologyπ_naturality, h₁, Limits.comp_zero]
  apply hψ
  rw [← cancel_epi (K.homologyπ 0), ← cancel_mono
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 I).inv, Limits.comp_zero, Limits.zero_comp,
    Category.assoc, ← iCycles_comp_homToSingleOfHomology_f, ← HomologicalComplex.cyclesMap_i,
    h₂, Limits.zero_comp]

/-- An object `K` of the derived category with `H⁰(K) ≠ 0` has a nonzero morphism to `I[0]`
for every injective coseparator `I`. -/
lemma exists_ne_zero_hom_singleFunctor_obj (K : DerivedCategory C) {I : C} [Injective I]
    (hI : IsCoseparator I) (hK : ¬ Limits.IsZero ((homologyFunctor C 0).obj K)) :
    ∃ φ : K ⟶ (singleFunctor C 0).obj I, φ ≠ 0 := by
  obtain ⟨K', ⟨e⟩⟩ : ∃ K', Nonempty (Q.obj K' ≅ K) := ⟨_, ⟨Q.objObjPreimageIso K⟩⟩
  have hK' : ¬ Limits.IsZero (K'.homology 0) := fun h ↦
    hK (h.of_iso (((homologyFunctorFactors C 0).app K').symm ≪≫
      (homologyFunctor C 0).mapIso e).symm)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : K'.homology 0 ⟶ I, ψ ≠ 0 := by
    by_contra! h
    exact hK' ((Limits.IsZero.iff_id_eq_zero _).2 (hI.def _ _ fun ψ ↦ by simp [h ψ]))
  refine ⟨e.inv ≫ Q.map (homToSingleOfHomology K' ψ), fun h ↦ ?_⟩
  exact Q_map_homToSingleOfHomology_ne_zero K' hψ (by simpa using e.hom ≫= h)

end DerivedCategory
