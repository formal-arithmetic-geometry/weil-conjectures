/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Gluing a complex onto the top degrees of another

Let `α : P ⟶ M` be a morphism of cochain complexes in an abelian category, with `P` strictly
concentrated in degrees `≥ k`, which induces isomorphisms in cohomology in degrees `> k` and an
epimorphism in degree `k`. Then `M` is isomorphic in the derived category to a complex `M'`
containing `P` as a subcomplex which is equal to `M'` in degrees `≥ k`
(`CochainComplex.exists_iso_Q_obj_of_homologyMap`).

This is the replacement of a representative used in the proof of Stacks, Tag 0FPV: the
mapping cone of `α` is acyclic in degrees `≥ k`, hence quasi-isomorphic to its truncation
`C'` in degrees `≤ k - 1`, and `M'` is the mapping cocone of the composite
`C' ⟶ cone(α) ⟶ P[1]`, whose terms are `C'ⁿ ⊕ Pⁿ`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

open DerivedCategory HomComplex

/-- A morphism of complexes induces an isomorphism on `H^i` in the derived category if and only
if it induces an isomorphism on the `i`-th homology. -/
lemma isIso_homologyFunctor_map_Q_map_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) (i : ℤ) :
    IsIso ((homologyFunctor C i).map (Q.map f)) ↔
      IsIso (HomologicalComplex.homologyMap f i) :=
  NatIso.isIso_map_iff (homologyFunctorFactors C i) f

/-- A morphism of complexes induces an epimorphism on `H^i` in the derived category if and only
if it induces an epimorphism on the `i`-th homology. -/
lemma epi_homologyFunctor_map_Q_map_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) (i : ℤ) :
    Epi ((homologyFunctor C i).map (Q.map f)) ↔
      Epi (HomologicalComplex.homologyMap f i) := by
  have h₁ := NatIso.naturality_1 (homologyFunctorFactors C i) f
  have h₂ := NatIso.naturality_2 (homologyFunctorFactors C i) f
  constructor
  · intro h
    have : Epi ((Q ⋙ homologyFunctor C i).map f) := h
    change Epi ((HomologicalComplex.homologyFunctor C (.up ℤ) i).map f)
    rw [← h₁]
    infer_instance
  · intro (_ : Epi ((HomologicalComplex.homologyFunctor C (.up ℤ) i).map f))
    change Epi ((Q ⋙ homologyFunctor C i).map f)
    rw [← h₂]
    infer_instance

/-- If `α : P ⟶ M` induces epimorphisms in cohomology in degrees `≥ k` and monomorphisms in
degrees `> k`, then its mapping cone is acyclic in degrees `≥ k`. -/
lemma isLE_mappingCone_of_homologyMap {P M : CochainComplex C ℤ} (α : P ⟶ M) (k : ℤ)
    (h₁ : ∀ i, k < i → Mono ((homologyFunctor C i).map (Q.map α)))
    (h₂ : ∀ i, k ≤ i → Epi ((homologyFunctor C i).map (Q.map α))) :
    (mappingCone α).IsLE (k - 1) := by
  let T := Q.mapTriangle.obj (mappingCone.triangle α)
  have hT : T ∈ distTriang _ := mappingCone_triangle_distinguished α
  rw [isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine IsZero.of_iso ?_ ((homologyFunctorFactors C i).app (mappingCone α)).symm
  have hk : k ≤ i := by lia
  have e₁ : (homologyFunctor C i).map T.mor₂ = 0 :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 (h₂ i hk)
  have e₂ : HomologySequence.δ T i (i + 1) = 0 :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1)).1 (h₁ (i + 1) (by lia))
  exact (HomologySequence.exact₃ T hT i (i + 1)).isZero_X₂ e₁ e₂

/-- **Gluing.** Let `α : P ⟶ M` be a morphism of cochain complexes with `P` strictly concentrated
in degrees `≥ k`, inducing isomorphisms in cohomology in degrees `> k` and an epimorphism in
degree `k`. Then there are a complex `M'` isomorphic to `M` in the derived category and a
degreewise monomorphism `j : P ⟶ M'` which is an isomorphism in degrees `≥ k`. -/
theorem exists_iso_Q_obj_of_homologyMap {P M : CochainComplex C ℤ} (α : P ⟶ M) (k : ℤ)
    (h₁ : ∀ i, k < i → IsIso ((homologyFunctor C i).map (Q.map α)))
    (h₂ : Epi ((homologyFunctor C k).map (Q.map α))) :
    ∃ (M' : CochainComplex C ℤ) (j : P ⟶ M'), (∀ i, Mono (j.f i)) ∧
      (∀ i, k ≤ i → IsIso (j.f i)) ∧ Nonempty (Q.obj M' ≅ Q.obj M) := by
  have hC := isLE_mappingCone_of_homologyMap α k (fun i hi ↦ by have := h₁ i hi; infer_instance)
    (fun i hi ↦ by
      obtain rfl | hi := eq_or_lt_of_le hi
      · exact h₂
      · have := h₁ i hi
        infer_instance)
  have := hC
  let C' := (mappingCone α).truncLE (k - 1)
  let ι : C' ⟶ mappingCone α := (mappingCone α).ιTruncLE (k - 1)
  let β : C' ⟶ P⟦(1 : ℤ)⟧ := ι ≫ (mappingCone.triangle α).mor₃
  let j : P ⟶ mappingCocone β := ((mappingCocone.inr β).leftUnshift 0 (by lia)).homOf
  have hj (i : ℤ) : j.f i = ((1 : ℤ) * 1 + ((1 : ℤ) * (1 - 1)) / 2).negOnePow •
      ((P.shiftFunctorObjXIso 1 (i - 1) i (by lia)).inv ≫
        (mappingCocone.inr β).1.v (i - 1) i (by lia)) :=
    Cochain.leftUnshift_v _ 0 (by lia) i i (add_zero i) (i - 1) (by lia)
  have hunit {X Y : C} (u : ℤˣ) (f : X ⟶ Y) : u • f = (u • 𝟙 X) ≫ f := by simp
  have hunitIso {X : C} (u : ℤˣ) : IsIso (u • 𝟙 X) :=
    ⟨⟨u⁻¹ • 𝟙 X, by simp [smul_smul], by simp [smul_smul]⟩⟩
  have hmono (i : ℤ) : Mono ((mappingCocone.inr β).1.v (i - 1) i (by lia)) :=
    mono_of_mono_fac (mappingCocone.inr_v_snd_v β (i - 1) i (by lia))
  refine ⟨mappingCocone β, j, fun i ↦ ?_, fun i hi ↦ ?_, ?_⟩
  · rw [hj, hunit]
    infer_instance
  · rw [hj, hunit]
    have hC' : IsZero (C'.X i) := C'.isZero_of_isStrictlyLE (k - 1) i (by lia)
    have : IsIso ((mappingCocone.inr β).1.v (i - 1) i (by lia)) := by
      refine ⟨⟨(mappingCocone.snd β).v i (i - 1) (by lia),
        mappingCocone.inr_v_snd_v β (i - 1) i (by lia), ?_⟩⟩
      have h := mappingCocone.id_X β i (i - 1) (by lia)
      rwa [hC'.eq_of_tgt ((mappingCocone.fst β).f i) 0, zero_comp, zero_add] at h
    infer_instance
  · have hT₁ := rot_of_distTriang _ (mappingCocone_triangle_distinguished β)
    have hT₂ := rot_of_distTriang _ (rot_of_distTriang _ (mappingCone_triangle_distinguished α))
    have : IsIso (Q.map ι) := (isIso_Q_map_iff_quasiIso (C := C) ι).2 inferInstance
    let e₁ : Q.obj C' ≅ Q.obj (mappingCone α) := asIso (Q.map ι)
    obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ hT₁ hT₂
      (Arrow.isoMk e₁ ((Q.commShiftIso (1 : ℤ)).app P) (by
        simp [e₁, β, Functor.mapTriangle, mappingCocone.triangle, Triangle.rotate]
        first
        | rfl
        | exact ((Q (C := C)).map_comp_assoc ι _ _).symm))
    let e' : (Q.obj (mappingCocone β))⟦(1 : ℤ)⟧ ≅ (Q.obj M)⟦(1 : ℤ)⟧ := Triangle.π₃.mapIso e
    exact ⟨(shiftFunctorCompIsoId (DerivedCategory C) (1 : ℤ) (-1) (by simp)).symm.app _ ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory C) (-1 : ℤ)).mapIso e' ≪≫
      (shiftFunctorCompIsoId (DerivedCategory C) (1 : ℤ) (-1) (by simp)).app _⟩

end CochainComplex
