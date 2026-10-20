/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredLocalization
import Sheaf.Algebra.Homology.FilteredInjectiveResolution
import Sheaf.Algebra.Homology.FilteredAcyclicInjectiveVanishing
import Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.ObjectProperty.Local

/-!
# Filtered injectives compute bounded-below filtered localization

Source: Stacks Project, Derived Categories, Tags 05TW
(`lemma-right-resolution-by-filtered-injectives`), 05TY
(`lemma-morphisms-into-filtered-injective-complex`) and 015Q
(`lemma-filtered-localization-functor`)
(blueprint: lem-trf-filtered-localization-injective-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w} C]

/-- Filtered-injective resolutions, the localization Hom bijection, and the exact
comparison equivalence, compatibly with forgetting and every graded-piece functor.
`B = none` imposes no common filtration interval on the terms of a complex;
`B = some (a,b)` gives all assertions with `Fᵃ = ⊤`, `Fᵇ⁺¹ = ⊥` throughout.
`p = none` denotes forgetting and `p = some n` denotes the `n`-th graded piece.

Source: Stacks, Derived Categories, Tags 05TW, 05TY and 015Q.
Proof:
1. Apply `filteredInjectiveResolution`, the separate Tag 05TW construction.
2. By `filteredAcyclic_injective_vanishing` (Tag 05TX), every graded-acyclic complex
   has only the zero map to a bounded-below complex of filtered injectives. Apply
   exactness of Hom to a distinguished triangle of a graded quasi-isomorphism and
   its inverse rotation. The graded cones are acyclic by the ordinary abelian cone
   criterion. Thus precomposition by the quasi-isomorphism is bijective.
3. In a left fraction ending at I, extend the identity of I across its denominator.
   This gives a retraction, so the fraction is the image of an ordinary morphism.
   The same retraction cancels the denominator witnessing equality of two images.
4. Full faithfulness of the inclusion and step 3 imply full faithfulness of the
   comparison. Step 1 and essential surjectivity of localization give essential
   surjectivity. The standard inclusion and localization instances give exactness.
5. Split a term's finite filtration using `injective_graded_filtration_splits`.
   Its underlying object is isomorphic to a finite sum of injectives, hence is
   injective; its graded pieces are injective by definition.
6. Evaluation commutes with inclusion termwise. The factorization isomorphism for
   the localization lift and the composition isomorphism for homotopy functors
   give the displayed natural comparison isomorphisms.
All arguments use the same B, including unrestricted and prescribed intervals.
(blueprint: lem-trf-filtered-localization-injective-model). -/
theorem filteredLocalization_injectiveModel (B : Option (ℤ × ℤ)) :
    (∀ K : CochainComplex.Plus (FiniteFilteredObjects C B false),
      ∃ (I : CochainComplex.Plus (FiniteFilteredObjects C B true))
        (f : K ⟶ (filteredInjectiveInclusion C B).mapCochainComplexPlus.obj I),
        finiteFilteredQuasiIso C B
          ((HomotopyCategory.Plus.quotient (FiniteFilteredObjects C B false)).map f)) ∧
    (∀ K I : FiniteFilteredHomotopyPlus C B false,
      (∀ n p : ℤ, Injective ((I.obj.as.X n).obj.filtration.gradedPiece p)) →
      Function.Bijective
        ((finiteFilteredQh C B).map : (K ⟶ I) →
          ((finiteFilteredQh C B).obj K ⟶ (finiteFilteredQh C B).obj I))) ∧
    (filteredInjectiveComparison C B).IsEquivalence ∧
    (filteredInjectiveComparison C B).IsTriangulated ∧
    (∀ (I : FiniteFilteredHomotopyPlus C B true) (n : ℤ) (p : Option ℤ),
      Injective ((filteredEvaluation C B true p).obj (I.obj.as.X n))) ∧
    (∀ p : Option ℤ, Nonempty
      (filteredInjectiveComparison C B ⋙ finiteFilteredDerivedEvaluation C B p ≅
        (filteredEvaluation C B true p).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh)) := by
  have hres := filteredInjectiveResolution C B
  have hzero := filteredAcyclic_injective_vanishing C B
  have hlocal (I : FiniteFilteredHomotopyPlus C B false)
      (hi : ∀ n p : ℤ, Injective ((I.obj.as.X n).obj.filtration.gradedPiece p)) :
      (finiteFilteredQuasiIso C B).isLocal I := by
    let E (p : ℤ) := (filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus ⋙
      HomotopyCategory.Plus.ι C
    let P (p : ℤ) := (HomotopyCategory.subcategoryAcyclic C).inverseImage (E p)
    have hz (A : FiniteFilteredHomotopyPlus C B false) (ha : ∀ p, P p A) (f : A ⟶ I) :
        f = 0 :=
      hzero A I (fun p ↦ (HomotopyCategory.mem_subcategoryAcyclic_iff _).1 (ha p)) hi f
    intro X Y f hf
    obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
    let T := Pretriangulated.Triangle.mk f g h
    have ha (p : ℤ) : P p Z := by
      have hp := hf p
      change HomotopyCategory.quasiIso C (.up ℤ) ((E p).map f) at hp
      rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hp
      exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
        ((E p).mapTriangle.obj T) ((E p).map_distinguished T hT)).1 hp
    constructor
    · suffices ∀ (α : Y ⟶ I), f ≫ α = 0 → α = 0 from fun α β hα ↦ by
        simpa only [sub_eq_zero] using this (α - β) (by simpa [sub_eq_zero] using hα)
      intro α hα
      obtain ⟨β, rfl⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT α hα
      simp [hz Z ha β]
    · intro α
      obtain ⟨β, hβ⟩ := Pretriangulated.Triangle.yoneda_exact₂ T.invRotate
        (Pretriangulated.inv_rot_of_distTriang T hT)
        α (hz _ (fun p ↦ (P p).le_shift (-1) Z (ha p)) _)
      exact ⟨β, hβ.symm⟩
  have hhom (K I : FiniteFilteredHomotopyPlus C B false)
      (hi : ∀ n p : ℤ, Injective ((I.obj.as.X n).obj.filtration.gradedPiece p)) :
      Function.Bijective ((finiteFilteredQh C B).map : (K ⟶ I) → _) := by
    let Q := finiteFilteredQh C B
    let W := finiteFilteredQuasiIso C B
    constructor
    · intro f g h
      obtain ⟨Z, s, hs, heq⟩ := (MorphismProperty.map_eq_iff_postcomp Q W f g).1 h
      obtain ⟨r, hr⟩ := (hlocal I hi s hs).2 (𝟙 I)
      calc
        f = (f ≫ s) ≫ r := by simp [Category.assoc, hr]
        _ = (g ≫ s) ≫ r := by rw [heq]
        _ = g := by simp [Category.assoc, hr]
    · intro f
      obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction Q W f
      obtain ⟨r, hr⟩ := (hlocal I hi φ.s φ.hs).2 (𝟙 I)
      change φ.s ≫ r = 𝟙 I at hr
      refine ⟨φ.f ≫ r, ?_⟩
      have hr' : Q.map r = inv (Q.map φ.s) := by
        rw [← cancel_epi (Q.map φ.s), ← Q.map_comp, hr, Q.map_id]
        simp
      rw [Q.map_comp, hr', hφ]
      rfl
  have hequiv : (filteredInjectiveComparison C B).IsEquivalence := by
    let A := (filteredInjectiveInclusion C B).mapHomotopyCategoryPlus
    let Q := finiteFilteredQh C B
    let F :=
      filteredInjectiveComparison C B
    let : (filteredInjectiveInclusion C B).Full := by
      dsimp only [filteredInjectiveInclusion]
      infer_instance
    let : (filteredInjectiveInclusion C B).Faithful := by
      dsimp only [filteredInjectiveInclusion]
      infer_instance
    have hb (K I : FiniteFilteredHomotopyPlus C B true) :
        Function.Bijective (F.map : (K ⟶ I) → _) := by
      exact (hhom (A.obj K) (A.obj I)
        (fun n p ↦ (I.obj.as.X n).property.2.2 p rfl)).comp
          ⟨A.map_injective, A.map_surjective⟩
    let : F.Full := ⟨fun {K I} ↦ (hb K I).2⟩
    let : F.Faithful := ⟨fun {K I} ↦ (hb K I).1⟩
    let : Q.EssSurj := Localization.essSurj Q (finiteFilteredQuasiIso C B)
    let : F.EssSurj := ⟨fun Y ↦ by
      let e := Q.objObjPreimageIso Y
      obtain ⟨K, hK⟩ := HomotopyCategory.Plus.quotient_obj_surjective (Q.objPreimage Y)
      obtain ⟨I, f, hf⟩ := hres K
      refine ⟨(HomotopyCategory.Plus.quotient (FiniteFilteredObjects C B true)).obj I, ?_⟩
      exact ⟨(Localization.isoOfHom Q (finiteFilteredQuasiIso C B) _ hf).symm ≪≫
        Q.mapIso (eqToIso hK) ≪≫ e⟩⟩
    exact {}
  refine ⟨hres, hhom, hequiv, ?_⟩
  constructor
  · dsimp only [filteredInjectiveComparison]
    infer_instance
  constructor
  · intro I n p
    cases p with
    | none =>
      simpa [filteredEvaluation] using
        (show Injective (I.obj.as.X n).obj.obj from by
          obtain ⟨a, b, ha, hb⟩ := (I.obj.as.X n).property.1
          let c := max a b
          have hc : (I.obj.as.X n).obj.filtration.F (c + 1) = ⊥ := by
            apply le_antisymm _ bot_le
            rw [← hb]
            exact (I.obj.as.X n).obj.filtration.antitone (by dsimp [c]; omega)
          obtain ⟨J, hJ, _, θ, _⟩ :=
            FilteredObject.injective_graded_filtration_splits (I.obj.as.X n).obj a c
              (le_max_left _ _) ha hc (fun p ↦ (I.obj.as.X n).property.2.2 p rfl)
          let := hJ
          exact Injective.of_iso θ.symm inferInstance)
    | some p =>
      exact (I.obj.as.X n).property.2.2 p rfl
  · intro p
    have e : filteredInjectiveInclusion C B ⋙ filteredEvaluation C B false p =
        filteredEvaluation C B true p := by
      cases p <;> rfl
    let A := (filteredInjectiveInclusion C B).mapHomotopyCategoryPlus
    let E := (filteredEvaluation C B false p).mapHomotopyCategoryPlus
    let Q := DerivedCategory.Plus.Qh (C := C)
    refine ⟨Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft A
      (eqToIso (Localization.Construction.fac _ _)) ≪≫
      (Functor.associator A E Q).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomotopyCategoryPlusCompIso (eqToIso e)) Q⟩

end CategoryTheory
