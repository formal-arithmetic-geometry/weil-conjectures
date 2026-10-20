/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredLocalization

/-!
# Cone triangles in the localization of finite filtered complexes

Source: Stacks Project, Derived Categories, Tags 014S, 014X, 05RQ, 05RX,
05S1 and 05S2 (blueprint: lem-trf-filtered-cone-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The standard cochain cone triangulation on bounded-below finite filtered complexes,
its restriction to every full additive subcategory, and its graded localization.
`B = none` allows filtration bounds depending on each term; `B = some (a,b)`
imposes `Fᵃ = ⊤` and `Fᵇ⁺¹ = ⊥`. In particular all intervals `a ≤ b` are covered.
The structures in the conclusion are the existing cochain and localization structures.
The graded-acyclic cone criterion is stated for every distinguished cone of a map,
so it is independent of the chain-map representative and of the chosen cone.

Source: Stacks, Derived Categories, Tags 05RX, 05S1 and 05S2, with bounded-below
restriction by 05RQ and additive inclusions by 014X.
Proof (the seven steps of the DAG node):
1. Finite filtered objects are additive: use finite sums of underlying objects and
   filtration steps (def-sp-filtration), with common extrema of their finite bounds.
   The same construction retains prescribed bounds. Apply
   lem-trf-additive-homotopy-category-triangulated (014S) to obtain the standard
   cochain shift and direct-sum mapping-cone triangles in the homotopy category.
2. Bounded-below complexes form a full triangulated subcategory
   (def-weil-triangulated-subcategory). Both shifts preserve boundedness. The cone
   of X to Y vanishes below min(N_Y,N_X-1). For an arbitrary triangle, rotate
   backwards and compare with a cone by TR3; lem-sf-triangle-morphism-iso identifies
   the third vertices. Thus its inherited triangles are precisely cone triangles
   up to isomorphism and the inclusion into the unbounded category is exact.
3. Each graded functor (def-sp-filtered-complex-subquotients) commutes with shifts
   and finite sums, identifying the graded cone with the cone of the graded map.
   Apply lem-pur-quasi-iso-cone-acyclic in every grade: W is exactly the maps with
   graded-acyclic cones, also for any isomorphic distinguished cone.
4. Grading preserves filtered homotopies, so graded cohomology is defined on the
   homotopy category and respects isomorphisms. Graded-acyclic objects contain zero,
   are closed under shifts, and are closed under cones by step 3. Backward rotation,
   TR3 and lem-sf-triangle-morphism-iso give closure under distinguished triangles.
   They therefore form a full replete triangulated subcategory.
5. The cone system of this subcategory is W by step 3. Apply
   lem-trf-triangulated-subcategory-cone-system: identities, composition, both
   fraction calculi, shift invariance and completion of squares by maps in W hold.
   These give def-pur-saturated-triangulated-localization's compatibility hypotheses.
6. Apply lem-pur-localization-triangles-05r6: localization is triangulated, Q is
   exact, and its distinguished triangles are the images of distinguished triangles
   up to isomorphism. Step 2 identifies these with images of cone triangles.
   The standard localization uses the maximum of the category's size universes.
7. A full additive subcategory J has zero and binary biproducts. Apply steps 1 and 2
   to J; inclusion preserves sums, shifts and homotopies, hence cone triangles and
   every distinguished triangle (014X). All constructions retain any fixed interval,
   without requiring a uniform filtration bound across degrees in the unrestricted case.
(blueprint: lem-trf-filtered-cone-localization). -/
theorem filteredConeLocalization (B : Option (ℤ × ℤ))
    (_hB : ∀ a b : ℤ, B = some (a, b) → a ≤ b) :
    IsTriangulated (FiniteFilteredHomotopyPlus A B false) ∧
    (∀ T : Triangle (FiniteFilteredHomotopyPlus A B false),
      T ∈ distTriang (FiniteFilteredHomotopyPlus A B false) ↔
        ∃ (X Y : CochainComplex.Plus (FiniteFilteredObjects A B false)) (f : X ⟶ Y),
          Nonempty ((HomotopyCategory.Plus.ι (FiniteFilteredObjects A B false)).mapTriangle.obj T
            ≅ CochainComplex.mappingCone.triangleh f.hom)) ∧
    (∀ (J : ObjectProperty (FiniteFilteredObjects A B false))
      [HasZeroObject J.FullSubcategory] [HasBinaryBiproducts J.FullSubcategory],
      IsTriangulated (HomotopyCategory.Plus J.FullSubcategory) ∧
        J.ι.mapHomotopyCategoryPlus.IsTriangulated) ∧
    (∀ (T : Triangle (FiniteFilteredHomotopyPlus A B false)),
      T ∈ distTriang (FiniteFilteredHomotopyPlus A B false) →
        (finiteFilteredQuasiIso A B T.mor₁ ↔ ∀ p n : ℤ,
          IsZero ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).obj
            (((filteredEvaluation A B false (some p)).mapHomotopyCategoryPlus.obj
              T.obj₃).obj)))) ∧
    IsTriangulated (FiniteFilteredDerivedPlus A B) ∧
    (finiteFilteredQh A B).IsTriangulated ∧
    (∀ T : Triangle (FiniteFilteredDerivedPlus A B),
      T ∈ distTriang (FiniteFilteredDerivedPlus A B) ↔
        ∃ S : Triangle (FiniteFilteredHomotopyPlus A B false),
          S ∈ distTriang (FiniteFilteredHomotopyPlus A B false) ∧
            Nonempty (T ≅ (finiteFilteredQh A B).mapTriangle.obj S)) := by
  refine ⟨inferInstance, ?_, ?_, ?_, inferInstance, inferInstance, ?_⟩
  · intro T
    constructor
    · intro hT
      have hX : CochainComplex.plus (FiniteFilteredObjects A B false) T.obj₁.obj.as :=
        (HomotopyCategory.plus_quotient_obj_iff _).mp T.obj₁.property
      have hY : CochainComplex.plus (FiniteFilteredObjects A B false) T.obj₂.obj.as :=
        (HomotopyCategory.plus_quotient_obj_iff _).mp T.obj₂.property
      obtain ⟨f, hf⟩ := (HomotopyCategory.quotient _ _).map_surjective T.mor₁.hom
      refine ⟨⟨_, hX⟩, ⟨_, hY⟩, ObjectProperty.homMk f, ⟨?_⟩⟩
      exact isoTriangleOfIso₁₂ _ _
        ((HomotopyCategory.Plus.ι _).map_distinguished T hT)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)
        (Iso.refl _) (Iso.refl _) (by
          change T.mor₁.hom ≫ 𝟙 _ =
            𝟙 _ ≫ (HomotopyCategory.quotient _ _).map f
          simp only [Category.comp_id, Category.id_comp]
          exact hf.symm)
    · rintro ⟨X, Y, f, ⟨e⟩⟩
      exact isomorphic_distinguished _
        (HomotopyCategory.mappingCone_triangleh_distinguished f.hom) _ e
  · intro J _ _
    exact ⟨inferInstance, inferInstance⟩
  · intro T hT
    change (∀ p : ℤ, HomotopyCategory.Plus.quasiIso A
      ((filteredEvaluation A B false (some p)).mapHomotopyCategoryPlus.map T.mor₁)) ↔ _
    apply forall_congr'
    intro p
    let F := (filteredEvaluation A B false (some p)).mapHomotopyCategoryPlus
    have h := (HomotopyCategory.subcategoryAcyclic A).trW_iff_of_distinguished _
      ((HomotopyCategory.Plus.ι A).map_distinguished _ (F.map_distinguished T hT))
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.mem_subcategoryAcyclic_iff] at h
    exact h
  · intro T
    change (∃ S, ∃ _ : T ≅ (finiteFilteredQh A B).mapTriangle.obj S,
      S ∈ distTriang (FiniteFilteredHomotopyPlus A B false)) ↔ _
    constructor
    · rintro ⟨S, e, hS⟩
      exact ⟨S, hS, ⟨e⟩⟩
    · rintro ⟨S, hS, ⟨e⟩⟩
      exact ⟨S, e, hS⟩

end CategoryTheory
