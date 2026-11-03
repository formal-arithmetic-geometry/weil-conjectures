/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.UniformFilteredHomotopy
import WeilConjectures.CategoryTheory.UniformFilteredBridge.UniformFilteredConeRotation

/-! # Ore squares up to filtered homotopy

Source: Stacks Project, Derived Categories, Sections 13.6 and 13.13.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory

open UniformFilteredCone UniformFilteredFiber UniformFilteredBridge Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Ore squares for uniformly finite filtered complexes, commuting by a
filtration-preserving homotopy, in both orientations.

Source: Stacks, Derived Categories, Tags 05S1--05S3, and the proof of the cone
multiplicative system in Section 13.6, Tag 05RG.
Proof. For s:A→X take its filtered fiber S with projection q:S→A. Since s
is a graded quasi-isomorphism, S is graded acyclic. Set k=q f and Z=Cone(k).
The inclusion t:Y→Z is a graded quasi-isomorphism. The filtered null-homotopy
of k t extends f t to U:Cone(q)→Z. The inverse rotation map J:X→Cone(q)
satisfies s J homotopic to the cone inclusion. Postcompose with U to obtain
the required square with u=J U.
For s:Y→A take S=Cone(s) and its inclusion i:A→S. This S is graded acyclic.
Set k=f i and Z=fiber(k). Its projection t:Z→X is a graded quasi-isomorphism.
The standard filtered null-homotopy of t k lifts t f to U:Z→fiber(i). The
rotation projection v:fiber(i)→Y satisfies v s homotopic to its fiber
projection. Precompose with U to obtain the square with u=U v.
The ordinary rotation maps and homotopies commute with every square, and the
canonical step comparisons transport them to actual filtered maps and
homotopies. Both cone and fiber constructions retain uniform finite
filtration bounds, the prescribed interval B, and all four cochain conditions.
(blueprint: lem-trf-uniform-filtered-ore-squares). -/
theorem uniformFiltered_ore_squares
    (B : Option (ℤ × ℤ)) (P : ObjectProperty (CochainComplex C ℤ))
    (hP : IsUniformCochainCondition P) :
    (∀ (A X Y : UniformFilteredComplexes C B P) (s : A ⟶ X) (f : A ⟶ Y),
      uniformFilteredQuasiIso B P s →
        ∃ (Z : UniformFilteredComplexes C B P) (u : X ⟶ Z) (t : Y ⟶ Z),
          uniformFilteredQuasiIso B P t ∧ UniformFilteredHomotopy (f ≫ t).hom (s ≫ u).hom) ∧
    (∀ (A X Y : UniformFilteredComplexes C B P) (s : Y ⟶ A) (f : X ⟶ A),
      uniformFilteredQuasiIso B P s →
        ∃ (Z : UniformFilteredComplexes C B P) (t : Z ⟶ X) (u : Z ⟶ Y),
          uniformFilteredQuasiIso B P t ∧ UniformFilteredHomotopy (t ≫ f).hom (u ≫ s).hom) := by
  constructor
  · intro A X Y s f hs
    let S : UniformFilteredComplexes C B P :=
      ⟨fiber A.obj X.obj s.hom, fiber_property B P hP s⟩
    let q : S ⟶ A := ⟨filteredFiberProjection s.hom⟩
    let k : S ⟶ Y := q ≫ f
    let Z : UniformFilteredComplexes C B P :=
      ⟨filteredCone k.hom, filteredCone_property B P hP k⟩
    let t : Y ⟶ Z := ⟨filteredCone_inr k.hom⟩
    have hnull : UniformFilteredHomotopy (q.hom ≫ (f.hom ≫ t.hom)) 0 := by
      simpa only [t, Z, k, ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using
        filteredCone_nullHomotopy k.hom
    obtain ⟨U, hU⟩ := filteredCone_desc q.hom (f.hom ≫ t.hom) hnull
    let u : X ⟶ Z := ⟨filteredInverseRotateInclusion s.hom ≫ U⟩
    refine ⟨Z, u, t, ?_, ?_⟩
    · exact filteredCone_inr_quasiIso k.hom (filteredFiber_acyclic s.hom hs)
    · have he := (filteredInverseRotateHomotopy s.hom).comp_right U
      change filteredCone_inr (filteredFiberProjection s.hom) ≫ U = f.hom ≫ t.hom at hU
      rw [hU] at he
      have hsu : UniformFilteredHomotopy (s ≫ u).hom (f ≫ t).hom := by
        simpa only [u, ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using he
      exact hsu.symm
  · intro A X Y s f hs
    let S : UniformFilteredComplexes C B P :=
      ⟨filteredCone s.hom, filteredCone_property B P hP s⟩
    let i : A ⟶ S := ⟨filteredCone_inr s.hom⟩
    let k : X ⟶ S := f ≫ i
    let Z : UniformFilteredComplexes C B P :=
      ⟨fiber X.obj S.obj k.hom, fiber_property B P hP k⟩
    let t : Z ⟶ X := ⟨filteredFiberProjection k.hom⟩
    have hnull : UniformFilteredHomotopy ((t.hom ≫ f.hom) ≫ i.hom) 0 := by
      simpa only [t, Z, k, ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using
        filteredFiber_nullHomotopy k.hom
    obtain ⟨U, hU⟩ := filteredFiber_lift i.hom (t.hom ≫ f.hom) hnull
    let u : Z ⟶ Y := ⟨U ≫ filteredRotateProjection s.hom⟩
    refine ⟨Z, t, u, ?_, ?_⟩
    · exact filteredFiberProjection_quasiIso k.hom (filteredCone_acyclic s.hom hs)
    · have he := (filteredRotateProjectionHomotopy s.hom).comp_left U
      change U ≫ filteredFiberProjection (filteredCone_inr s.hom) = t.hom ≫ f.hom at hU
      rw [hU] at he
      have hus : UniformFilteredHomotopy (u ≫ s).hom (t ≫ f).hom := by
        simpa only [u, ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc] using he
      exact hus.symm

end CategoryTheory
