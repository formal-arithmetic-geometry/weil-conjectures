/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.UniformFilteredHomotopy
import WeilConjectures.CategoryTheory.UniformFilteredOreSquares
import WeilConjectures.CategoryTheory.UniformFilteredHomotopy
import WeilConjectures.CategoryTheory.UniformFilteredCone.UniformFilteredCone
import WeilConjectures.CategoryTheory.UniformFilteredFiber.UniformFilteredFiber

/-! # Both fraction calculi on actual filtered homotopy classes

Source: Stacks Project, Derived Categories, Sections 13.6 and 13.13.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Graded quasi-isomorphisms on actual filtered homotopy classes admit both
fraction calculi. Source: Stacks, Section 13.13, Tags 05S1--05S3.
Proof: lift each quotient arrow to a chain map. The inverse-image equality
transfers the denominator condition. Apply the two Ore-square constructions
for the fraction condition and the two cancellation constructions for its equality
condition. Project the resulting filtered homotopies to quotient equalities.
Identities and compositions of denominators have already been proved.
(blueprint: lem-trf-uniform-filtered-homotopy-calculus). -/
theorem uniformFiltered_homotopy_calculus
    (B : Option (ℤ × ℤ)) (P : ObjectProperty (CochainComplex C ℤ))
    (hP : IsUniformCochainCondition P) :
    (uniformFilteredHomotopyQuasiIso B P).HasLeftCalculusOfFractions ∧
      (uniformFilteredHomotopyQuasiIso B P).HasRightCalculusOfFractions := by
  obtain ⟨hOreL, hOreR⟩ := uniformFiltered_ore_squares B P hP
  obtain ⟨hCancelL, hCancelR⟩ := uniformFiltered_homotopy_cancellation B P hP
  let q := uniformFilteredHomotopyQ B P
  have hW := uniformFilteredHomotopyQuasiIso_inverseImage B P
  have wiff {X Y : UniformFilteredComplexes C B P} (f : X ⟶ Y) :
      uniformFilteredHomotopyQuasiIso B P (q.map f) ↔ uniformFilteredQuasiIso B P f := by
    rw [hW]
    rfl
  have heq {X Y : UniformFilteredComplexes C B P} (f g : X ⟶ Y) :
      q.map f = q.map g ↔ UniformFilteredHomotopy f.hom g.hom :=
    CategoryTheory.Quotient.functor_map_eq_iff _ f g
  constructor
  · refine { exists_leftFraction := ?_, ext := ?_ }
    · intro X Y φ
      obtain ⟨f, hf⟩ := q.map_surjective φ.f
      obtain ⟨s, hs⟩ := q.map_surjective φ.s
      have hsW := (wiff s).1 (by rw [hs]; exact φ.hs)
      obtain ⟨Z, u, t, ht, h⟩ := hOreL _ _ _ s f hsW
      refine ⟨⟨q.map u, q.map t, (wiff t).2 ht⟩, ?_⟩
      rw [← hf, ← hs, ← q.map_comp, ← q.map_comp]
      exact (heq _ _).2 h
    · intro A X Y f g s hs h
      obtain ⟨f, rfl⟩ := q.map_surjective f
      obtain ⟨g, rfl⟩ := q.map_surjective g
      obtain ⟨s, rfl⟩ := q.map_surjective s
      have h' : UniformFilteredHomotopy (s ≫ f).hom (s ≫ g).hom :=
        (heq _ _).1 (by simpa only [Functor.map_comp] using h)
      obtain ⟨Z, t, ht, he⟩ := hCancelL _ _ _ f g s ((wiff s).1 hs) h'
      exact ⟨q.obj Z, q.map t, (wiff t).2 ht,
        by simpa only [Functor.map_comp] using (heq _ _).2 he⟩
  · refine { exists_rightFraction := ?_, ext := ?_ }
    · intro X Y φ
      obtain ⟨f, hf⟩ := q.map_surjective φ.f
      obtain ⟨s, hs⟩ := q.map_surjective φ.s
      have hsW := (wiff s).1 (by rw [hs]; exact φ.hs)
      obtain ⟨Z, t, u, ht, h⟩ := hOreR _ _ _ s f hsW
      refine ⟨⟨q.map t, (wiff t).2 ht, q.map u⟩, ?_⟩
      rw [← hf, ← hs, ← q.map_comp, ← q.map_comp]
      exact (heq _ _).2 h
    · intro X Y A f g s hs h
      obtain ⟨f, rfl⟩ := q.map_surjective f
      obtain ⟨g, rfl⟩ := q.map_surjective g
      obtain ⟨s, rfl⟩ := q.map_surjective s
      have h' : UniformFilteredHomotopy (f ≫ s).hom (g ≫ s).hom :=
        (heq _ _).1 (by simpa only [Functor.map_comp] using h)
      obtain ⟨Z, t, ht, he⟩ := hCancelR _ _ _ f g s ((wiff s).1 hs) h'
      exact ⟨q.obj Z, q.map t, (wiff t).2 ht,
        by simpa only [Functor.map_comp] using (heq _ _).2 he⟩

end CategoryTheory
