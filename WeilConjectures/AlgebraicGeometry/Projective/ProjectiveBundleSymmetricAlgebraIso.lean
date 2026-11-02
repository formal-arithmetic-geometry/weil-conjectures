/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra

/-! # Transport from the canonical symmetric algebra to a normalized realization

Source: Stacks Project, Constructions, Tag 01OB.
(blueprint: def-pur-projective-bundle-symmetric-algebra-iso).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- The product-span definition of symmetric degree equals the power of the inclusion range.
Source: Stacks Project, Tag 01OB
(blueprint: def-pur-projective-bundle-symmetric-algebra-iso). -/
theorem projectiveBundleSymmetricDegree_eq (R M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] (n : ℕ) :
    Scheme.symmetricDegree R M n = (SymmetricAlgebra.ι R M).range ^ n := by
  have h := SymmetricAlgebra.graded_span_pure_tensors R M n
  simp only [Submodule.map_pow, ← LinearMap.range_comp] at h
  change (SymmetricAlgebra.ι R M).range ^ n = _ at h
  simpa only [Scheme.symmetricDegree, List.prod_ofFn] using h.symm

/-- The section identifications of a normalized realization assemble to a graded-algebra
isomorphism from the canonical symmetric algebra. The grading equation identifies precisely the
same products of degree-one generators, and the restriction equation is naturality.
Source: Stacks Project, Tag 01OB.
(blueprint: def-pur-projective-bundle-symmetric-algebra-iso). -/
noncomputable def projectiveBundleSymmetricAlgebraIso
    {B : Scheme.{u}} {F : B.Modules} [F.IsQuasicoherent]
    (A : B.SymmetricGradedAlgebraData F) :
    SymmetricAlgebraSheaf.gradedAlgebraData F ≅ A.data where
  hom :=
    { app := fun U ↦
        { toRingHom := (A.sectionEquiv U).toRingHom
          map_mem := by
            intro n x hx
            apply (A.sectionEquiv_grade U n x).mp
            rwa [projectiveBundleSymmetricDegree_eq] }
      app_algebraMap := fun U r ↦ (A.sectionEquiv U).commutes r
      naturality := by
        intro U V h x
        exact (A.sectionEquiv_restriction h x).symm }
  inv :=
    { app := fun U ↦
        { toRingHom := (A.sectionEquiv U).symm.toRingHom
          map_mem := by
            intro n x hx
            change (A.sectionEquiv U).symm x ∈
              (SymmetricAlgebra.ι _ _).range ^ n
            rw [← projectiveBundleSymmetricDegree_eq]
            apply (A.sectionEquiv_grade U n _).mpr
            simpa using hx }
      app_algebraMap := fun U r ↦ (A.sectionEquiv U).symm.commutes r
      naturality := by
        intro U V h x
        apply (A.sectionEquiv U).injective
        change A.sectionEquiv U ((A.sectionEquiv U).symm (A.data.res h x)) =
          A.sectionEquiv U (SymmetricAlgebraSheaf.restriction F (homOfLE h).op
            ((A.sectionEquiv V).symm x))
        rw [AlgEquiv.apply_symm_apply, ← A.sectionEquiv_restriction,
          AlgEquiv.apply_symm_apply] }
  hom_inv_id := by
    apply Scheme.GradedAlgebraData.hom_ext
    intro U
    apply GradedRingHom.ext
    intro x
    exact (A.sectionEquiv U).symm_apply_apply x
  inv_hom_id := by
    apply Scheme.GradedAlgebraData.hom_ext
    intro U
    apply GradedRingHom.ext
    intro x
    exact (A.sectionEquiv U).apply_symm_apply x

end AlgebraicGeometry
