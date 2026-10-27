/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData

/-! # Normalized degree-one sections of the glued symmetric Proj twist

Source: Stacks Project, Constructions, Tags 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-glued-sections).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

/-- The degree-one affine twists glue, together with the sheaf map sending a module
section to its homogeneous fraction. No invertibility or surjectivity is asserted here.
Source: Stacks, Tag 01NR (lemma-glue-relative-proj-twists), specialized to degree one
of the symmetric algebra as in Tag 01OB (definition-projective-bundle).
(blueprint: lem-trf-symmetric-proj-glued-sections).

Proof: on every affine base open U take the existing module Proj.twist A(U) 1.
Quasi-coherent affine restriction is coefficientwise scalar extension. On the standard
open D_+(e), the scalar-extension isomorphism sends a/e^k to res(a)/res(e)^k.
These maps and their inverses commute with further standard-open restriction and
compose by the fraction formula. Refine intersections of affine base opens by affine
opens; agreement after refinement supplies the descent cocycle on the relative-Proj
chart cover. Glue these actual module sheaves and the chart isomorphisms. The sections
m ↦ iota(m)/1 are additive, linear over the base structure map, and compatible with
restriction by that same fraction formula. They therefore glue to a module morphism
σ from E to the direct image of the glued module. Its displayed normalization is the
local formula for this morphism, transported through the actual tensor-pullback unit.
No local freeness, finite generation, or nonemptiness is needed. -/
theorem exists_symmetric_twist_sections
    (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent] :
    ∃ (L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
      (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj L ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1)
      (σ : E ⟶ (Scheme.Modules.pushforward
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj L),
    ∀ (U : S.affineOpens) (m : E.val.obj (op U.1))
      (hm : SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1),
    (chart U).hom.app
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (Scheme.Modules.tensorPullbackSection
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U) L
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
          (σ.app U.1 m)) =
      Scheme.Modules.Hom.app (Proj.unitToTwist
        (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) hm)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (1 : Γ(Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U),
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))) := by
  sorry

end AlgebraicGeometry.SymmetricProjTautologicalCharts
