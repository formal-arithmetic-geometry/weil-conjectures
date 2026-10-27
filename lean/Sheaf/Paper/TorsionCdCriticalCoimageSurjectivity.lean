/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence

/-! # A relation-comparison substep of the arbitrary-affine cohomological bound -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The critical coimage cohomology classes lift to source cohomology.

Source: blueprint latest, `det-sf-comp-coherence-refinement.proof.md`, paragraph (2),
first paragraph, arbitrary-affine coefficient-transfer obligation; the relation
comparison in steps 2 and 3 of `lem-sfb-torsion-cd-bounded-serre-kernel`.
Agent-formulated sub-obligation; exact full-generality reference WANTED.
(blueprint: lem-sfb-torsion-cd-critical-coimage-surjectivity)

Proof in words (the remaining geometric obligation):
At the critical degree d+2, retain the map from the source to its actual coimage
in the strict relation comparison on affine weakly contractible pro-etale charts.
The torsion etale bound makes the critical obstruction a boundary in the finite
quotient relation complexes. For integral coefficients compare the compatible
boundaries through the countable inverse-limit triangle, rather than assuming
surjectivity of individual quotient transition maps. For rational coefficients
localize the finite integral relation comparison exactly. Descend the comparison
through the open-closed support refinements. The resulting lift of each critical
coimage cohomology class to source cohomology proves the asserted epimorphism.
This statement concerns this one critical degree only; it gives no bound in higher
degrees. It requires the actual relation comparison for arbitrary earlier hull
objects, not merely finite-model maps, and assumes no arbitrary completeness.

For the zero map the coimage is zero. For an isomorphism the coimage is isomorphic
to the source and its quotient map is invertible. Empty schemes and zero modules
are included. The functor is the ordinary uncompleted derived sections functor.
-/
theorem torsionCd_critical_coimage_surjectivity
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : M ⟶ N)
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M)
    (hN : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) N)
    (hMb : ∀ q : ℤ, (d : ℤ) + 2 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((condensedModuleSections Λ X).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))))
    (hNb : ∀ q : ℤ, (d : ℤ) + 2 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((condensedModuleSections Λ X).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj N))))
    : Epi ((DerivedCategory.homologyFunctor _ ((d : ℤ) + 2)).map
      ((condensedModuleSections Λ X).rightDerivedFunctor.map
        ((DerivedCategory.singleFunctor _ 0).map (Abelian.coimage.π f)))) := by
  sorry

end AlgebraicGeometry.ProEtale
