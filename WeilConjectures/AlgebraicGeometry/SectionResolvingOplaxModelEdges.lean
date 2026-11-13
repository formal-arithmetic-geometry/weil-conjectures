/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxConstraintData
import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxClosure
import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxEdgeIdentifications

/-! # Resolving model edge squares

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
namespace ResolvingOplaxConstraints

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

/-- The nested resolving models, and the six edge squares. -/
theorem section_resolving_oplax_model_edges {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    (h : SectionHypotheses Λ f μ v) :
    ∀ P Q H : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory,
      ResolvingClosure Λ f P.obj Q.obj H.obj ∧
        SectionEdges Λ f μ P.obj Q.obj H.obj := by
  intro P Q H
  exact ⟨section_resolving_oplax_closure Λ f P.obj Q.obj H.obj
      P.property Q.property H.property,
    section_resolving_oplax_edge_identifications Λ f μ v h P.obj Q.obj H.obj⟩

end ResolvingOplaxConstraints
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
