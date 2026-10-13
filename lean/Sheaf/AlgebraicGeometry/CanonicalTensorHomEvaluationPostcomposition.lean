/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # One-variable localized evaluation compatibility

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-evaluation-postcomposition).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- One-variable compatibility of the explicit localized identity evaluation.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-evaluation-postcomposition).

Proof: Evaluation is natural in its target. Compute c.inv by a map between the fixed
K-injective target resolutions, after replacing the source by a quasi-isomorphic
complex if needed. On each total tensor summand, Hom projection naturality and
the sheaf tensor-Hom adjunction identify evaluation after Hom postcomposition
with evaluation followed by the target map. The coproduct universal property
gives equality of chain maps. Degree-minus-one uncurrying and the signed Hom
differential show that the equality survives passage to homotopy classes. Apply Q
and use naturality of the lax tensor comparison, the fixed Hom resolution
comparison, and the augmentation. Cancel the quasi-isomorphisms of the target
models. A K-flat resolution of L reduces arbitrary L to the same computation,
since Hom into a K-injective and derived tensor invert this resolution. The
argument uses no boundedness assumption and applies to zero objects and identity
comparisons. -/
theorem tensorHomEvaluation_postcomposition (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L M M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (c : DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj M') :
    letI := schemeDerivedTensorMonoidal X
    let E := fun L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ↦
      ((schemeDerivedInternalHomResolutionIso X L M).hom ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L)) ≫
        pullbackTensorModelMap X (homComplex (R := X.sheaf) L
          ((schemeHomKInjectiveResolution X).obj M)) L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X _ L M (𝟙 _)) ≫
        schemeHomResolutionInverse X M
    ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
        (𝟙 (op (DerivedCategory.Q.obj L)), c.inv) ⊗ₘ 𝟙 (DerivedCategory.Q.obj L)) ≫
        E L M = E L M' ≫ c.inv := by sorry

end AlgebraicGeometry
