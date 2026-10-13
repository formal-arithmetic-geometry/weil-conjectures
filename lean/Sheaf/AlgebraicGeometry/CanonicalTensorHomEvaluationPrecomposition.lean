/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # One-variable localized evaluation compatibility

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-evaluation-precomposition).
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
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-evaluation-precomposition).

Proof: Evaluation is dinatural in the complex being evaluated. Resolve L and L' by
K-flat complexes and represent b on a common K-flat roof. Hom into I(M) is
K-injective on these models, so the comparison is computed by chain maps modulo
homotopy. On each total tensor summand, the Hom projection and sheaf tensor-Hom
adjunction identify evaluation after Hom precomposition with evaluation after
applying the comparison in the tensor factor. Extend over the coproduct to get the
chain-map identity. Uncurry the degree-minus-one components to carry chain
homotopies to tensor homotopies using the signed Hom differential formula. Apply
Q; naturality of its lax tensor comparison and the Hom resolution comparison
identifies the resulting composites. Cancel the localized roof denominators and
K-flat resolutions. This proves the displayed identity for arbitrary unbounded
L and L'; zero complexes, zero maps, and identity comparisons obey the same
summand identity. -/
theorem tensorHomEvaluation_precomposition (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L L' M : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (b : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L') :
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
        (b.hom.op, 𝟙 (DerivedCategory.Q.obj M)) ⊗ₘ 𝟙 (DerivedCategory.Q.obj L)) ≫ E L M =
      (𝟙 _ ⊗ₘ b.hom) ≫ E L' M := by sorry

end AlgebraicGeometry
