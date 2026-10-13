/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # Naturality of localized tensor-Hom evaluation

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-evaluation-naturality).
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

/-- Evaluation at the identity of the fixed Hom complex is natural in both derived
variables. This concerns the evaluation morphism itself, with no choice of a map into
internal Hom.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex, Tags 0A90
and 0A96. (blueprint: lem-pc-tensor-hom-evaluation-naturality).

Proof: First resolve L and L' by K-flat complexes. Compute b on a common K-flat
roof and c by maps between the fixed K-injective resolutions. Evaluation of the
Hom complex commutes with precomposition in L and postcomposition in I(M): on
each tensor summand this is naturality of the sheaf tensor-Hom adjunction and of
the Hom projections. The coproduct universal property gives these equalities of
chain maps. The same componentwise uncurrying of degree-minus-one cochains takes
homotopies to homotopies, by the signed Hom differential formula, so these identities
hold for homotopy classes. Hom from a K-flat complex into a K-injective complex is
K-injective, allowing derived morphisms into these Hom complexes to be computed by
homotopy classes. Localize the evaluation identities and use naturality of the lax
tensor comparison, the internal-Hom resolution comparison and the augmentation into
I(M). Cancel the localized quasi-isomorphisms in the common roofs. For arbitrary L
and L', the Hom functor into I(M) inverts their K-flat resolutions; the derived tensor
also inverts these resolutions. Thus the localized identities give the displayed
square on the original objects. The identity evaluations are genuine chain maps;
no data is chosen from an existence assertion. This argument includes zero objects,
zero maps and identity comparisons, and imposes no boundedness condition. -/
theorem tensorHomEvaluation_natural (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L M L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (b : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L')
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
        (b.hom.op, c.inv) ⊗ₘ 𝟙 (DerivedCategory.Q.obj L)) ≫ E L M =
      (𝟙 _ ⊗ₘ b.hom) ≫ E L' M' ≫ c.inv := by sorry

end AlgebraicGeometry
