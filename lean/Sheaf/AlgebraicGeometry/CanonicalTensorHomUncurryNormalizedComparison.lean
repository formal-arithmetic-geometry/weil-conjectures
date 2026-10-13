/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.HomComplexGlobalCochains

/-! # Comparison of normalized derived evaluation maps

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-uncurry-normalized-comparison).
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

/-- Localized evaluation respects comparisons between normalized representatives.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex, Tags 0A90
and 0A96. (blueprint: lem-pc-tensor-hom-uncurry-normalized-comparison).

Proof: Replace L and L' by K-flat resolutions, and replace both targets by their
fixed K-injective resolutions. Hom from a K-flat complex into a K-injective is
K-injective, so the displayed equality of derived inputs is an equality of
homotopy classes after computing the comparison roofs on common K-flat sources.
Uncurrying carries a chain homotopy to a chain homotopy: uncurry its degree-minus-one
components on every tensor summand, and use the Hom differential formula to
identify the boundary with the difference of evaluations. On chain maps,
precomposition in P and L and postcomposition in the target commute with evaluation
by naturality of the sheaf tensor-Hom adjunction and of the Hom projections.
Coproduct extensionality promotes the summand identities to identities of chain
maps. Localize those identities. Naturality of the tensor model comparison, of the
internal-Hom resolution comparison, and of the resolution augmentation identifies
the resulting composites with the displayed outputs. Cancel the localized
quasi-isomorphisms of the chosen resolutions. For arbitrary L, K-flatness of P
makes P tensor - invert its resolution, while Hom(-,I(M)) also inverts it; hence
the same cancellation applies. This proves the implication without any hypothesis
on a family of values, and includes zero maps, zero complexes, and identity
comparisons. No boundedness is used. -/
theorem tensorHomUncurry_normalized_comparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L M P' L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlat) (hP' : P'.IsKFlat)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (φ' : P' ⟶ homComplex (R := X.sheaf) L'
      ((schemeHomKInjectiveResolution X).obj M'))
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (b : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L')
    (c : DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj M')
    (h : DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv =
      a.hom ≫ DerivedCategory.Q.map φ' ≫
        (schemeDerivedInternalHomResolutionIso X L' M').inv ≫
          (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
            (b.hom.op, c.inv)) :
    letI := schemeDerivedTensorMonoidal X
    pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
          schemeHomResolutionInverse X M =
      (a.hom ⊗ₘ b.hom) ≫ pullbackTensorModelMap X P' L' ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P' L' M' φ') ≫
          schemeHomResolutionInverse X M' ≫ c.inv := by sorry

end AlgebraicGeometry
