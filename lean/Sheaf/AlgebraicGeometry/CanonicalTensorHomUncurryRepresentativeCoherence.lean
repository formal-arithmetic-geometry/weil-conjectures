/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.HomComplexGlobalCochains
import Sheaf.Algebra.Homology.HomTensorTotal

/-! # Independence of the localized evaluation from a chain presentation

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96.
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

/-- Two chain presentations of the same literal derived input have the same localized
uncurried output. Object equalities and heterogeneous equalities record only transport
along equality, not transport along arbitrary isomorphisms. No family of functions is
asserted to exist here.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex, Tags 0A90, 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-representative-coherence).

Proof: Resolve L and L' by K-flat complexes. Hom into the fixed K-injective
resolutions and tensoring with P or P' invert these quasi-isomorphisms. On these
models, maps into the Hom complex are chain maps modulo homotopy, since Hom from
a K-flat complex into a K-injective complex is K-injective. Represent the equalities
of derived objects by the identity morphisms after equality transport, and compute
these morphisms by roofs on common K-flat resolutions. The equality of the input
morphisms makes the two resulting chain maps homotopic after these comparisons.
Uncurry the degree-minus-one components of this homotopy and extend them over the
coproduct defining the total tensor. The Hom differential formula gives a homotopy
between the uncurried chain maps: its boundary is their difference, with the same
Koszul signs as the total tensor differential. Evaluation commutes with all comparison
maps, by naturality of the sheaf tensor-Hom adjunction and the Hom projections;
verify this on every tensor summand and use the coproduct universal property.
Localizing the homotopy and cancelling the quasi-isomorphisms, with the natural
Hom resolution isomorphism, tensor model comparison and inverse augmentation,
gives the asserted equality after equality transport. Express it as HEq to avoid
choosing casts. This works for zero maps, zero complexes and unbounded complexes;
no injectivity or flatness of L or L' is assumed. -/
theorem tensorHomUncurry_representative_coherence (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L M P' L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlat) (hP' : P'.IsKFlat)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (φ' : P' ⟶ homComplex (R := X.sheaf) L'
      ((schemeHomKInjectiveResolution X).obj M'))
    (hK : DerivedCategory.Q.obj P = DerivedCategory.Q.obj P')
    (hL : DerivedCategory.Q.obj L = DerivedCategory.Q.obj L')
    (hM : DerivedCategory.Q.obj M = DerivedCategory.Q.obj M')
    (hφ : HEq (DerivedCategory.Q.map φ ≫
        (schemeDerivedInternalHomResolutionIso X L M).inv)
      (DerivedCategory.Q.map φ' ≫
        (schemeDerivedInternalHomResolutionIso X L' M').inv)) :
    HEq (pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
          schemeHomResolutionInverse X M)
      (pullbackTensorModelMap X P' L' ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P' L' M' φ') ≫
          schemeHomResolutionInverse X M') := by sorry

end AlgebraicGeometry
