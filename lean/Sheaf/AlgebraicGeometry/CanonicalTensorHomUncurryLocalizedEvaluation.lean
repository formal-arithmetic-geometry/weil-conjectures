/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # Localized evaluation and chain-map composition

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-localized-evaluation).
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

/-- The localized evaluation composite is natural for actual Hom-complex inputs.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-localized-evaluation).

Proof: Put ψ = a followed by φ followed by Hom(b,I(c)). Restrict U(ψ) and
Tot(a tensor b) followed by U(φ) followed by I(c) to the summand P'^p tensor L'^q
in total degree n = p+q. The projection equation in homComplex_exists identifies
ψ's projection with a_p followed by φ's projection followed by Hom(b_q,I(c)_n).
Naturality of SheafOfModules.tensorHomEquiv and of the symmetry identifies its
uncurrying with (a_p tensor b_q) followed by U(φ)'s component followed by I(c)_n.
The summand equation schemeTensorHomUncurry_component and coproduct
extensionality therefore give equality of the two chain maps. Apply Q. The
lax-monoidal comparison μ is natural in both chain variables, so
(Qa tensor Qb);μ(P,L) = μ(P',L');Q Tot(a tensor b). Finally the augmentation
M -> I(M) is natural in c, hence QI(c);(Qη_M')⁻¹ = (Qη_M)⁻¹;Qc.
Associativity gives precisely the stated equality. No K-flatness or lift of an
arbitrary derived arrow is needed. For identities this is reflexive; for zero
maps component evaluation is zero; all total degrees and unbounded complexes
use the same coproduct extensionality. -/
theorem schemeTensorHomUncurry_localized_evaluation (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P P' L L' M M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : P' ⟶ P) (b : L' ⟶ L) (c : M ⟶ M')
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) :
    letI := schemeDerivedTensorMonoidal X
    pullbackTensorModelMap X P' L' ≫
      DerivedCategory.Q.map (schemeTensorHomUncurry X P' L' M'
        (a ≫ φ ≫ (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
          (X := (op L, (schemeHomKInjectiveResolution X).obj M))
          (Y := (op L', (schemeHomKInjectiveResolution X).obj M'))
          (b.op, (schemeHomKInjectiveResolution X).map c))) ≫
        schemeHomResolutionInverse X M' =
      (DerivedCategory.Q.map a ⊗ₘ DerivedCategory.Q.map b) ≫
        (pullbackTensorModelMap X P L ≫
          DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
            schemeHomResolutionInverse X M) ≫ DerivedCategory.Q.map c := by sorry

end AlgebraicGeometry
