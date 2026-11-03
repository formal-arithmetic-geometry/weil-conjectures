/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteHomSiteDescent.CoefFiniteHomSiteDescentModels

/-! # The tensor diagram for scalar/site comparison

Source: thm-coef-finite-hom.proof.md, final paragraph.
(blueprint: lem-coef-finite-hom-scalar-site-monoidal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.FiniteHomSiteDescent

/-- Tensor compatibility of the specified inverse scalar/site mate.

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md, final site-transport sentence; Stacks 03EL, 07A4.
(blueprint: lem-coef-finite-hom-scalar-site-monoidal).

Proof: first use the ordinary scalar adjunction and the geometric comparison
adjunction. Restriction of the site commutes sectionwise with coextension of
scalars. Taking the two mates and applying the unit/counit triangles identifies
the ordinary scalar/site mate with the canonical pullback/tensor comparison.
Its tensor diagram commutes on pure tensors: both paths pull back the two module
factors and multiply the two target-ring factors. This proves equality as
B-linear sheaf morphisms by the tensor universal property and sheafification.

Lift this diagram to cochain complexes with the signed total tensor. Use
flat-term K-flat resolutions, preserved by scalar extension and by the exact
comparison inverse image, to compute the derived tensorators. The derived
adjunction unit formula identifies the mate on these representatives with the
localization of the ordinary mate. The left-adjoint uniqueness isomorphism
`scalarResolutionIso` preserves that unit formula; consequently this is the
particular `scalarSiteMate`, with the particular `scalarTensor` and site tensor
structures in the statement. Localizing the cochain tensor diagram and using
naturality along the representative isomorphisms proves cotensorator
compatibility for all derived inputs. Invert the specified mate and apply the
strong-monoidal natural-isomorphism criterion: tensor compatibility implies
unit compatibility. This yields exactly the asserted monoidality of
`scalarSiteIso.hom`, without any flatness assumption on the ring homomorphism. -/
theorem scalarSiteIso_monoidal (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    let := scalarMonoidal X.smallEtaleTopology φ
    let := scalarMonoidal (ProEt.topology X) φ
    let := ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
    let := ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} B) X
    NatTrans.IsMonoidal (scalarSiteIso X φ).hom := by
  sorry

end AlgebraicGeometry.FiniteHomSiteDescent
