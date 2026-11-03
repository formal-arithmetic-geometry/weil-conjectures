/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteHomSiteDescent.CoefFiniteHomSiteDescentModels

/-! # The tensor diagram for successive scalar extension

Source: thm-coef-finite-hom.proof.md, final paragraph.
(blueprint: lem-coef-finite-hom-scalar-assoc-monoidal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.FiniteHomSiteDescent

/-- Tensor compatibility of the specified adjunction scalar associator.

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md, penultimate sentence; Stacks 07A4.
(blueprint: lem-coef-finite-hom-scalar-assoc-monoidal).

Proof: on ordinary module sheaves the scalar associator sends
`(x tensor b) tensor r` to `x tensor (psi(b) * r)`. The tensor comparison and this
associator commute, since the two composites multiply the same target-ring
factors. Check the equality on pure tensors, then use the balanced tensor
universal property and sheafification. The corresponding total cochain maps
commute as well: their homogeneous components have the same Koszul sign.

Resolve both inputs by flat-term K-flat complexes. Each successive scalar
extension preserves this resolving class, so the two localized ordinary
extensions compute both successive and composite derived extensions. Normalize
their adjunction units against the ordinary scalar units. The scalar
restriction-composition isomorphism is the derived sectionwise restriction
identity. The adjunction-mate equation therefore identifies the localized
ordinary associator with the specified `Adjunction.leftAdjointCompIso` used in
`scalarAssoc`. In particular it identifies the actual associator, not an
unrelated natural isomorphism between the same functors.

The defining counit equation for `leftDerivedTensorComparison` identifies its
components on these representatives with the localized ordinary tensor maps.
Transport along `scalarResolutionIso`, whose defining uniqueness equation
preserves the scalar units. Localizing the cochain diagram now gives the
cotensorator equation for `scalarAssoc`. Every derived object admits the chosen
resolving representatives, so naturality gives that equation for all inputs.
The isomorphism tensor criterion supplies the unit equation and thus the stated
monoidality. No scalar extension is assumed exact; this includes nonflat maps
and identity maps, and it does not use any geometric site comparison. -/
theorem scalarAssoc_monoidal
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B R : Type (u + 1)}
    [CommRing A] [CommRing B] [CommRing R] (φ : A →+* B) (ψ : B →+* R) :
    let := scalarMonoidal J φ
    let := scalarMonoidal J ψ
    let := scalarMonoidal J (ψ.comp φ)
    NatTrans.IsMonoidal (scalarAssoc J φ ψ).hom := by
  sorry

end AlgebraicGeometry.FiniteHomSiteDescent
