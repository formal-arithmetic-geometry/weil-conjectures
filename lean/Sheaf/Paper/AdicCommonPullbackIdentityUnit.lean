/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

/-! # Identity unit for the specified common-stage pullback compositor

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

/-- The identity pullback unit cancels the specified twice-identity compositor.
Source: BS Remark 6.8.15; Stacks 07A4 and 0941; the source-identity part of
lem-sf-adic-reindexing-core (blueprint: lem-sf-adic-common-pullback-identity-unit).

Proof: On finite coefficient complexes use the usual inverse-image identity map. Its
composition with the twice-identity pullback compositor is the identity, by the identity
adjunction and the sectionwise tensor unit formula. Passage to the completed integral
pullback preserves this equation: its comparison and the specified compositor are fixed
by the coherent quotient-system factorization, including the completion unit. Localize
the identity components and their inverses to the raw rational category. The scalar
extension comparison commutes with the identity maps, since both are induced by the
same identity on integral sections. At a common-stage object use its own finite field
and the rational identity component, inserting the literal-object transports from the
pullback specification. Common-field arrow representatives and the scalar square prove
naturality, so these components define a natural isomorphism. The defining representative
equation of pullbackTensorCommonComposition reduces the asserted cancellation to the
rational cancellation at that field. The endpoint transports account for the HEq. -/
theorem exists_common_pullback_identity_unit (D : FiniteFieldDatum.{u})
    (T : GeometricSpace D)
    [∀ x : T.base.left, Invertible (l : T.base.left.residueField x)] :
    ∃ e : commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left) ≅ 𝟭 _,
    ∀ M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left,
      HEq
        ((pullbackTensorCommonComposition l (PadicAlgCl l) (𝟙 T.base.left) (𝟙 T.base.left) M).hom ≫
          e.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
        (𝟙 ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M)) := by
  sorry

end WeilConjectures.AdicQbarRealization
