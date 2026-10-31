/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VerdierHomChainCompositionData

/-! # Identity projection in the restricted tensor coordinates

Source: current blueprint, sec-six-functors/sk-prop-sf-pf-coherence,
prop-sf-pf-coherence.proof.md, identity calculation; and the identity calculation
in proof step 5 of lem-sf-verdier-hom-chain-composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures.VerdierHomChainComposition
open TensorHomCoefficientTransposes

variable {D : FiniteFieldDatum.{u}} {B : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic B.l) E]
  [FiniteDimensional (Padic B.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D B E n hn) (s : PodCoefficientStage)
  (X : SixFunctorSpace D)
  (R : Domain S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left))

/-- The identity pullback unit and the projection triangle, before any Hom or
exceptional transposition. The support unit is its prescribed ordinary/proper mate.
Source: prop-sf-pf-coherence.proof.md, identity clause, and proof step 5 of
lem-sf-verdier-hom-chain-composition
(blueprint: lem-sf-verdier-identity-projection).
Proof: take the normalized identity inverse-image comparison at the selected
coefficient stage and restrict it through the full finite-Tor inclusion. The
identity/self pullback compositor identifies pull(p_K) with its inverse component,
which gives the first equation. Conjugate the identity ordinary adjunction by p;
its unique right-adjoint comparison, after the specified proper identification,
is q. At the identity-open/proper compactification, expand the projection as the
proper counit tensor mate and the open unit tensor mate. Their triangle identities
cancel the units and counits and leave the tensor of q_M with the test identity.
Transport through the full inclusion and the tensor comparisons. Naturality of the
shared tensor comparison in M moves q_M through it; test naturality moves p_T
through it. Identify the two closed presentations by hclosed to obtain the displayed
triangle. This is the identity calculation of the projection-coherence proof,
which uses the operation datum alone. For integral coefficients perform the unit
calculation on completed systems before evaluation; raw localization and common
finite-stage inclusion preserve that equation for the two field stages. Empty
schemes and zero inputs require no exceptions; every component being cancelled
is an isomorphism, and the equality is an equality of actual morphisms. -/
theorem normalized_identity_projection
    (hclosed : R.closedX = R.closedY) (htensor : HEq R.tensorX R.tensorY)
    (hnatural : TensorPresentationNatural S s X R.closedX R.tensorX) :
    ∃ p : R.pull ≅ 𝟭 _,
      (∀ K : (PodCoefficientStage.domain S s X).FullSubcategory,
        (PodCoefficientStage.domain S s X).ι.map (R.pull.map (p.hom.app K)) =
          ((PodCoefficientStage.operations S s).pullComposition (𝟙 X) (𝟙 X)).inv.app
            K.obj) ∧
      let q : R.support ≅ 𝟭 _ :=
        ((PodCoefficientStage.domain S s X).fullyFaithfulι.whiskeringRight _).preimageIso
          (X := R.support) (Y := R.direct)
          (Functor.isoWhiskerLeft (PodCoefficientStage.domain S s X).ι
            ((PodCoefficientStage.operations S s).properIdentity (𝟙 X))) ≪≫
          R.ordinaryAdjunction.rightAdjointUniq (Adjunction.id.ofNatIsoLeft p.symm)
      ∀ M T : (PodCoefficientStage.domain S s X).FullSubcategory,
        PodCtfPairing.projection S s (𝟙 X) (.ofIsProper ((𝟙 X) : X ⟶ X).hom.left)
            R M T ≫
          q.hom.app ((tensorLeft R.closedX.closed.monoidal M).obj (R.pull.obj T)) ≫
          (tensorLeft R.closedX.closed.monoidal M).map (p.hom.app T) ≫
          (tensorCoordinate S s hclosed M T).hom =
        @MonoidalCategory.whiskerRight _ _ R.closedY.closed.monoidal.toMonoidalCategoryStruct
          _ _ (q.hom.app M) T := by sorry

end WeilConjectures.VerdierHomChainComposition
