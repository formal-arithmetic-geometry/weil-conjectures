/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePartialPullbackTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePartialPullbackTensor
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionFixedCoordinates
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackTensorComposition
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePullbackCompositionFixedCoordinates
import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare

/-! # Tensor compatibility of normalized identity inverse image

Source: latest blueprint, part-appendices/sec-nagata-compactification/
sec-compactifications-and-refinements/sk-def-nagata-sketch-data/sk-prop-sf-pf-coherence/
prop-sf-pf-coherence.proof.md, first paragraph, identity sentence
(blueprint: lem-sf-projection-identity-tensor-unit).

The finite clause uses the published partial tensor comparison. The other three clauses
use ordinary condensed modules and the native derived tensorator and compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The finite coefficient clause, with arbitrary first input and finite-Tor second input.
Source: latest blueprint prop-sf-pf-coherence.proof.md, first paragraph, identity sentence
(blueprint: lem-sf-projection-identity-tensor-unit).
Proof: apply lem-sf-finite-partial-tensor-identity-composition to the explicit comparison.
Lift e through the full finite-Tor inclusion; faithfulness gives its naturality and its
normalization. Naturality at e_M gives U(e_M) = e_(UM). Postcompose the composition square
by tensor(e_(UM),e_(VL)). The two normalizations and naturality of the tensorator reduce
it to mu = c U(nu) mu, where nu = mu tensor(e_M,e_L). Cancel mu and c to get
U(nu) = e_(U(T(M,L))) = U(e_(T(M,L))). Naturality of e at nu and cancellation of its
invertible component give nu = e_(T(M,L)). This includes zero objects, the empty scheme
and n = 1, and imposes no Tor condition on M. -/
theorem finiteProjectionIdentity_tensorUnit
    (S : SixFunctorFiniteOperations D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (e : S.finite.pull (𝟙 X) ≅ 𝟭 (sixFunctorFiniteCategory D C E n hn X))
    (he : ∀ M : sixFunctorFiniteCategory D C E n hn X,
      (S.finite.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
          e.hom.app ((S.finite.pull (𝟙 X)).obj M) =
        eqToHom (congrArg (fun f ↦ (S.finite.pull f).obj M)
          (Category.id_comp (𝟙 X))))
    (M : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :
    (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
        ((CompactSupportFiniteProjection.partialTensor S X).map (e.hom.app M)).app
          ((CompactSupportFiniteProjection.torPull S (𝟙 X)).obj L) ≫
        ((CompactSupportFiniteProjection.partialTensor S X).obj M).map
          (ObjectProperty.isoMk (finiteTorConstructible C.l E n hn X.obj.left)
            (X := (CompactSupportFiniteProjection.torPull S (𝟙 X)).obj L) (Y := L)
            ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
              (e.app ⟨L.obj, L.property.1⟩))).hom =
      e.hom.app (((CompactSupportFiniteProjection.partialTensor S X).obj M).obj L) := by
  sorry

end WeilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

open MonoidalCategory

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Native identity inverse image restricted to the recorded bounded constructible category.
Source: latest blueprint prop-sf-pf-coherence.proof.md, identity sentence, and the
restriction convention of det-def-sf-operations
(blueprint: lem-sf-projection-identity-tensor-unit).
The canonical native identity comparison proves preservation; the functor itself is the
full-subcategory lift of native pullback, with its actual object and morphism maps. -/
def constructibleIdentityPullback (X : Scheme.{u}) :
    ConstantModelBoundedConstructible Λ X ⥤ ConstantModelBoundedConstructible Λ X :=
  (constantModelBoundedConstructible Λ X).lift
    ((constantModelBoundedConstructible Λ X).ι ⋙ L((𝟙 X)^*⟦Λ⟧))
    (fun K ↦ (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1.of_iso
      ((leftDerivedUpperStarId Λ X).app K.obj).symm K.property)

/-- The native condensed identity tensor equation, written through the faithful inclusion.
Source: latest blueprint prop-sf-pf-coherence.proof.md, first paragraph, identity sentence
(blueprint: lem-sf-projection-identity-tensor-unit).
The existential ranges only over proofs that the actual relative tensor is constructible;
it supplies the object property needed to evaluate e at that tensor, not a choice of tensor
or comparison. The normalization uses the raw native compositor and equality transport.
The conclusion uses the native tensorator and the two actual components of e. -/
def ConstructibleIdentityTensorEquation (X : Scheme.{u}) : Prop :=
  ∃ hT : ∀ M L : ConstantModelBoundedConstructible Λ X,
      constantModelBoundedConstructible Λ X (M.obj ⊗ L.obj),
    ∀ e : constructibleIdentityPullback Λ X ≅ 𝟭 (ConstantModelBoundedConstructible Λ X),
      (∀ M : ConstantModelBoundedConstructible Λ X,
        (leftDerivedUpperStarComp Λ (𝟙 X) (𝟙 X)).hom.app M.obj ≫
            (e.hom.app ((constructibleIdentityPullback Λ X).obj M)).hom =
          eqToHom (congrArg (fun f ↦ L((f)^*⟦Λ⟧).obj M.obj)
            (Category.id_comp (𝟙 X)))) →
      ∀ M L : ConstantModelBoundedConstructible Λ X,
        ((leftDerivedUpperStarTensorIso Λ (𝟙 X)).hom.app M.obj).app L.obj ≫
            ((e.hom.app M).hom ⊗ₘ (e.hom.app L).hom) =
          (e.hom.app ⟨M.obj ⊗ L.obj, hT M L⟩).hom

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

open AlgebraicGeometry.ProEtale.CondensedRing

/-- The three higher coefficient clauses in the ordinary condensed categories.
Source: latest blueprint prop-sf-pf-coherence.proof.md, first paragraph, identity sentence
(blueprint: lem-sf-projection-identity-tensor-unit).
Proof: the relative derived tensor restricts to bounded constructible objects at each of
these coefficients. Apply lem-sf-higher-tensor-identity-composition, the twice-identity
specialization of the native monoidality equation of lem-fix-condensed-pullback-coherence.
Put c = t inverse followed by the compositor. Naturality of e at its own components gives
U(e_M) = e_(UM). For nu = mu tensor(e_M,e_L), postcompose that composition square by
tensor(e_(UM),e_(UL)); the normalizations and naturality give mu = c U(nu) mu. Cancel mu
and compare with c e_(U(T(M,L))) = 1. Thus U(nu) = U(e_(T(M,L))). Naturality of e at nu
and cancellation give the required equation. Faithfulness of the constructible inclusion
identifies this ambient equation with the equation in the constructible category. The
argument includes zero objects and the empty scheme. All comparisons are the native ones.
-/
theorem condensedProjectionIdentity_tensorUnit
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : PadicAlgCl.FiniteIntermediateField C.l)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    ConstructibleIdentityTensorEquation (Profinite.padicIntegersRingObj C.l E) X.obj.left ∧
    ConstructibleIdentityTensorEquation (Profinite.continuousMapRingObj E) X.obj.left ∧
    ConstructibleIdentityTensorEquation (Profinite.padicAlgClRingObj C.l) X.obj.left := by
  sorry

end WeilConjectures
