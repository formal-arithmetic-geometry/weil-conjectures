/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionCoordinates
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionOpenSquare
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCompositorSquare

/-! # Open comparison for the specified finite tensor realization

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: lem-sf-finite-intrinsic-projection-open-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open CompactSupportFiniteProjection FiniteIntrinsicProjectionCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntrinsicDerivedEquivalence

private theorem paste_open_tail
    {A : Type*} [Category A] {P Q R S T U V : A}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S} {out : S ⟶ T}
    {d : P ⟶ U} {e : U ⟶ R} {q : U ⟶ V} {z : V ⟶ T}
    (h₁ : a ≫ b = d ≫ e)
    (h₂ : e ≫ c ≫ out = q ≫ z) :
    a ≫ (b ≫ c) ≫ out = (d ≫ q) ≫ z := by
  calc
    a ≫ (b ≫ c) ≫ out = (a ≫ b) ≫ c ≫ out := by simp only [Category.assoc]
    _ = (d ≫ e) ≫ c ≫ out := by rw [h₁]
    _ = (d ≫ q) ≫ z := by
      simpa only [Category.assoc] using congrArg (fun t ↦ d ≫ t) h₂

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The open tensor map and inverse-image compositor commute with the specified
tensor realization. The proper projection mate does not occur.

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0E8I, 07A4.
(blueprint: lem-sf-finite-intrinsic-projection-open-factor).

Proof: transpose the intrinsic inverse open tensor map through the actual open
extension/restriction adjunction. Its transpose is the open unit tensored with
identity followed by inverse tensor/pullback comparison. The coefficient realization
preserves that unit: it is identity on sections over the open, and the unique map from
zero elsewhere. On simultaneous flat K-flat representatives the scalar tensor square
with open restriction sends each pure tensor to the same two sections. Localization
descends this equality, and injectivity of the open adjunction identifies the inverse
open tensor maps. The fixed open tensor map is an isomorphism, so transport through
the coefficient and tensor isomorphisms makes the intrinsic inverse open tensor map
invertible too. Thus inverseOnDomain is its actual inverse, and the equality also
identifies the forward open maps. For the remaining pullback compositor, the two
section-normalized comparisons are equal on every section by the inverse-image
unit uniqueness property. Their derived comparisons agree by the localization
universal property, including the equality cast from c.comm. Tensor naturality pastes
this compositor square onto the open square. Apply proper direct image and its
realization comparison. Expand targetComparison and fixedPullRealization: the
coefficient units cancel by the triangle identities; finitePullback and finiteSupport
are precisely the remaining displayed target factors. This yields the displayed
equation, without any proper projection or its invertibility. The argument applies
to zero inputs, identity opens, empty opens and m=0. -/
theorem finiteIntrinsicProjectionOpenFactor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    midpoint m f c K L U V k l ≫ fixedTail m f c K L ≫
        (targetComparison S f c K L).inv =
      ((proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing C.l E (m + 1))).map
          (SystemProjectionFormula.inverseOnDomain
            (SystemProjectionFormula.finiteOpenTensorInv C.l E D C.different c.i
              X.obj.hom (c.g ≫ Y.obj.hom) m U
              ((finiteDerivedPullback C.l E m c.g).obj V))) ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing C.l E (m + 1)) c).map
          ((finiteIntrinsicDerivedTensor C.l E X.obj.left m).map
            (Prod.mkHom (𝟙 U)
              (((SystemProjectionFormula.finitePullComp C.l E c.i c.g m).symm ≪≫
                eqToIso (congrArg (finiteDerivedPullback C.l E m) c.comm.symm)).hom.app V)))) ≫
      ((sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).map
        ((canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X).hom.app
          (U, (finiteDerivedPullback C.l E m f.hom.left).obj V) ≫
          (evaluatedTensor (C := C) (E := E) m X).map
            (Prod.mkHom k.hom ((finiteDerivedPullback C.l E m f.hom.left).map l.hom ≫
              (S.finitePullback f).inv.app ⟨L.obj, L.property.1⟩))) ≫
        (S.finiteSupport f c).inv.app
          (((partialTensor S X).obj K).obj ((torPull S f).obj L))) := by
  have h := paste_open_tail
    (finiteIntrinsicProjectionOpenSquare m f c K L U V k l)
    (finiteIntrinsicProjectionCompositorSquare m S f c K L U V k l)
  rw [fixedTail_parts m f c K L]
  simpa only [Category.assoc] using h

end WeilConjectures.IntegralProjectionReduction
