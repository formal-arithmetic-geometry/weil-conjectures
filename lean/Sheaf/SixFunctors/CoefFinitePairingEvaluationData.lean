module

public import Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData

/-! # Finite normalization of the system projection-evaluation word

Source: blueprint latest, prop-coef-integral-dualizing.proof.md, paragraph 2;
Stacks 07A6 and 0B56 (blueprint: def-coef-finite-pairing-evaluation-data).

All point sections take values in ordinary derived categories of towers, before limits.
Index n denotes the positive coefficient exponent n + 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation of a site's derived tensor, fixed by pure tensors at every actual local
section, followed by the universal total-complex comparison of TensorEvaluation.
Source: Stacks 03EK, 06YT (blueprint: def-coef-finite-pairing-evaluation-data). -/
structure SiteTensorEvaluation (W : Scheme.{u}) (S : SystemTensor l E W)
    (n : ℕ) (f : FiniteSiteTensor l E W S.data n) extends
    TensorEvaluation (coefficientSequenceEvaluation.{u, u} l E W n)
      S.data.systemClosed.tensor (S.data.finiteClosed n).tensor S.localization f.localization
    where
  pure : ∀ (M N : coefficientSequenceModules.{u, u} l E W) (V : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj M).val.obj V)
    (y : ((coefficientSequenceEvaluation l E W n).obj N).val.obj V),
    HEq (((ordinary M N).hom.val.app V)
      (@SemilinearSections.tensorSection.{u + 1, u, u + 1}
        (ℕ × W.ProEt) _
        (coefficientSequenceTopology (ProEt.topology W))
        (ProEtale.VaryingRing.sequenceSiteSmall W)
        (coefficientSequenceCommRingSheaf l E W) M N (op (n, V.unop)) x y))
      (@SemilinearSections.tensorSection.{u + 1, u, u + 1} W.ProEt _
        (ProEt.topology W) (ProEtale.VaryingRing.siteSmall W)
        (integralCoefficientCommRingSheaf.{u, u} l E W n)
        ((coefficientSequenceEvaluation l E W n).obj M)
        ((coefficientSequenceEvaluation l E W n).obj N) V x y)

/-- Simultaneous finite comparison witnesses for the already specified system word.
Every comparison is fixed by ordinary sections, pure tensors, or adjunction units and
counits. Hom evaluation is its tensor-Hom transpose, not an arbitrary isomorphism.
Source: blueprint paragraph 2; Stacks 07A6, 08J9, 0B56
(blueprint: def-coef-finite-pairing-evaluation-data). -/
structure FiniteEvaluation {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
    (m : Model l E c) (s : ScalarSpecialization l E m) (n : ℕ) where
  finite : FiniteModel l E m n
  x : SiteTensorEvaluation l E X m.x n finite.x
  y : SiteTensorEvaluation l E Y m.y n finite.y
  z : SiteTensorEvaluation l E c.Z m.z n finite.z
  quotient : @TensorEvaluation
    (coefHomQuotientPointModules.{u, u} l E) (FinitePointModules l E n)
    _ _ _ _ _ _ _ _ _ _ _ _ (quotientEvaluation l E n) _ _ _
    m.point.qTensor finite.qTensor m.point.quotientLocalization finite.quotientLocalization
  integral : @TensorEvaluation
    (coefHomPointModules.{u, u} l E)
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
    _ _ _ _ _ _ _ _ _ _ _ _ ((evaluation ℕᵒᵖ _).obj (op n)) _ _ _
    m.point.rTensor finite.integralTensor
    m.point.integralLocalization finite.integralLocalization
  quotient_pure : ∀ (M N : coefHomQuotientPointModules.{u, u} l E)
    (x : M.obj (op n)) (y : N.obj (op n)),
    HEq ((quotient.ordinary M N).hom
      (ringTensorSection (pointRing l E) (coefHomPointQuotientRing l E)
        (pointRing_forget l E) M N (op n) x y))
      (x ⊗ₜ[compactSupportSystemLevel l E n] y)
  integral_pure : ∀ (M N : coefHomPointModules.{u, u} l E)
    (x : M.obj (op n)) (y : N.obj (op n)),
    HEq ((integral.ordinary M N).hom
      (x ⊗ₜ[ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)] y))
      (x ⊗ₜ[ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)] y)
  symmetry : ∀ H B : DerivedCategory (coefHomQuotientPointModules.{u, u} l E),
    (finitePointEvaluation l E n).map
        ((m.pointSymmetry.symmetry.toBraidedCategory.braiding H B).hom) ≫
        quotient.derived.hom.app (B, H) =
      quotient.derived.hom.app (H, B) ≫
        (finite.symmetry.toBraidedCategory.braiding
          ((finitePointEvaluation l E n).obj H) ((finitePointEvaluation l E n).obj B)).hom
  sectionsX : SectionsEvaluation l E X n
  sectionsY : SectionsEvaluation l E Y n
  gx : m.gx.left ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
    finitePointEvaluation l E n ⋙ finite.gx.left
  gy : m.gy.left ⋙ coefficientSequenceDerivedEvaluation l E Y n ≅
    finitePointEvaluation l E n ⋙ finite.gy.left
  r : m.r.left ⋙ finitePointEvaluation l E n ≅
    coefHomPointEvaluation l E n ⋙ finite.r.left
  gxUnit : ∀ T,
    (finitePointEvaluation l E n).map (m.gx.adjunction.unit.app T) ≫
        (sectionsX.derived).hom.app (m.gx.left.obj T) ≫
        (finiteDerivedSections l E X n).map (gx.hom.app T) =
      finite.gx.adjunction.unit.app ((finitePointEvaluation l E n).obj T)
  gxCounit : ∀ T,
    (coefficientSequenceDerivedEvaluation l E X n).map (m.gx.adjunction.counit.app T) =
      gx.hom.app _ ≫ finite.gx.left.map ((sectionsX.derived).hom.app T) ≫
        finite.gx.adjunction.counit.app ((coefficientSequenceDerivedEvaluation l E X n).obj T)
  gyUnit : ∀ T,
    (finitePointEvaluation l E n).map (m.gy.adjunction.unit.app T) ≫
        (sectionsY.derived).hom.app (m.gy.left.obj T) ≫
        (finiteDerivedSections l E Y n).map (gy.hom.app T) =
      finite.gy.adjunction.unit.app ((finitePointEvaluation l E n).obj T)
  gyCounit : ∀ T,
    (coefficientSequenceDerivedEvaluation l E Y n).map (m.gy.adjunction.counit.app T) =
      gy.hom.app _ ≫ finite.gy.left.map ((sectionsY.derived).hom.app T) ≫
        finite.gy.adjunction.counit.app ((coefficientSequenceDerivedEvaluation l E Y n).obj T)
  rUnit : ∀ T,
    (coefHomPointEvaluation l E n).map (m.r.adjunction.unit.app T) ≫
        (restrictionEvaluation l E n).hom.app (m.r.left.obj T) ≫
        (finiteDerivedRestriction l E n).map (r.hom.app T) =
      finite.r.adjunction.unit.app ((coefHomPointEvaluation l E n).obj T)
  rCounit : ∀ T,
    (finitePointEvaluation l E n).map (m.r.adjunction.counit.app T) =
      r.hom.app _ ≫ finite.r.left.map ((restrictionEvaluation l E n).hom.app T) ≫
        finite.r.adjunction.counit.app ((finitePointEvaluation l E n).obj T)
  properCounit : ∀ U : coefficientSequenceDerived.{u, u} l E c.Z,
    (coefficientSequenceDerivedEvaluation l E c.Z n).map
        ((ProEtale.VaryingRing.adj (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g).counit.app U) =
      (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g n).hom.app _ ≫
      (finitePull l E c.g n).map
        ((ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g n).hom.app U) ≫
      (finiteAdjunction l E c.g n).counit.app
        ((coefficientSequenceDerivedEvaluation l E c.Z n).obj U)
  properUnit : ∀ L : coefficientSequenceDerived.{u, u} l E Y,
    (coefficientSequenceDerivedEvaluation l E Y n).map
        ((ProEtale.VaryingRing.adj (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g).unit.app L) ≫
      (ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g n).hom.app _ ≫
      (finitePush l E c.g n).map
        ((ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g n).hom.app L) =
      (finiteAdjunction l E c.g n).unit.app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj L)
  xSymmetry : ∀ U V : coefficientSequenceDerived.{u, u} l E X,
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((m.x.symmetry.toBraidedCategory.braiding U V).hom) ≫
        x.derived.hom.app (V, U) = x.derived.hom.app (U, V) ≫
      (finite.x.symmetry.toBraidedCategory.braiding
        ((coefficientSequenceDerivedEvaluation l E X n).obj U)
        ((coefficientSequenceDerivedEvaluation l E X n).obj V)).hom
  gxTensor : StrongTensorEvaluation m.gxTensor.comparison finite.gxTensor.comparison
    (finitePointEvaluation l E n) (coefficientSequenceDerivedEvaluation l E X n)
    gx quotient.derived x.derived
  gyTensor : StrongTensorEvaluation m.gyTensor.comparison finite.gyTensor.comparison
    (finitePointEvaluation l E n) (coefficientSequenceDerivedEvaluation l E Y n)
    gy quotient.derived y.derived
  rTensor : StrongTensorEvaluation m.rTensor.comparison finite.rTensor.comparison
    (coefHomPointEvaluation l E n) (finitePointEvaluation l E n)
    r integral.derived quotient.derived
  properTensor : StrongTensorEvaluation m.properTensor finite.properTensor
    (coefficientSequenceDerivedEvaluation l E Y n)
    (coefficientSequenceDerivedEvaluation l E c.Z n)
    (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g n) y.derived z.derived
  composition : ∀ H : DerivedCategory (coefHomQuotientPointModules.{u, u} l E),
    (coefficientSequenceDerivedEvaluation l E X n).map (m.sectionsPullback.hom.app H) ≫
        gx.hom.app H =
      (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) a n).hom.app (m.gy.left.obj H) ≫
        (finitePull l E a n).map (gy.hom.app H) ≫
        finite.composition.hom.app ((finitePointEvaluation l E n).obj H)
  pullbackComposition : ∀ L : coefficientSequenceDerived.{u, u} l E Y,
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((Model.compactificationPullback (l := l) (E := E) (c := c)).hom.app L) ≫
      (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) a n).hom.app L =
    (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i n).hom.app
        ((ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g).obj L) ≫
      (finitePull l E c.i n).map
        ((ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g n).hom.app L) ≫
      finite.compactificationPullback.hom.app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj L)
  gamma : ∀ (U : coefficientSequenceDerived.{u, u} l E X)
    (L : coefficientSequenceDerived.{u, u} l E c.Z),
    (coefficientSequenceDerivedEvaluation l E c.Z n).map
        ((CoefSupportOpenTensor.systemGamma l E c.i m.x.data m.z.data m.openTensor).hom.app
          (U, L)) ≫
      (ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i n).hom.app
          (m.x.data.systemClosed.tensor.obj (U,
            (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
              (compactSupportSystemQuotient l E) c.i).obj L)) ≫
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) c.i).mapDerivedCategory.map
        (x.derived.hom.app (U,
          (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) c.i).obj L)) ≫
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) c.i).mapDerivedCategory.map
        ((m.x.data.finiteClosed n).tensor.map (Prod.mkHom (𝟙 _)
          ((ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) c.i n).hom.app L))) =
    z.derived.hom.app
        ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.i).obj U, L) ≫
      (m.z.data.finiteClosed n).tensor.map (Prod.mkHom
        ((ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.i n).hom.app U) (𝟙 _)) ≫
      (CoefSupportOpenTensor.finiteGamma l E c.i m.x.data m.z.data n finite.openTensor).hom.app
        ((coefficientSequenceDerivedEvaluation l E X n).obj U,
          (coefficientSequenceDerivedEvaluation l E c.Z n).obj L)
  hom : ∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (N : coefficientSequenceDerived.{u, u} l E X),
    (coefficientSequenceDerivedEvaluation l E X n).obj (Model.hom (s.reduced K) N) ≅
      (coefficientFiniteInternalHom l E X n).obj
        (op ((coefficientSequenceDerivedEvaluation l E X n).obj (s.reduced K)),
          (coefficientSequenceDerivedEvaluation l E X n).obj N)
  hom_normalization : ∀ K N,
    (hom K N).hom = coefficientBaseChangeHom m.x.data.systemClosed
      (m.x.data.finiteClosed n) (coefficientSequenceDerivedEvaluation l E X n)
      x.derived (s.reduced K) N




end WeilConjectures.CoefProjectionEvaluation
