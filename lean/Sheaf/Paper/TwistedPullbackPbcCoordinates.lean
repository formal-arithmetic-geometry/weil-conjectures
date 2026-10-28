/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module
public import Sheaf.Paper.TwistedPullbackSquareMaps
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.FdCoefficientComparison

/-! # Normalized raw PBC presentation and scalar coordinates

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
common integral objects and coefficient presentation
(blueprint: def-pur-twisted-pullback-pbc-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The presentation equivalence, with its actual integral restriction and its action
on every localized pure tensor. No completion of the raw object set is allowed.
Source: purity transport, common integral objects and coefficient presentation
(blueprint: def-pur-twisted-pullback-pbc-coordinates). -/
structure Presentation (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))] where
  integral : sfIntegralConstructibleCategory l E W ≌
    PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)
  integral_identity : integral.functor ⋙ ObjectProperty.ι (PbcIsBoundedConstructibleComplete
      W (pbcIntegralDatum l E)) =
    (sfIntegralConstructible l E W).ι ⋙ integralDetailedTransport W l E
  integralShift : integral.functor.CommShift ℤ
  integral_shift_normalization : ∀ (n : ℤ) K,
    HEq ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E))).map
        ((Functor.commShiftIso integral.functor (self := integralShift) n).hom.app K) ≫
      ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E))).commShiftIso
        n).hom.app (integral.functor.obj K))
      ((integralDetailedTransport W l E).map
        (((sfIntegralConstructible l E W).ι.commShiftIso n).hom.app K) ≫
      ((fdCoefficientTransport l E W).mapDerivedCategory.commShiftIso n).hom.app K.obj)
  rational : sfRationalConstructibleCategory l E W ≌
    PbcRationalCategory W (pbcIntegralDatum l E) (pbcUniformizer l E)
  rationalShift : rational.functor.CommShift ℤ
  rational_shift_normalization : ∀ (n : ℤ) K,
    HEq (rational.functor.map
        (((sfRationalConstructibleLocalization l E W).commShiftIso n).hom.app K) ≫
      (Functor.commShiftIso rational.functor (self := rationalShift) n).hom.app
        ((sfRationalConstructibleLocalization l E W).obj K))
      ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).map
          ((Functor.commShiftIso integral.functor (self := integralShift) n).hom.app K) ≫
        ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).commShiftIso n).hom.app
          (integral.functor.obj K))
  objects : ∀ K, rational.functor.obj K = ⟨integral.functor.obj K.obj⟩
  tensors : ∀ (K N : sfIntegralConstructibleCategory l E W)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) (b : K ⟶ N),
    HEq (rational.functor.map
      (fdRawTensor (Padic.coefficientExtensionUniformizer l E) a b))
      (fdRawTensor (pbcUniformizer l E)
        ((pbcRationalCoefficientEquiv l E).symm (sfRationalCoefficientEquiv l E a))
        (integral.functor.map b))

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

/-- Actual integral scalar extension in the framework constructible category.
Source: the scalar extension convention
(blueprint: def-pur-twisted-pullback-pbc-coordinates). -/
abbrev integralScalar (W : Scheme.{u}) :=
  sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero E L i W

/-- The normalized scalar-presentation comparison. Applying Phi fixes the ambient
map by the specified ordinary scalar model, completion chi, and the equivalence
counits. The rational comparison is its localized restriction, including the
specified integral/rational scalar comparison.
Source: purity transport, identification of the specified scalar functors
(blueprint: def-pur-twisted-pullback-pbc-coordinates). -/
structure ScalarCoordinates (W : Scheme.{u}) [IsNoetherian W]
    [dW : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [iW : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]
    (JE : Presentation l E W) (JL : Presentation l L W) where
  ambient : (sfIntegralConstructible l E W).ι ⋙ integralDetailedTransport W l E ⋙
      pbcEmbeddingAmbientTensor l E L i W ≅
    integralScalar l E L i W ⋙ (sfIntegralConstructible l L W).ι ⋙
      integralDetailedTransport W l L
  normalization : ∀ K : sfIntegralConstructibleCategory l E W,
    HEq ((purCoefficientModel l L W).functor.map (ambient.hom.app K))
      ((purScalarModel l E L i W).hom.app
          ((integralDetailedTransport W l E).obj K.obj) ≫
        (integralOrdinaryDerivedScalar l E L i W).map
          ((purCoefficientModel l E W).counitIso.hom.app K.obj) ≫
        (scalarCompletionIso l E L i W K.obj K.property.1).hom ≫
        (purCoefficientModel l L W).counitIso.inv.app
          ((integralScalarExtension l E L i W).obj K.obj))
  integral : JE.integral.functor ⋙ pbcEmbeddingIntegralTensor l E L i W dW.out iW.out ≅
    integralScalar l E L i W ⋙ JL.integral.functor
  integral_lift : ∀ K, HEq (integral.hom.app K).hom (ambient.hom.app K)
  rational : JE.rational.functor ⋙ pbcRationalScalarExtension l E L i W dW.out iW.out ≅
    T l E L i W ⋙ JL.rational.functor
  rationalization : ∀ K : sfIntegralConstructibleCategory l E W,
    HEq (rational.hom.app ((sfRationalConstructibleLocalization l E W).obj K))
      ((pbcScalarLocalizationIso l E L i W).inv.app (JE.integral.functor.obj K) ≫
        (pbcRationalization W (pbcIntegralDatum l L) (pbcUniformizer l L)).map
          (integral.hom.app K))

end WeilConjectures.TwistedPullbackScalars
