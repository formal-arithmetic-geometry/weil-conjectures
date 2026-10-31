/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralComparisons
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.DirectImagesConstructible

/-! # FieldExtensionRationalModels

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: def-sp-field-extension-rational-models).

## Main definitions and statements

The declarations below package the named functors, comparisons and equations of
the indicated clauses, using the published coefficient and geometric models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
variable (P : PurityFiniteSetting.{u})
variable (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

/-- Extension of an integral functor to the raw rational Hom tensors, specified on
unchanged objects and every pure tensor. Source: clause (3)
(blueprint: def-sp-field-extension-rational-models). -/
structure Localization (E : FieldShriekSystem.Index P) (T U : Scheme.{u})
    (F : Integral P E T ⥤ Integral P E U) where
  functor : Rational P E T ⥤ Rational P E U
  [additive : functor.Additive]
  objects : ∀ K : Rational P E T, functor.obj K = ⟨F.obj K.obj⟩
  tensors : ∀ (K L : Integral P E T) (f : K ⟶ L)
    (c : _root_.Localization.Away (Padic.coefficientExtensionUniformizer
      P.coefficients.l E.val)),
    HEq (functor.map (c ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l E.val] f :
      (sfRationalConstructibleLocalization P.coefficients.l E.val T).obj K ⟶
        (sfRationalConstructibleLocalization P.coefficients.l E.val T).obj L))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l E.val] F.map f)

/-- The inverse of ell in every residue field, transported from the fixed base field.
Source: standing ell distinct from p (blueprint: def-sp-field-extension-rational-models). -/
@[instance_reducible] def residueInvertible (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] : ∀ x : T, Invertible (P.coefficients.l : T.residueField x) :=
  fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit P.field P.coefficients.l
      P.coefficients.different).map
        ((T ↘ Spec (.of P.field.k)).residueFieldAlgebraMap x) :
          IsUnit (P.coefficients.l : T.residueField x)).invertible

/-- The existing rational pullback followed by the intrinsic signed twist and shift.
All residue-field inverse instances come from the finite-field datum.
Source: clause (3), second displayed comparison
(blueprint: def-sp-field-extension-rational-models). -/
def rationalPuritySource (E : FieldShriekSystem.Index P) : Rational P E Y ⥤ Rational P E X :=
  letI := residueInvertible P X
  letI := residueInvertible P Y
  rationalDerivedPullback P.coefficients.l E.val (j ≫ p) ⋙
    sfRationalTwistingFunctor P.coefficients.l E.val X (d : ℤ) ⋙
      shiftFunctor (Rational P E X) (2 * (d : ℤ))

/-- The rational source identification is the localized tensor completion unit,
followed by the canonical commutation of localization with the indicated shift.
It is fixed on every integral object and is independent of purity.
Source: clause (3) (blueprint: def-sp-field-extension-rational-models). -/
@[irreducible] def rationalSourceIdentificationNormalized
    (E : FieldShriekSystem.Index P) (m : IntegralModel P D E j p d)
    (source : Localization P E Y X (puritySource P D j p d m))
    (sourceIdentification : source.functor ≅ rationalPuritySource P j p d E) : Prop :=
  ∀ K : Integral P E Y,
    HEq (sourceIdentification.hom.app
      ((sfRationalConstructibleLocalization P.coefficients.l E.val Y).obj K))
      ((sfRationalConstructibleLocalization P.coefficients.l E.val X).map
        (ObjectProperty.homMk
          (sourceCompletion P E.val (j ≫ p) d m.sourceNormalization K) :
            (puritySource P D j p d m).obj K ⟶
              completedSourceObject P E.val (j ≫ p) d m.sourceNormalization K) ≫
        ((sfRationalConstructibleLocalization P.coefficients.l E.val X).commShiftIso
          (2 * (d : ℤ))).hom.app
            (completedTensorObject P E.val (j ≫ p) d m.sourceNormalization K))

/-- Rational adjunction and purity are literal localizations, on all integral
representatives, of the recorded integral ones. The source is identified with the
published rational twisted shifted pullback by localization of the actual tensor
completion unit; it is independent of the purity map. Source: clause (3)
(blueprint: def-sp-field-extension-rational-models). -/
structure RationalModel (E : FieldShriekSystem.Index P) (m : IntegralModel P D E j p d) where
  support : Localization P E X Y (support P D j p d m)
  exceptional : Localization P E Y X (exceptional P D j p d m)
  source : Localization P E Y X (puritySource P D j p d m)
  sourceIdentification : source.functor ≅ rationalPuritySource P j p d E
  sourceIdentification_normalized :
    rationalSourceIdentificationNormalized P D j p d E m source sourceIdentification
  adjunction : support.functor ⊣ exceptional.functor
  unit : ∀ M : Integral P E X,
    HEq (adjunction.unit.app
      ((sfRationalConstructibleLocalization P.coefficients.l E.val X).obj M))
      ((sfRationalConstructibleLocalization P.coefficients.l E.val X).map
        (m.realization.adjunction.unit.app M))
  counit : ∀ K : Integral P E Y,
    HEq (adjunction.counit.app
      ((sfRationalConstructibleLocalization P.coefficients.l E.val Y).obj K))
      ((sfRationalConstructibleLocalization P.coefficients.l E.val Y).map
        (m.realization.adjunction.counit.app K))
  gamma : source.functor ≅ exceptional.functor
  purity : ∀ K : Integral P E Y,
    HEq (gamma.hom.app
      ((sfRationalConstructibleLocalization P.coefficients.l E.val Y).obj K))
      ((sfRationalConstructibleLocalization P.coefficients.l E.val X).map
        (FieldExtensionTowers.gamma P D j p d m K))

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
