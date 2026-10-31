/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientConventions
public import WeilConjectures.AlgebraicGeometry.PurityDiagonalDualizingObject
public import WeilConjectures.AlgebraicGeometry.AdicSmoothDualizingIntegralDetection
public import WeilConjectures.AlgebraicGeometry.TraceFormulaLocalFrobeniusOperator
public import WeilConjectures.AlgebraicGeometry.CoefficientDuality
public import WeilConjectures.AlgebraicGeometry.IntegralConstructibleInternalHom
public import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
public import WeilConjectures.AlgebraicGeometry.FiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.GeometricCommonStageDirectImage
public import WeilConjectures.AlgebraicGeometry.SystemOperationExchangeRealization
public import WeilConjectures.CategoryTheory.SemilinearScalarLocalization
public import WeilConjectures.AlgebraicGeometry.ExceptionalAdjointAdmissibility
public import WeilConjectures.AlgebraicGeometry.PurityTateDatum
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.GlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.OrdinaryCompactCohomology

/-! # Poincare duality conventions

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-cor-sp-all-coefficients/def-pod-conventions.md`
(blueprint: def-pod-conventions).

The structure records the global finite-field, coefficient, smooth geometric and
exceptional-adjoint data used by the Poincare-duality statements.  Its projections
reuse the recorded categories, operations, Frobenius and geometric-fibre constructions.

## Main definitions
* `PoincareDualityConventions`: the fixed field, coefficients and geometric hypotheses.
* `PoincareDualityConventions.coefficientOperation`: the recorded exceptional adjunctions.
* `PoincareDualityConventions.finiteOrientation` and the three higher orientations.
* `PoincareDualityConventions.pointDual` and the four coefficient and Verdier duals.
* The four ordinary/compact cohomology and Frobenius conventions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures

/-- The exact finite-stage exceptional-adjoint predicate for the structure morphism.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-cor-sp-all-coefficients/def-pod-conventions.md`
(blueprint: def-pod-conventions). -/
noncomputable def poincareExceptionalAdmissibility
    (B : TraceFormulaCoefficientConventions.{u}) (n : ℕ) (hn : 1 ≤ n) : Prop := by
  let S : Scheme := Spec (CommRingCat.of B.datum.k)
  let X := B.geometricBaseChange
  letI : X.Over S := ⟨B.structureMap⟩
  let f : X ⟶ S := X ↘ S
  letI : S.Over S := ⟨𝟙 S⟩
  letI : LocallyOfFiniteType (X ↘ S) := B.geometricFiniteType
  letI : QuasiCompact (X ↘ S) := B.geometricQuasiCompact
  letI : IsSeparated (X ↘ S) := B.geometricSeparated
  let hS : ∀ t : S, IsUnit (B.coefficients.l : S.presheaf.stalk t) := by
    intro t
    let φ : B.datum.k →+* S.presheaf.stalk t :=
      (S.presheaf.germ ⊤ t trivial).hom.comp
        (Scheme.ΓSpecIso (.of B.datum.k)).inv.hom
    simpa only [map_natCast] using (finiteFieldDatumPrimeUnit B.datum
      B.coefficients.l B.coefficients.different).map φ
  letI := hasCompactification_of_finiteType_over_field B.datum.k X S f
  exact IsExceptionalAdjointAdmissibleAtFiniteStage B.coefficients.l B.extension.val n hn
    S X S hS f (HasCompactification.compactification f)

/-- The Poincare-duality convention package.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-cor-sp-all-coefficients/def-pod-conventions.md`
(blueprint: def-pod-conventions).

The fields fix the finite field datum, a finite coefficient extension and positive
level, a smooth separated geometrically connected finite-type model of pure dimension
`d`, and exceptional-adjoint admissibility at every finite coefficient stage.  The
inherited fields provide the coefficient ring, geometric base change and the finite
constructible derived pullback, tensor and internal-Hom operations.
-/
structure PoincareDualityConventions where
  datum : FiniteFieldDatum.{u}
  coefficients : datum.CoefficientDatum
  extension : Padic.FiniteCoefficientFields coefficients.l coefficients.Qbar
  level : ℕ
  level_pos : 1 ≤ level
  X₀ : Over (Spec (CommRingCat.of datum.k₀))
  [finite_type : LocallyOfFiniteType X₀.hom]
  [quasi_compact : QuasiCompact X₀.hom]
  [separated : IsSeparated X₀.hom]
  d : ℕ
  [smooth : SmoothOfRelativeDimension d X₀.hom]
  [geometrically_connected : GeometricallyConnected X₀.hom]
  exceptional_adjoint_admissible : ∀ (n : ℕ) (hn : 1 ≤ n),
    poincareExceptionalAdmissibility
      ⟨datum, coefficients, extension, level, level_pos, X₀⟩ n hn

attribute [instance] PoincareDualityConventions.smooth
  PoincareDualityConventions.geometrically_connected
  PoincareDualityConventions.finite_type PoincareDualityConventions.quasi_compact
  PoincareDualityConventions.separated

namespace PoincareDualityConventions

/-- Trace-formula coordinates constructed from the independently fixed setting fields.
Source: finite-field and coefficient conventions [def-weil-finite-field-fiber], and
[def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
noncomputable abbrev base (P : PoincareDualityConventions.{u}) :
    TraceFormulaCoefficientConventions.{u} :=
  ⟨P.datum, P.coefficients, P.extension, P.level, P.level_pos, P.X₀⟩

/-- The fixed geometric fibre `X = X₀ × k`.
Source: [def-weil-finite-field-fiber] (blueprint: def-pod-conventions). -/
noncomputable abbrev X (P : PoincareDualityConventions.{u}) : Scheme.{u} :=
  P.base.geometricBaseChange

/-- The geometric point `s = Spec k`.
Source: [def-weil-finite-field-fiber] (blueprint: def-pod-conventions). -/
noncomputable abbrev s (P : PoincareDualityConventions.{u}) : Scheme.{u} :=
  Spec (CommRingCat.of P.base.datum.k)

/-- The structure morphism `a_X : X → s`.
Source: [def-weil-finite-field-fiber] (blueprint: def-pod-conventions). -/
noncomputable abbrev structureMap (P : PoincareDualityConventions.{u}) :
    P.X ⟶ P.s := P.base.structureMap

/-- The geometric fibre is over the fixed geometric point by its actual structure map.
Source: [def-weil-finite-field-fiber] (blueprint: def-pod-conventions). -/
instance geometricOver (P : PoincareDualityConventions.{u}) : P.X.Over P.s :=
  ⟨P.structureMap⟩

/-- Finite type survives the geometric base change.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance geometricFiniteType (P : PoincareDualityConventions.{u}) :
    LocallyOfFiniteType (P.X ↘ P.s) := P.base.geometricFiniteType

/-- Quasi-compactness survives the geometric base change.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance geometricQuasiCompact (P : PoincareDualityConventions.{u}) :
    QuasiCompact (P.X ↘ P.s) := P.base.geometricQuasiCompact

/-- Separatedness survives the geometric base change.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance geometricSeparated (P : PoincareDualityConventions.{u}) :
    IsSeparated (P.X ↘ P.s) := P.base.geometricSeparated

/-- Smoothness of the fixed pure dimension survives the geometric base change.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance geometricSmooth (P : PoincareDualityConventions.{u}) :
    SmoothOfRelativeDimension P.d (P.X ↘ P.s) := by
  change SmoothOfRelativeDimension P.d
    (pullback.snd P.X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap P.datum.k₀ P.datum.k))))
  infer_instance

/-- Smoothness stated on the explicitly named structure morphism.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance structureSmooth (P : PoincareDualityConventions.{u}) :
    SmoothOfRelativeDimension P.d P.structureMap :=
  inferInstanceAs (SmoothOfRelativeDimension P.d (P.X ↘ P.s))

/-- Finite type on the named structure morphism.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance structureFiniteType (P : PoincareDualityConventions.{u}) :
    LocallyOfFiniteType P.structureMap :=
  inferInstanceAs (LocallyOfFiniteType (P.X ↘ P.s))

/-- Quasi-compactness on the named structure morphism.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance structureQuasiCompact (P : PoincareDualityConventions.{u}) :
    QuasiCompact P.structureMap :=
  inferInstanceAs (QuasiCompact (P.X ↘ P.s))

/-- Separatedness on the named structure morphism.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance structureSeparated (P : PoincareDualityConventions.{u}) :
    IsSeparated P.structureMap :=
  inferInstanceAs (IsSeparated (P.X ↘ P.s))

/-- The same selected coefficients in the recorded purity interface.
Source: [thm-pur-diagonal-dualizing-object] (blueprint: def-pod-conventions). -/
noncomputable abbrev puritySetting (P : PoincareDualityConventions.{u}) : PurityFiniteSetting.{u} :=
  ⟨P.datum, P.coefficients, P.extension.val, P.level, P.level_pos⟩

/-- The structure morphism is an arrow over the geometric coefficient field.
Source: [cor-pur-adic-and-rational-smooth-dualizing-complexes]
(blueprint: def-pod-conventions). -/
instance structureIsOver (P : PoincareDualityConventions.{u}) :
    P.structureMap.IsOver (Spec (.of P.datum.k)) :=
  AdicSmoothDualizing.structureIsOver P.puritySetting P.X

/-- The finite coefficient ring `A = O_E / ϖ_E^n`.
Source: [def-weil-finite-coefficient-point] (blueprint: def-pod-conventions). -/
noncomputable abbrev coefficientRing (P : PoincareDualityConventions.{u}) : Type u :=
  Padic.coefficientExtensionRing P.coefficients.l P.extension.val P.level

/-- The finite-Tor constructible category at the chosen coefficient stage.
Source: [def-weil-finite-tor-amplitude] (blueprint: def-pod-conventions). -/
noncomputable abbrev finiteTorCategory (P : PoincareDualityConventions.{u}) :=
  finiteTorConstructibleCategory P.coefficients.l P.extension.val P.level P.level_pos P.X

/-- The finite-stage derived pullback.
Source: [def-weil-derived-pullback-tensor-hom] (blueprint: def-pod-conventions). -/
noncomputable def derivedPullback (P : PoincareDualityConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    proEtaleDerivedCategory Z P.coefficientRing ⥤
      proEtaleDerivedCategory Y P.coefficientRing :=
  by
    unfold coefficientRing
    rw [← Nat.sub_add_cancel P.level_pos]
    exact finiteDerivedPullback P.coefficients.l P.extension.val (P.level - 1) f

/-- The finite-stage derived tensor.
Source: [def-weil-derived-pullback-tensor-hom] (blueprint: def-pod-conventions). -/
noncomputable def derivedTensor (P : PoincareDualityConventions.{u}) :
    proEtaleDerivedCategory P.X P.coefficientRing ×
      proEtaleDerivedCategory P.X P.coefficientRing ⥤
        proEtaleDerivedCategory P.X P.coefficientRing := by
  unfold coefficientRing
  rw [← Nat.sub_add_cancel P.level_pos]
  exact finiteIntrinsicDerivedTensor P.coefficients.l P.extension.val P.X (P.level - 1)

/-- The finite-stage derived internal Hom.
Source: [def-weil-derived-pullback-tensor-hom] (blueprint: def-pod-conventions). -/
noncomputable def derivedInternalHom (P : PoincareDualityConventions.{u}) :
    (proEtaleDerivedCategory P.X P.coefficientRing)ᵒᵖ ×
      proEtaleDerivedCategory P.X P.coefficientRing ⥤
        proEtaleDerivedCategory P.X P.coefficientRing := by
  unfold coefficientRing
  rw [← Nat.sub_add_cancel P.level_pos]
  exact finiteIntrinsicDerivedInternalHom P.coefficients.l P.extension.val P.X (P.level - 1)

/-! The six operations used below are aliases for the recorded constructions.  In
particular, the finite exceptional inverse image uses the recorded etale-origin
construction at the chosen compactification. -/

/-- The finite-coefficient derived direct image `Rf_*`.
Source: [def-weil-derived-direct-image]
(blueprint: def-pod-conventions). -/
noncomputable def finiteDirectImage (P : PoincareDualityConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    proEtaleDerivedCategory Y P.coefficientRing ⥤
      proEtaleDerivedCategory Z P.coefficientRing := by
  letI hfinite : Finite P.coefficientRing :=
    Padic.finite_coefficientExtensionRing P.base.coefficients.l
      P.extension.val P.base.level P.base.level_pos
  exact proEtaleConstantDerivedDirectImage f P.coefficientRing

/-- The completed `O_E` derived direct image, the integral-stage realization of
`Rf_*`.
Source: [def-weil-derived-direct-image]
(blueprint: def-pod-conventions). -/
noncomputable def completedDirectImage (P : PoincareDualityConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    DerivedCategory (scalarReductionSource P.base.coefficients.l
      P.extension.val Y) ⥤
      DerivedCategory (scalarReductionSource P.base.coefficients.l
        P.extension.val Z) :=
  sfCompletedDerivedDirectImage P.base.coefficients.l P.extension.val f

/-- The finite-coefficient compact-support direct image `Rf_!` for a chosen
compactification.
Source: [def-compact-support-direct-image-detailed]
(blueprint: def-pod-conventions). -/
noncomputable def finiteCompactSupport (P : PoincareDualityConventions.{u})
    {Y Z : Scheme.{u}} {f : Y ⟶ Z} (c : Compactification f) :
    proEtaleDerivedCategory Y P.coefficientRing ⥤
      proEtaleDerivedCategory Z P.coefficientRing := by
  letI := Padic.finite_coefficientExtensionRing P.base.coefficients.l
    P.extension.val P.base.level P.base.level_pos
  exact AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport c P.coefficientRing

/-- The finite-coefficient exceptional inverse image `Rf^!`, using the recorded etale
right adjoint transported to the pro-etale site.
The compactification parameter records the support presentation.
Source: [def-weil-exceptional-inverse-image]
(blueprint: def-pod-conventions). -/
noncomputable def finiteExceptionalInverseImage (P : PoincareDualityConventions.{u})
    (_c : Compactification P.structureMap) :
    proEtaleDerivedCategory P.s P.coefficientRing ⥤
      proEtaleDerivedCategory P.X P.coefficientRing := by
  exact Scheme.finiteExceptionalInverseImage P.base.coefficients.l
    P.extension.val P.base.level P.base.level_pos P.base.datum.k P.X P.s
    P.structureMap

/-- The finite dualizing object is the recorded exceptional inverse image of the
coefficient unit, in the canonical intrinsic realization used by the purity orientation.
Source: [thm-pur-diagonal-dualizing-object], [def-weil-exceptional-inverse-image]
(blueprint: def-pod-conventions). -/
noncomputable def finiteDualizingObject (P : PoincareDualityConventions.{u}) :=
  (sfIntrinsicDerivedEquivalence P.X P.puritySetting.Ring).functor.obj
    (P.puritySetting.diagonalDualizing P.structureMap)

/-- The finite Verdier dual is internal Hom into that same finite dualizing object.
Source: [def-sf-coefficient-duality] (blueprint: def-pod-conventions). -/
noncomputable def finiteVerdierDual (P : PoincareDualityConventions.{u})
    (K : proEtaleDerivedCategory P.X P.coefficientRing) :=
  P.derivedInternalHom.obj (op K, P.finiteDualizingObject)

/-- Strict Weil complexes at the finite extension stage.
Source: [def-weil-weil-sheaf-complex] (blueprint: def-pod-conventions). -/
noncomputable abbrev strictWeilComplex (P : PoincareDualityConventions.{u}) :=
  sfWeilComplex P.base.datum P.base.coefficients.l P.base.coefficients.different
    P.base.X₀ P.base.extension.val

/-- The integral constructible category for `O_E` coefficients.
Source: [def-weil-integral-rational-qbar-compact-support]
(blueprint: def-pod-conventions). -/
noncomputable abbrev integralCategory (P : PoincareDualityConventions.{u}) :=
  sfIntegralConstructibleCategory P.base.coefficients.l P.base.extension.val P.X

/-- The rational constructible category for `E` coefficients.
Source: [def-weil-integral-rational-qbar-compact-support]
(blueprint: def-pod-conventions). -/
noncomputable abbrev rationalCategory (P : PoincareDualityConventions.{u}) :=
  sfRationalConstructibleCategory P.base.coefficients.l P.base.extension.val P.X

/-- The algebraically closed constructible category at a common coefficient field.
Source: [def-weil-algebraically-closed-coefficients]
(blueprint: def-pod-conventions). -/
noncomputable abbrev qbarCategory (P : PoincareDualityConventions.{u})
    (Ω : Type u) [Field Ω] [Algebra (Padic P.base.coefficients.l) Ω]
    [IsAlgClosure (Padic P.base.coefficients.l) Ω] :=
  generalAlgebraicallyClosedConstructibleCategory P.base.coefficients.l Ω P.X

/-- Integral derived pullback on constructible objects.
Source: [def-weil-derived-pullback-tensor-hom]
(blueprint: def-pod-conventions). -/
noncomputable def integralPullback (P : PoincareDualityConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [∀ y : Y, Invertible (P.base.coefficients.l : Y.residueField y)]
    [∀ z : Z, Invertible (P.base.coefficients.l : Z.residueField z)] :
    sfIntegralConstructibleCategory P.base.coefficients.l P.base.extension.val Z ⥤
      sfIntegralConstructibleCategory P.base.coefficients.l P.base.extension.val Y :=
  constructibleIntegralPullback P.base.coefficients.l P.base.extension.val f

/-- Integral derived tensor on constructible objects.
Source: [def-weil-derived-pullback-tensor-hom]
(blueprint: def-pod-conventions). -/
noncomputable def integralTensor (P : PoincareDualityConventions.{u})
    (W : Scheme.{u})
    [∀ w : W, Invertible (P.base.coefficients.l : W.residueField w)] :
    sfIntegralConstructibleCategory P.base.coefficients.l P.base.extension.val W ×
      sfIntegralConstructibleCategory P.base.coefficients.l P.base.extension.val W ⥤
        sfIntegralConstructibleCategory P.base.coefficients.l P.base.extension.val W :=
  constructibleIntegralTensor P.base.coefficients.l P.base.extension.val W

/-- Rational derived pullback on constructible objects.
Source: [def-weil-derived-pullback-tensor-hom]
(blueprint: def-pod-conventions). -/
noncomputable def rationalPullback (P : PoincareDualityConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [∀ y : Y, Invertible (P.base.coefficients.l : Y.residueField y)]
    [∀ z : Z, Invertible (P.base.coefficients.l : Z.residueField z)] :=
  rationalDerivedPullback P.base.coefficients.l P.base.extension.val f

/-- Rational derived tensor on constructible objects.
Source: [def-weil-derived-pullback-tensor-hom]
(blueprint: def-pod-conventions). -/
noncomputable def rationalTensor (P : PoincareDualityConventions.{u})
    (W : Scheme.{u})
    [∀ w : W, Invertible (P.base.coefficients.l : W.residueField w)] :=
  rationalDerivedTensor P.base.coefficients.l P.base.extension.val W

/-- Common-stage derived pullback for algebraically closed coefficients.
Source: [def-weil-derived-pullback-tensor-hom]
(blueprint: def-pod-conventions). -/
noncomputable def qbarPullback (P : PoincareDualityConventions.{u})
    (Ω : Type u) [Field Ω] [Algebra (Padic P.base.coefficients.l) Ω]
    [IsAlgClosure (Padic P.base.coefficients.l) Ω]
    {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [∀ y : Y, Invertible (P.base.coefficients.l : Y.residueField y)]
    [∀ z : Z, Invertible (P.base.coefficients.l : Z.residueField z)] :=
  commonStageDerivedPullback P.base.coefficients.l Ω f

/-- Common-stage derived tensor for algebraically closed coefficients.
Source: [def-weil-derived-pullback-tensor-hom]
(blueprint: def-pod-conventions). -/
noncomputable def qbarTensor (P : PoincareDualityConventions.{u})
    (Ω : Type u) [Field Ω] [Algebra (Padic P.base.coefficients.l) Ω]
    [IsAlgClosure (Padic P.base.coefficients.l) Ω]
    (W : Scheme.{u})
    [∀ w : W, Invertible (P.base.coefficients.l : W.residueField w)] :=
  commonStageDerivedTensor P.base.coefficients.l Ω W

/-- Ordinary and compact-support cohomology at the integral and rational stages are
provided by `integralOrdinaryCohomology`, `integralCompactCohomology`,
`rationalOrdinaryCohomology`, and `rationalCompactCohomology` from the recorded
ordinary/compact cohomology module.
Source: [def-weil-ordinary-compact-cohomology]
(blueprint: def-pod-conventions). -/
noncomputable abbrev integralOrdinary (P : PoincareDualityConventions.{u}) :=
  integralOrdinaryCohomology P.base.datum P.base.coefficients.l
    P.base.coefficients.different P.base.extension.val P.X

/-- Rational ordinary cohomology `H^i(X,K)`.
Source: [def-weil-ordinary-compact-cohomology]
(blueprint: def-pod-conventions). -/
noncomputable abbrev rationalOrdinary (P : PoincareDualityConventions.{u}) :=
  rationalOrdinaryCohomology P.base.datum P.base.coefficients.l
    P.base.coefficients.different P.base.extension.val P.X

/-- The finite signed Tate twist K(m) is the recorded derived tensor with A_X(m).
The successor index runs through all positive finite coefficient stages.
Source: [def-coefficient-twists-detailed] (blueprint: def-pod-conventions). -/
noncomputable def finiteTwist (P : PoincareDualityConventions.{u}) (n : ℕ) (m : ℤ)
    (K : proEtaleDerivedCategory P.X
      (Padic.coefficientExtensionRing P.coefficients.l P.extension.val (n + 1))) :=
  letI := sfWeilPrimeInvertible P.datum P.coefficients.l P.coefficients.different P.X₀
  (finiteIntrinsicDerivedTensor P.coefficients.l P.extension.val P.X n).obj
    (K, (DerivedCategory.singleFunctor _ 0).obj
      (finiteCoefficientTwist P.coefficients.l P.extension.val P.X n m))

/-- The integral Tate-twist coefficient object, with the recorded signed Frobenius
normalization.  The normalization is the one built into the existing twisting functor.
Source: [def-coefficient-twists-detailed]
(blueprint: def-pod-conventions). -/
noncomputable def integralTwist (P : PoincareDualityConventions.{u}) (m : ℤ) :
    DerivedCategory (integralTowerModules P.base.coefficients.l
      P.base.extension.val P.X) ⥤
      DerivedCategory (integralTowerModules P.base.coefficients.l
        P.base.extension.val P.X) := by
  letI : ∀ x : P.X, Invertible (P.base.coefficients.l : P.X.residueField x) :=
    sfWeilPrimeInvertible P.datum P.coefficients.l P.coefficients.different P.X₀
  exact sfIntegralTwistingFunctor P.base.coefficients.l P.base.extension.val P.X m

/-- The rational Tate-twist coefficient object.
Source: [def-coefficient-twists-detailed]
(blueprint: def-pod-conventions). -/
noncomputable def rationalTwist (P : PoincareDualityConventions.{u}) (m : ℤ) :
    sfRationalConstructibleCategory P.base.coefficients.l P.base.extension.val P.X ⥤
      sfRationalConstructibleCategory P.base.coefficients.l P.base.extension.val P.X := by
  letI : ∀ x : P.X, Invertible (P.base.coefficients.l : P.X.residueField x) :=
    sfWeilPrimeInvertible P.datum P.coefficients.l P.coefficients.different P.X₀
  exact sfRationalTwistingFunctor P.base.coefficients.l P.base.extension.val P.X m

/-- The common-stage Tate-twist coefficient object.
Source: [def-coefficient-twists-detailed]
(blueprint: def-pod-conventions). -/
noncomputable def qbarTwist (P : PoincareDualityConventions.{u})
    (Ω : Type u) [Field Ω] [Algebra (Padic P.base.coefficients.l) Ω]
    [IsAlgClosure (Padic P.base.coefficients.l) Ω] (m : ℤ) :
    qbarCategory P Ω ⥤ qbarCategory P Ω := by
  letI : ∀ x : P.X, Invertible (P.base.coefficients.l : P.X.residueField x) :=
    sfWeilPrimeInvertible P.datum P.coefficients.l P.coefficients.different P.X₀
  exact sfQbarTwistingFunctor P.base.coefficients.l P.X Ω m

/-- The global geometric-Frobenius pair on a strict Weil complex.
Its two components are the ordinary and compact-support transports followed by the
Weil isomorphism, exactly as in the recorded global-geometric-Frobenius definition.
Source: [def-weil-global-geometric-frobenius]
(blueprint: def-pod-conventions). -/
noncomputable def globalFrobenius (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.base.X₀.hom) (K : P.strictWeilComplex) :=
  globalGeometricFrobenius P.base.datum P.base.coefficients P.base.extension
    P.base.X₀ c₀ K

/-- The degreewise global Frobenius actions.
Source: [def-weil-global-geometric-frobenius]
(blueprint: def-pod-conventions). -/
noncomputable def globalFrobeniusOnCohomology (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.base.X₀.hom) (K : P.strictWeilComplex) (i : ℤ) :=
  globalGeometricFrobeniusOnCohomology P.base.datum P.base.coefficients P.base.extension
    P.base.X₀ c₀ K i

/-- The common-stage Frobenius operator, whose ordinary and compact-support
components are the recorded `frobeniusCohomologyTransport` composites.
Source: [def-weil-frobenius-cohomology-transport]
(blueprint: def-pod-conventions). -/
noncomputable def globalQbarFrobenius (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.base.X₀.hom)
    (Ω : Type u) [Field Ω] [Algebra (Padic P.base.coefficients.l) Ω]
    [IsAlgClosure (Padic P.base.coefficients.l) Ω]
    (K : sfCommonStageWeilComplex P.base.datum P.base.coefficients.l
      P.base.coefficients.different P.base.X₀ Ω) (compact : Bool) :=
  globalGeometricFrobeniusQbar P.base.datum P.base.coefficients.l
    P.base.coefficients.different P.base.X₀ Ω c₀ K compact

/-- The Qlbar actions in each degree are the homology of the specified derived operator.
Source: [def-weil-global-geometric-frobenius] (blueprint: def-pod-conventions). -/
noncomputable def globalQbarFrobeniusOnCohomology (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.X₀.hom)
    (Ω : Type u) [Field Ω] [Algebra (Padic P.coefficients.l) Ω]
    [IsAlgClosure (Padic P.coefficients.l) Ω]
    (K : sfCommonStageWeilComplex P.datum P.coefficients.l
      P.coefficients.different P.X₀ Ω) (compact : Bool) (i : ℤ) :=
  globalGeometricFrobeniusQbarOnCohomology P.datum P.coefficients.l
    P.coefficients.different P.X₀ Ω c₀ K compact i

/-- The coefficient-compatible exceptional system already constructed by the six-functor
chapter. Its realization and adjunction normalizations are part of the recorded interface.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable abbrev exceptionalSystem (P : PoincareDualityConventions.{u}) :=
  ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.datum P.coefficients.different (f := P.structureMap)

/-- The chosen compactification in the purity convention, with no universal quantification
in the admissibility hypothesis.
Source: [cor-pur-adic-and-rational-smooth-dualizing-complexes]
(blueprint: def-pod-conventions). -/
noncomputable abbrev purityCompactification (P : PoincareDualityConventions.{u}) :=
  AdicSmoothDualizing.compactification P.puritySetting P.X

/-- The coefficient-stage adjunction for an arbitrary separated finite-type morphism
and its chosen compactification. F is Rf_!, G is Rf^!, and adjunction is their recorded
unit/counit adjunction. All scalar and proper/open normalizations remain in S.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable def coefficientOperation (P : PoincareDualityConventions.{u})
    {Y Z : Scheme.{u}} [Y.Over P.s] [Z.Over P.s]
    [LocallyOfFiniteType (Y ↘ P.s)] [QuasiCompact (Y ↘ P.s)]
    [LocallyOfFiniteType (Z ↘ P.s)] [QuasiCompact (Z ↘ P.s)]
    (f : Y ⟶ Z) [f.IsOver P.s]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
      P.datum P.coefficients.different (f := f))
    (c : Compactification f) (stage : ConstructibleExceptionalCoefficients.Stage.{u}
      P.coefficients.l) := S.ring.operation c stage

/-- The recorded constructible adjunction at each of A, O_E, E and Qlbar.
The system parameter retains all the source's proper/open and scalar normalizations.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable abbrev exceptionalOperation (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) (stage : ConstructibleExceptionalCoefficients.Stage.{u}
      P.coefficients.l) := S.ring.operation P.purityCompactification stage

/-- The finite dualizing object in the purity chapter's original coefficient-field
coordinates, transported by the canonical fixed-scalar/intrinsic module equivalence.
Source: [thm-pur-diagonal-dualizing-object] (blueprint: def-pod-conventions). -/
noncomputable abbrev finiteOrientedDualizingObject (P : PoincareDualityConventions.{u}) :=
  P.finiteDualizingObject

/-- The canonical finite orientation eta_X in the purity chapter's fixed-scalar
presentation of the small pro-etale category.
Source: [thm-pur-diagonal-dualizing-object] (blueprint: def-pod-conventions). -/
noncomputable def finiteOrientation (P : PoincareDualityConventions.{u}) :=
  (sfIntrinsicDerivedEquivalence P.X P.puritySetting.Ring).functor.mapIso
    (P.puritySetting.diagonalDualizingObject P.d P.structureMap (𝟙 P.s))

/-- The canonical O_E orientation eta_X, uniquely normalized by its finite reductions.
Source: [cor-pur-adic-and-rational-smooth-dualizing-complexes]
(blueprint: def-pod-conventions). -/
noncomputable def integralOrientation (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) :=
  AdicSmoothDualizing.integralIdentification P.puritySetting P.X S P.d

/-- The canonical E orientation, using the specified rational coefficient comparison.
Source: [cor-pur-adic-and-rational-smooth-dualizing-complexes]
(blueprint: def-pod-conventions). -/
noncomputable def rationalOrientation (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) :=
  AdicSmoothDualizing.rationalIdentification P.puritySetting P.X S P.d

/-- The canonical Qlbar orientation, using the specified common-stage comparison.
Source: [cor-pur-adic-and-rational-smooth-dualizing-complexes]
(blueprint: def-pod-conventions). -/
noncomputable def qbarOrientation (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) :=
  AdicSmoothDualizing.closedIdentification P.puritySetting P.X S P.d

/-- Integral omega_X is the recorded exceptional inverse image of the coefficient unit.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable def integralDualizingObject (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) :=
  (P.exceptionalOperation S (.integral (AdicSmoothDualizing.fieldStage P.puritySetting))).G.obj
    (AdicSmoothDualizing.integralTwist P.puritySetting P.s (𝟙 P.s) 0)

/-- Rational omega_X is the exceptional inverse image of the rational coefficient unit.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable def rationalDualizingObject (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) :=
  (P.exceptionalOperation S (.rational (AdicSmoothDualizing.fieldStage P.puritySetting))).G.obj
    (AdicSmoothDualizing.rationalTwist P.puritySetting P.s (𝟙 P.s) 0)

/-- Common-stage omega_X is the exceptional inverse image of the common-stage unit.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable def qbarDualizingObject (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) :=
  (P.exceptionalOperation S .closed).G.obj
    (AdicSmoothDualizing.closedTwist P.puritySetting P.s (𝟙 P.s) 0)

/-- The finite-Tor point category, formed by the same finite coefficient convention.
Source: [def-weil-finite-coefficient-point] (blueprint: def-pod-conventions). -/
noncomputable abbrev finitePointCtf (P : PoincareDualityConventions.{u}) :=
  finiteTorConstructibleCategory P.coefficients.l P.extension.val P.level P.level_pos P.s

/-- The integral point category, with the same derived-complete constructible convention.
Source: [def-weil-finite-coefficient-point] (blueprint: def-pod-conventions). -/
noncomputable abbrev integralPointCtf (P : PoincareDualityConventions.{u}) :=
  sfIntegralConstructibleCategory P.coefficients.l P.extension.val P.s

/-- The rational point category, with the specified raw localization.
Source: [def-weil-finite-coefficient-point] (blueprint: def-pod-conventions). -/
noncomputable abbrev rationalPointCtf (P : PoincareDualityConventions.{u}) :=
  sfRationalConstructibleCategory P.coefficients.l P.extension.val P.s

/-- The common-stage point category, retaining the actual finite fields of definition.
Source: [def-weil-finite-coefficient-point] (blueprint: def-pod-conventions). -/
noncomputable abbrev qbarPointCtf (P : PoincareDualityConventions.{u}) :=
  generalAlgebraicallyClosedConstructibleCategory P.coefficients.l P.coefficients.Qbar P.s

/-- Bounded finite-cohomology module complexes at the finite coefficient point.
Source: [def-weil-finite-coefficient-point] (blueprint: def-pod-conventions). -/
noncomputable abbrev finitePointComplexes (P : PoincareDualityConventions.{u}) :=
  (DerivedCategory.pointFiniteCohomology (ULift.{u + 1} P.coefficientRing)).FullSubcategory

/-- Bounded finitely generated derived-complete module complexes at the integral point.
Source: [def-weil-finite-coefficient-point] (blueprint: def-pod-conventions). -/
noncomputable abbrev integralPointComplexes (P : PoincareDualityConventions.{u}) :=
  (DerivedCategory.pointFgComplete
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers P.coefficients.l P.extension.val))
    (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer
      P.coefficients.l P.extension.val)})).FullSubcategory

/-- Bounded finite-dimensional E-module complexes at the rational point.
Source: [def-weil-finite-coefficient-point] (blueprint: def-pod-conventions). -/
noncomputable abbrev rationalPointComplexes (P : PoincareDualityConventions.{u}) :=
  (DerivedCategory.pointFiniteDimensional P.extension.val).FullSubcategory

/-- The recorded common-stage module-complex category at Qlbar.
Source: [def-weil-finite-coefficient-point] (blueprint: def-pod-conventions). -/
noncomputable abbrev qbarPointComplexes (P : PoincareDualityConventions.{u}) :=
  DerivedCategory.PointFdQbar P.coefficients.l P.coefficients.Qbar

/-- Point coefficient duality C^vee = RHom_R(C,R), at any of the coefficient rings
and their prescribed size lifts. The actual point categories are full subcategories
of these module derived categories.
Source: [def-sf-coefficient-duality] (blueprint: def-pod-conventions). -/
noncomputable def pointDual (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (C : DerivedCategory (ModuleCat.{u} R)) :=
  (coefficientDerivedDual R).obj (op C)

/-- Finite coefficient duality K^vee = RHom_X(K,A_X).
Source: [def-weil-derived-pullback-tensor-hom] (blueprint: def-pod-conventions). -/
noncomputable def finiteCoefficientDual (P : PoincareDualityConventions.{u})
    (K : proEtaleDerivedCategory P.X P.coefficientRing) :=
  P.derivedInternalHom.obj (op K,
    finiteCohomologyCoefficient P.coefficients.l P.extension.val P.X
      P.level P.level_pos)

/-- Integral coefficient duality uses the recorded ambient derived internal Hom.
Source: [def-weil-derived-pullback-tensor-hom] (blueprint: def-pod-conventions). -/
noncomputable def integralCoefficientDual (P : PoincareDualityConventions.{u})
    (K : P.integralCategory) :=
  (integralDerivedInternalHom P.coefficients.l P.extension.val P.X).obj
    (op K.obj, (integralCohomologyCoefficient P.datum P.coefficients.l
      P.coefficients.different P.extension.val P.X).obj)

/-- Integral Verdier duality is RHom_X(K,omega_X), with the specified exceptional unit.
Source: [def-weil-derived-pullback-tensor-hom] (blueprint: def-pod-conventions). -/
noncomputable def integralVerdierDual (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) (K : P.integralCategory) :=
  (integralDerivedInternalHom P.coefficients.l P.extension.val P.X).obj
    (op K.obj, (P.integralDualizingObject S).obj)

/-- The literal integral pair on which internal Hom is taken. The recorded closure
corollary supplies its membership; the short proof transports between the two recorded
completeness presentations and does not add a condition on either argument.
Source: [cor-coef-integral-internal-hom] (blueprint: def-pod-conventions). -/
noncomputable def integralHomPair (P : PoincareDualityConventions.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (K L : sfIntegralConstructibleCategory P.coefficients.l E P.X) :
    (constructibleIntegralHomPairs P.coefficients.l E P.X).FullSubcategory := by
  have hK : boundedConstructibleDerivedCompleteIntegral P.datum P.coefficients.l
      P.coefficients.different E P.X K.obj :=
    ⟨(sfDerivedComplete_iff_legacy P.coefficients.l E P.X P.datum
      P.coefficients.different K.obj).mp K.property.1, K.property.2⟩
  have hL : boundedConstructibleDerivedCompleteIntegral P.datum P.coefficients.l
      P.coefficients.different E P.X L.obj :=
    ⟨(sfDerivedComplete_iff_legacy P.coefficients.l E P.X P.datum
      P.coefficients.different L.obj).mp L.property.1, L.property.2⟩
  have hH := (integral_constructible_internalHom P.datum P.coefficients.l
    P.coefficients.different E P.X K.obj L.obj hK hL).1
  exact ⟨(op K, L),
    (sfDerivedComplete_iff_legacy P.coefficients.l E P.X P.datum
      P.coefficients.different _).mpr hH.1, hH.2⟩

/-- The rational pair is exactly the pair of integral representatives, with membership
supplied by the recorded integral closure corollary.
Source: [cor-coef-integral-internal-hom], [def-weil-derived-pullback-tensor-hom]
(blueprint: def-pod-conventions). -/
noncomputable def rationalHomPair (P : PoincareDualityConventions.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (K L : sfRationalConstructibleCategory P.coefficients.l E P.X) :
    (constructibleRationalHomPairs P.coefficients.l E P.X).FullSubcategory :=
  ⟨(op K, L), (P.integralHomPair E K.obj L.obj).property⟩

/-- Common-stage Hom uses the actual scalar-extended pair at the coefficient compositum.
Source: [def-weil-derived-pullback-tensor-hom], [cor-coef-integral-internal-hom]
(blueprint: def-pod-conventions). -/
noncomputable def qbarHomPair (P : PoincareDualityConventions.{u})
    (K L : P.qbarCategory P.coefficients.Qbar) :
    (commonStageHomPairs P.coefficients.l P.coefficients.Qbar P.X).FullSubcategory := by
  refine ⟨(op K, L), ?_⟩
  exact (P.rationalHomPair _ _ _).property

/-- Rational coefficient duality is the recorded internal Hom into the coefficient unit.
Source: [def-weil-derived-pullback-tensor-hom] (blueprint: def-pod-conventions). -/
noncomputable def rationalCoefficientDual (P : PoincareDualityConventions.{u})
    (K : P.rationalCategory) :=
  (rationalDerivedInternalHom P.coefficients.l P.extension.val P.X).obj
    (P.rationalHomPair P.extension.val K
      (AdicSmoothDualizing.rationalTwist P.puritySetting P.X P.structureMap 0))

/-- Common-stage coefficient duality uses internal Hom into the common-stage unit.
Source: [def-weil-derived-pullback-tensor-hom] (blueprint: def-pod-conventions). -/
noncomputable def qbarCoefficientDual (P : PoincareDualityConventions.{u})
    (K : P.qbarCategory P.coefficients.Qbar) :=
  (commonStageDerivedInternalHom P.coefficients.l P.coefficients.Qbar P.X).obj
    (P.qbarHomPair K
      (AdicSmoothDualizing.closedTwist P.puritySetting P.X P.structureMap 0))

/-- Rational Verdier duality is internal Hom into the same exceptional image of unit.
Source: [def-weil-derived-pullback-tensor-hom] (blueprint: def-pod-conventions). -/
noncomputable def rationalVerdierDual (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) (K : P.rationalCategory) :=
  (rationalDerivedInternalHom P.coefficients.l P.extension.val P.X).obj
    (P.rationalHomPair P.extension.val K (P.rationalDualizingObject S))

/-- Common-stage Verdier duality is internal Hom into the same common-stage omega_X.
Source: [def-weil-derived-pullback-tensor-hom] (blueprint: def-pod-conventions). -/
noncomputable def qbarVerdierDual (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) (K : P.qbarCategory P.coefficients.Qbar) :=
  (commonStageDerivedInternalHom P.coefficients.l P.coefficients.Qbar P.X).obj
    (P.qbarHomPair K (P.qbarDualizingObject S))

/-- The integral compact-support functor in the prescribed adjunction.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable abbrev integralCompactSupport (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) :=
  (P.exceptionalOperation S (.integral (AdicSmoothDualizing.fieldStage P.puritySetting))).F

/-- The integral exceptional inverse image in that same adjunction.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable abbrev integralExceptionalInverseImage (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) :=
  (P.exceptionalOperation S (.integral (AdicSmoothDualizing.fieldStage P.puritySetting))).G

/-- The rational compact-support functor in the prescribed adjunction.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable abbrev rationalCompactSupport (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) :=
  (P.exceptionalOperation S (.rational (AdicSmoothDualizing.fieldStage P.puritySetting))).F

/-- The rational exceptional inverse image in that same adjunction.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable abbrev rationalExceptionalInverseImage (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) :=
  (P.exceptionalOperation S (.rational (AdicSmoothDualizing.fieldStage P.puritySetting))).G

/-- The common-stage compact-support functor in the prescribed adjunction.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable abbrev qbarCompactSupport (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) := (P.exceptionalOperation S .closed).F

/-- The common-stage exceptional inverse image in that same adjunction.
Source: [def-weil-exceptional-inverse-image] (blueprint: def-pod-conventions). -/
noncomputable abbrev qbarExceptionalInverseImage (P : PoincareDualityConventions.{u})
    (S : P.exceptionalSystem) := (P.exceptionalOperation S .closed).G

/-- The integral ordinary direct image on the selected coefficient field.
Source: [def-weil-derived-direct-image] (blueprint: def-pod-conventions). -/
noncomputable abbrev integralDirectImage (P : PoincareDualityConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :=
  sfCompletedDerivedDirectImage P.coefficients.l P.extension.val f

/-- The rational ordinary direct image, uniquely specified as right adjoint of the
recorded rational pullback. The adjunction is the localized integral adjunction.
Source: [def-weil-derived-direct-image] (blueprint: def-pod-conventions). -/
noncomputable def rationalDirectImage (P : PoincareDualityConventions.{u})
    {Y Z : Scheme.{u}}
    [Y.Over P.s] [Z.Over P.s]
    [LocallyOfFiniteType (Y ↘ P.s)] [QuasiCompact (Y ↘ P.s)]
    [LocallyOfFiniteType (Z ↘ P.s)] [QuasiCompact (Z ↘ P.s)]
    (f : Y ⟶ Z) [f.IsOver P.s]
    [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
    [∀ z : Z, Invertible (P.coefficients.l : Z.residueField z)] :=
  let R := FrobeniusExchange.directImageFunctor P.coefficients.l P.extension.val
    P.datum.k
    (finiteFieldDatumPrimeUnit P.datum P.coefficients.l P.coefficients.different) f
  let h := FrobeniusExchange.directImage_linear P.coefficients.l P.extension.val
    P.datum.k
    (finiteFieldDatumPrimeUnit P.datum P.coefficients.l P.coefficients.different) f
  letI : R.Additive := h.1
  letI : R.Linear (Padic.coefficientExtensionIntegers P.coefficients.l P.extension.val) := h.2
  let p := Padic.coefficientExtensionUniformizer P.coefficients.l P.extension.val
  ScalarLocalization.extension p p (RingHom.id _)
    (IsLocalization.Away.algebraMap_isUnit p) R
    (fun _ _ a f ↦ R.map_smul a f)

/-- The common-stage ordinary direct image with its recorded finite-field comparisons.
Source: [def-weil-derived-direct-image] (blueprint: def-pod-conventions). -/
noncomputable def qbarDirectImage (P : PoincareDualityConventions.{u})
    {Y Z : Scheme.{u}}
    [Y.Over P.s] [Z.Over P.s]
    [LocallyOfFiniteType (Y ↘ P.s)] [QuasiCompact (Y ↘ P.s)]
    [LocallyOfFiniteType (Z ↘ P.s)] [QuasiCompact (Z ↘ P.s)]
    (f : Y ⟶ Z) [f.IsOver P.s]
    [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
    [∀ z : Z, Invertible (P.coefficients.l : Z.residueField z)] :=
  geometricCommonStageDirectImage P.coefficients.l P.coefficients.Qbar P.datum.k
    (finiteFieldDatumPrimeUnit P.datum P.coefficients.l P.coefficients.different) f

/-- The ordinary and compact F-operators at every positive finite exponent n+1.
They are exactly the respective transport followed by the cohomology image of phi.
Source: [def-weil-frobenius-cohomology-transport], [def-pur-tate-datum]
(blueprint: def-pod-conventions). -/
noncomputable def finiteFrobenius (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.X₀.hom) (n : ℕ)
    (K : proEtaleDerivedCategory P.X
      (Padic.coefficientExtensionRing P.coefficients.l P.extension.val (n + 1)))
    (φ : (finiteDerivedPullback P.coefficients.l P.extension.val n
      (P.datum.geometricGaloisFrobenius P.X₀)).obj K ≅ K) :=
  (frobeniusOrdinaryTransportFinite P.datum P.coefficients.l
      P.coefficients.different P.extension.val P.X₀ n K ≫
    (frobeniusCohomologyFiniteFunctor P.datum P.coefficients.l
      P.extension.val P.X₀ c₀ n false).map φ.hom,
   frobeniusCompactTransportFinite P.datum P.coefficients.l
      P.coefficients.different P.extension.val P.X₀ c₀ n K ≫
    (frobeniusCohomologyFiniteFunctor P.datum P.coefficients.l
      P.extension.val P.X₀ c₀ n true).map φ.hom)

/-- The finite actions on H^i and H_c^i are induced by those same derived endomorphisms.
Source: [def-weil-frobenius-cohomology-transport] (blueprint: def-pod-conventions). -/
noncomputable def finiteFrobeniusOnCohomology (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.X₀.hom) (n : ℕ)
    (K : proEtaleDerivedCategory P.X
      (Padic.coefficientExtensionRing P.coefficients.l P.extension.val (n + 1)))
    (φ : (finiteDerivedPullback P.coefficients.l P.extension.val n
      (P.datum.geometricGaloisFrobenius P.X₀)).obj K ≅ K) (i : ℤ) :=
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing P.coefficients.l P.extension.val (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1}
    (Padic.coefficientExtensionRing P.coefficients.l P.extension.val (n + 1)))) i
  (H.map (P.finiteFrobenius c₀ n K φ).1, H.map (P.finiteFrobenius c₀ n K φ).2)

/-- The finite and integral Tate-line actions have the recorded q^(-m) normalization.
For negative m this is q^(-m) as a positive power, including the untwisted case m=0.
Source: [lem-pur-twist-frobenius-scalar] (blueprint: def-pod-conventions). -/
noncomputable abbrev twistFrobeniusNormalization (P : PoincareDualityConventions.{u})
    (m : ℤ) :=
  Purity.tau_scalar P.puritySetting m

/-- The scalar q^(-m) of geometric Frobenius on the signed coefficient line.
Source: [lem-pur-twist-frobenius-scalar] (blueprint: def-pod-conventions). -/
noncomputable abbrev twistFrobeniusScalar (P : PoincareDualityConventions.{u})
    (R : Type u) [CommRing R] (m : ℤ) : R :=
  TwistFrobeniusScalar.scalar R P.datum.q m

/-- Integral geometric Frobenius: ordinary and compact transport, each followed by RΓ(phi).
Source: [def-weil-frobenius-cohomology-transport], [def-pur-tate-datum]
(blueprint: def-pod-conventions). -/
noncomputable def integralFrobenius (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.X₀.hom) (K : P.integralCategory)
    (φ : (frobeniusCohomologyIntegralPullback P.datum P.coefficients.l
      P.coefficients.different P.extension.val P.X₀).obj K ≅ K) :=
  ((frobeniusCohomologyTransportIntegral P.datum P.coefficients.l
      P.coefficients.different P.extension.val P.X₀ c₀ K).1 ≫
    (frobeniusCohomologyIntegralFunctor P.datum P.coefficients.l
      P.coefficients.different P.extension.val P.X₀ c₀ false).map φ.hom,
   (frobeniusCohomologyTransportIntegral P.datum P.coefficients.l
      P.coefficients.different P.extension.val P.X₀ c₀ K).2 ≫
    (frobeniusCohomologyIntegralFunctor P.datum P.coefficients.l
      P.coefficients.different P.extension.val P.X₀ c₀ true).map φ.hom)

/-- The integral actions on H^i and H_c^i, for every integer degree.
Source: [def-weil-frobenius-cohomology-transport] (blueprint: def-pod-conventions). -/
noncomputable def integralFrobeniusOnCohomology (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.X₀.hom) (K : P.integralCategory)
    (φ : (frobeniusCohomologyIntegralPullback P.datum P.coefficients.l
      P.coefficients.different P.extension.val P.X₀).obj K ≅ K) (i : ℤ) :=
  let H := DerivedCategory.coefficientFgCohomology
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers P.coefficients.l P.extension.val))
    (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer
      P.coefficients.l P.extension.val)}) i
  (H.map (P.integralFrobenius c₀ K φ).1, H.map (P.integralFrobenius c₀ K φ).2)

/-- Positive Frobenius iterates mean repeated composition of the specified endomorphism.
Source: [def-trf-frobenius-operators] (blueprint: def-pod-conventions). -/
noncomputable def frobeniusIterate {C : Type u} [Category.{v} C] {K : C}
    (F : End K) (r : ℕ) (_hr : 1 ≤ r) : End K := F ^ r

/-- Finite compact-support Frobenius at m=1 is exactly clause 1 of the recorded operator.
Source: [def-trf-frobenius-operators] (blueprint: def-pod-conventions). -/
noncomputable def finiteCompactFrobenius (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.X₀.hom) (K : P.base.strictWeilComplex) :=
  P.base.finiteGlobalFrobenius c₀ K 0

/-- The finite compact transport is the recorded degree-one transport, not a new choice.
Source: [def-trf-frobenius-operators] (blueprint: def-pod-conventions). -/
noncomputable def finiteCompactTransport (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.X₀.hom)
    (K : proEtaleDerivedCategory P.X P.base.coefficientRing) :=
  P.base.finiteGlobalCompactStep c₀ K

/-- Finite compact Frobenius in every integer cohomological degree.
Source: [def-trf-frobenius-operators] (blueprint: def-pod-conventions). -/
noncomputable def finiteCompactFrobeniusCohomology (P : PoincareDualityConventions.{u})
    (c₀ : Compactification P.X₀.hom) (K : P.base.strictWeilComplex) (i : ℤ) :=
  P.base.finiteGlobalFrobeniusCohomology c₀ K 0 i

/-- The finite ordinary sections convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev finiteOrdinarySections (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.finiteOrdinarySections P.datum P.coefficients.l P.extension.val P.X

/-- The finite ordinary cohomology convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev finiteOrdinaryCohomology (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.finiteOrdinaryCohomology P.datum P.coefficients.l P.extension.val P.X

/-- The finite compact sections convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev finiteCompactSections (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.finiteCompactSections P.datum P.coefficients.l P.extension.val P.X

/-- The finite compact cohomology convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev finiteCompactCohomology (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.finiteCompactCohomology P.datum P.coefficients.l P.extension.val P.X

/-- The integral ordinary sections convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev integralOrdinarySections (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.integralOrdinarySections P.datum P.coefficients.l
    P.coefficients.different P.extension.val P.X

/-- The integral ordinary cohomology convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev integralOrdinaryCohomology (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.integralOrdinaryCohomology P.datum P.coefficients.l
    P.coefficients.different P.extension.val P.X

/-- The integral compact sections convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev integralCompactSections (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.integralCompactSections P.datum P.coefficients.l
    P.coefficients.different P.extension.val P.X

/-- The integral compact cohomology convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev integralCompactCohomology (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.integralCompactCohomology P.datum P.coefficients.l
    P.coefficients.different P.extension.val P.X

/-- The rational ordinary sections convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev rationalOrdinarySections (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.rationalOrdinarySections P.datum P.coefficients.l
    P.coefficients.different P.extension.val P.X

/-- The rational ordinary cohomology convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev rationalOrdinaryCohomology (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.rationalOrdinaryCohomology P.datum P.coefficients.l
    P.coefficients.different P.extension.val P.X

/-- The rational compact sections convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev rationalCompactSections (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.rationalCompactSections P.datum P.coefficients.l
    P.coefficients.different P.extension.val P.X

/-- The rational compact cohomology convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev rationalCompactCohomology (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.rationalCompactCohomology P.datum P.coefficients.l
    P.coefficients.different P.extension.val P.X

/-- The qbar ordinary sections convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev qbarOrdinarySections (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.qbarOrdinarySections P.datum P.coefficients.l
    P.coefficients.different P.X P.coefficients.Qbar

/-- The qbar ordinary cohomology convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev qbarOrdinaryCohomology (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.qbarOrdinaryCohomology P.datum P.coefficients.l
    P.coefficients.different P.X P.coefficients.Qbar

/-- The qbar compact sections convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev qbarCompactSections (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.qbarCompactSections P.datum P.coefficients.l
    P.coefficients.different P.X P.coefficients.Qbar

/-- The qbar compact cohomology convention, directly specialized
from the recorded construction on the actual geometric fibre.
Source: [def-weil-ordinary-compact-cohomology] (blueprint: def-pod-conventions). -/
noncomputable abbrev qbarCompactCohomology (P : PoincareDualityConventions.{u}) :=
  WeilConjectures.qbarCompactCohomology P.datum P.coefficients.l
    P.coefficients.different P.X P.coefficients.Qbar

end PoincareDualityConventions
end WeilConjectures
