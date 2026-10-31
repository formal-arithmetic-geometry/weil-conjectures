/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDualNotation
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.CtfCoefficientStageSelectors
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorIso
public import WeilConjectures.CategoryTheory.DerivedTensorKoszulSymmetry
public import WeilConjectures.AlgebraicGeometry.CompletedPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.DirectImagesConstructible
import WeilConjectures.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionFormula
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # The six relative-product base-change squares

Source: latest blueprint, sec-six-functors/sk-thm-sf-kunneth-relative/_section.md,
coherence (iii), with the six displayed factors
(blueprint: lem-sf-relative-product-base-change-factor-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.RelativeProductBaseChange

attribute [local irreducible] Scheme.residueField

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {m : ℕ}
  (S : SixFunctorDatum D C E (m + 1) (Nat.succ_pos m))

/-- The recorded finite-Tor full domain at any of the four coefficient stages.
Source: coefficient conventions (blueprint: lem-sf-relative-product-base-change-factor-squares).
-/
abbrev Ctf (s : PodCoefficientStage) (X : SixFunctorSpace D) :=
  (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).FullSubcategory

/-- The recorded operations, without a replacement coefficient category.
Source: A1--A4 (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
abbrev operations (s : PodCoefficientStage) :=
  PodCoefficientStage.operations S.toSixFunctorOperationDatum s

/-- The existing preservation proofs, selected from the datum at the chosen stage.
Proof: select finiteCoherence, integralCoherence, rationalCoherence or commonCoherence.
Source: A1, A4 (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
theorem coherence (s : PodCoefficientStage) :
    SixFunctorCoherentStage (operations S s)
      (PodCoefficientStage.domain S.toSixFunctorOperationDatum s) := by
  cases s with
  | finite => exact S.finiteCoherence
  | integral => exact S.integralCoherence
  | rational => exact S.rationalCoherence
  | common => exact S.commonCoherence

/-- Restrict the specified inverse image through the full finite-Tor inclusions.
Source: Lu* (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def pull (s : PodCoefficientStage) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] : Ctf S s Y ⥤ Ctf S s X :=
  sixFunctorDomainChange _ _ ((operations S s).pull f)
    (fun K ↦ (coherence S s).pullDomain f K.obj K.property)

/-- Restrict the specified compact-support functor, keeping its compactification.
Source: Rf! (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def support (s : PodCoefficientStage) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) : Ctf S s X ⥤ Ctf S s Y :=
  sixFunctorDomainChange _ _ ((operations S s).support f c)
    (fun K ↦ (coherence S s).supportDomain f c K.obj K.property)

/-- The specified tensor, with both inputs in its actual finite-Tor domain.
Source: the seven Di (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def tensorValue (s : PodCoefficientStage) (X : SixFunctorSpace D) :=
  ((Functor.whiskeringLeft _ _ _).obj
    (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).ι).obj
      (PodCoefficientStage.tensor S.toSixFunctorOperationDatum s X)

private theorem torAmplitudeIso (X : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory X A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude X A K a b) : HasProEtaleTorAmplitude X A L a b := by
  refine ⟨h.1, ?_⟩
  intro V P hV f hf hP M i hi
  obtain ⟨eV⟩ := hV
  exact h.2 V P ⟨eV ≪≫ e.symm⟩ f hf hP M i hi

/-- The displayed tensors remain finite-Tor constructible.
Source: the displayed domains (blueprint: lem-sf-relative-product-base-change-factor-squares).
Proof: finite Tor intervals add under tensor. Bounded constructibility is preserved
by the recorded finite tensor on etale representatives and its coefficient realization.
For integral coefficients use completed tensor and the uniform sum of the two intervals.
Rationalization and a common finite coefficient field give the two field cases. -/
theorem tensor_domain (s : PodCoefficientStage) (X : SixFunctorSpace D)
    (K L : Ctf S s X) :
    PodCoefficientStage.domain S.toSixFunctorOperationDatum s X
      (((tensorValue S s X).obj K).obj L) := by
  cases s with
  | finite =>
    let := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.succ_pos m)
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let R := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) X
    refine ⟨(((tensorValue S .finite X).obj K).obj L).property, ?_⟩
    obtain ⟨a, b, hK⟩ := K.property.2
    obtain ⟨c, d, hL⟩ := L.property.2
    have hK' := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      A X.obj.left a b hK.1 (R.inverse.obj K.obj.obj)).mp
        (torAmplitudeIso _ _ (R.counitIso.app K.obj.obj).symm hK)
    have hL' := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      A X.obj.left c d hL.1 (R.inverse.obj L.obj.obj)).mp
        (torAmplitudeIso _ _ (R.counitIso.app L.obj.obj).symm hL)
    have hT := DerivedCategory.torAmplitudeIn_tensor hK' hL'
    refine ⟨a + c, b + d, ?_⟩
    exact (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      A X.obj.left (a + c) (b + d) (add_le_add hK.1 hL.1) _).mpr hT
  | integral =>
    let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) := fun x ↦
      (by
        simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
          (X.obj.hom.residueFieldAlgebraMap x) :
            IsUnit (C.l : X.obj.left.residueField x)).invertible
    change finiteTorConstructibleIntegral C.l E X.obj.left _
    rw [← (integral_residue_tor D C.l C.different E X.obj.left).2]
    exact (((tensorValue S .integral X).obj K).obj L).property
  | rational => trivial
  | common => trivial

/-- Full restriction of the recorded tensor, on objects and arrows.
Source: the seven Di (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def tensor (s : PodCoefficientStage) (X : SixFunctorSpace D) :
    Ctf S s X × Ctf S s X ⥤ Ctf S s X :=
  (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).lift
    (Functor.uncurry.obj (tensorValue S s X))
    (fun KL ↦ tensor_domain S s X KL.1 KL.2)

/-- The supplied support compositor lifted through the full inclusion.
Source: d0 (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def composition (s : PodCoefficientStage) {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (cf : Compactification f.hom.left)
    (cg : Compactification g.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (K : Ctf S s X) :
    (support S s (f ≫ g) cfg).obj K ≅
      (support S s g cg).obj ((support S s f cf).obj K) :=
  ObjectProperty.isoMk _ (((operations S s).composition f g cf cg cfg).app K.obj)

/-- Canonical pullback composition in the same full domain.
Source: beta comparisons (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def pullSquare (s : PodCoefficientStage) {W X Y Z : SixFunctorSpace D}
    (a : W ⟶ X) (b : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsSeparated a.hom.left] [IsSeparated b.hom.left]
    [IsSeparated f.hom.left] [IsSeparated g.hom.left]
    (w : a ≫ f = b ≫ g) (K : Ctf S s Z) :
    (pull S s a).obj ((pull S s f).obj K) ≅
      (pull S s b).obj ((pull S s g).obj K) :=
  ObjectProperty.isoMk _
    ((((operations S s).pullComposition a f).symm ≪≫
      eqToIso (congrArg (fun e ↦ (operations S s).pull e) w) ≪≫
      (operations S s).pullComposition b g).app K.obj)

/-- The coefficient prime is invertible in all geometric residue fields.
Source: the fixed distinct primes
(blueprint: lem-sf-relative-product-base-change-factor-squares). -/
@[instance_reducible] def residueInvertible (X : SixFunctorSpace D) :
    ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
  fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
      (X.obj.hom.residueFieldAlgebraMap x) : IsUnit (C.l : X.obj.left.residueField x)).invertible

/-- Equality transport of a specified tensor-distribution component.
Source: coefficient presentations
(blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def transportTensorPull {A B : Type (u + 2)} [Category.{u + 2} A] [Category.{u + 2} B]
    (F G : A ⥤ B) (TX UX : B ⥤ B ⥤ B) (TY UY : A ⥤ A ⥤ A)
    (hF : F = G) (hX : TX = UX) (hY : TY = UY) (K L : A)
    (e : G.obj ((UY.obj K).obj L) ≅ ((UX.obj (G.obj K)).obj (G.obj L))) :
    F.obj ((TY.obj K).obj L) ≅ ((TX.obj (F.obj K)).obj (F.obj L)) := by
  subst G
  subst UX
  subst UY
  exact e

/-- Finite inverse image in fixed-module coordinates, cancelling the exact/derived
comparison and no other map. Source: coefficient realization
(blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def finitePullCoordinates {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.succ_pos m) Y) :=
  let R := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) X
  CompactSupportFiniteProjection.pullRealization S.toSixFunctorFiniteOperations f K ≪≫
    R.functor.mapIso ((CompactSupportFiniteProjection.fixedPullComparison
      (C := C) (E := E) (n := m + 1) f).symm.app
        ((CompactSupportFiniteProjection.realization
          (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) Y).inverse.obj K.obj))

/-- The canonical tensor distribution, including fixed-module cancellation at finite
coefficients and completed pullback at integral coefficients.
Source: the specified beta routes
(blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def tensorPull (s : PodCoefficientStage) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (K L : Ctf S s Y) :
    (pull S s f).obj ((tensor S s Y).obj (K, L)) ≅
      (tensor S s X).obj ((pull S s f).obj K, (pull S s f).obj L) := by
  cases s with
  | finite =>
    letI := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.succ_pos m)
    letI : IsNoetherianRing
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))) :=
      isNoetherian_of_finite _ _
    let RY := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) Y
    let RX := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) X
    let F := CompactSupportFiniteProjection.fixedDerivedPull
      (C := C) (E := E) (n := m + 1) f
    let TX := CompactSupportFiniteProjection.fixedTensor
      (C := C) (E := E) (n := m + 1) X
    let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1)))
    exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      (finitePullCoordinates S f (((tensor S .finite Y).obj (K, L)).obj) ≪≫
        RX.functor.mapIso (F.mapIso (RY.unitIso.app _).symm) ≪≫
        RX.functor.mapIso
          (ProEtale.leftDerivedUpperStarTensorIso A f.hom.left
            (RY.inverse.obj K.obj.obj) (RY.inverse.obj L.obj.obj)) ≪≫
        RX.functor.mapIso ((TX.mapIso
          (CompactSupportFiniteProjection.fixedPullRealization
            S.toSixFunctorFiniteOperations f K.obj).symm).app _ ≪≫
          (TX.obj _).mapIso
            (CompactSupportFiniteProjection.fixedPullRealization
              S.toSixFunctorFiniteOperations f L.obj).symm)))
  | integral =>
    letI := residueInvertible (C := C) X
    letI := residueInvertible (C := C) Y
    exact ObjectProperty.isoMk _
      (transportTensorPull (S.higher.integral.pull f)
        (constructibleIntegralPullback C.l E f.hom.left)
        (S.higher.integralTensor X)
        (Functor.currying.inverse.obj (constructibleIntegralTensor C.l E X.obj.left))
        (S.higher.integralTensor Y)
        (Functor.currying.inverse.obj (constructibleIntegralTensor C.l E Y.obj.left))
        (S.higher.integralPullback f) (S.higher.integralTensorNormalization X)
        (S.higher.integralTensorNormalization Y) K.obj L.obj
        (canonicalIntegralPullbackTensor C.l E f.hom.left K.obj L.obj))
  | rational =>
    letI := residueInvertible (C := C) X
    letI := residueInvertible (C := C) Y
    exact ObjectProperty.isoMk _
      (transportTensorPull (S.higher.rational.pull f)
        (rationalDerivedPullback C.l E f.hom.left)
        (S.higher.rationalTensor X)
        (Functor.currying.inverse.obj (rationalDerivedTensor C.l E X.obj.left))
        (S.higher.rationalTensor Y)
        (Functor.currying.inverse.obj (rationalDerivedTensor C.l E Y.obj.left))
        (S.higher.rationalPullback f) (S.higher.rationalTensorNormalization X)
        (S.higher.rationalTensorNormalization Y) K.obj L.obj
        (canonicalRationalPullbackTensor C.l E f.hom.left K.obj L.obj))
  | common =>
    letI := residueInvertible (C := C) X
    letI := residueInvertible (C := C) Y
    exact ObjectProperty.isoMk _
      (transportTensorPull (S.closure.commonStage.pull f)
        (commonStageDerivedPullback C.l C.Qbar f.hom.left)
        (S.closure.commonStageTensor X)
        (Functor.currying.inverse.obj (commonStageDerivedTensor C.l C.Qbar X.obj.left))
        (S.closure.commonStageTensor Y)
        (Functor.currying.inverse.obj (commonStageDerivedTensor C.l C.Qbar Y.obj.left))
        (S.closure.commonStagePullback f) (S.closure.commonStageTensorNormalization X)
        (S.closure.commonStageTensorNormalization Y) K.obj L.obj
        (canonicalCommonStagePullbackTensor C.l C.Qbar f.hom.left K.obj L.obj))

/-- The canonical Koszul symmetry, transported only by the recorded tensor equalities.
Source: d3 and d5 (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def symmetry (s : PodCoefficientStage) (X : SixFunctorSpace D) (K L : Ctf S s X) :
    (tensor S s X).obj (K, L) ≅ (tensor S s X).obj (L, K) := by
  cases s with
  | finite =>
    letI := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.succ_pos m)
    letI : IsNoetherianRing
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))) :=
      isNoetherian_of_finite _ _
    let R := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) X
    exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      (R.functor.mapIso (CategoryTheory.derivedTensorKoszulSymmetry
        (Sheaf (ProEt.topology X.obj.left)
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1)))))
        (R.inverse.obj K.obj.obj) (R.inverse.obj L.obj.obj))))
  | integral =>
    letI := residueInvertible (C := C) X
    exact ObjectProperty.isoMk _
      (eqToIso (congrArg (fun T ↦ (T.obj K.obj).obj L.obj)
          (S.higher.integralTensorNormalization X)) ≪≫
        pullbackTensorIntegralBraiding C.l E X.obj.left K.obj L.obj ≪≫
        (eqToIso (congrArg (fun T ↦ (T.obj L.obj).obj K.obj)
          (S.higher.integralTensorNormalization X))).symm)
  | rational =>
    letI := residueInvertible (C := C) X
    exact ObjectProperty.isoMk _
      (eqToIso (congrArg (fun T ↦ (T.obj K.obj).obj L.obj)
          (S.higher.rationalTensorNormalization X)) ≪≫
        pullbackTensorRationalBraiding C.l E X.obj.left K.obj L.obj ≪≫
        (eqToIso (congrArg (fun T ↦ (T.obj L.obj).obj K.obj)
          (S.higher.rationalTensorNormalization X))).symm)
  | common =>
    letI := residueInvertible (C := C) X
    exact ObjectProperty.isoMk _
      (eqToIso (congrArg (fun T ↦ (T.obj K.obj).obj L.obj)
          (S.closure.commonStageTensorNormalization X)) ≪≫
        pullbackTensorCommonBraiding C.l C.Qbar X.obj.left K.obj L.obj ≪≫
        (eqToIso (congrArg (fun T ↦ (T.obj L.obj).obj K.obj)
          (S.closure.commonStageTensorNormalization X))).symm)

/-- Bundle the actual proper/open pullbacks of a compactification. The intermediate
schemes are the scheme fibre products, not arbitrary Cartesian replacements.
Source: the Cartesian cube (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def compactifiedSquare {X Y X' Y' : SixFunctorSpace D}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left)
    (c : Compactification f.hom.left) : SixFunctorCompactifiedSquare D where
  X := X
  Y := Y
  X' := X'
  Y' := Y'
  Z := (compactSupportProjectionSquare f c).Z
  Z' := (compactSupportProjectionSquare f' (c.ofIsPullback sq)).Z
  f := f
  f' := f'
  g := g
  g' := g'
  i := (compactSupportProjectionSquare f c).i
  p := (compactSupportProjectionSquare f c).p
  i' := (compactSupportProjectionSquare f' (c.ofIsPullback sq)).i
  p' := (compactSupportProjectionSquare f' (c.ofIsPullback sq)).p
  h := ObjectProperty.homMk (Over.homMk (pullback.fst c.g g.hom.left) (by
    change pullback.fst c.g g.hom.left ≫ c.g ≫ Y.obj.hom =
      pullback.snd c.g g.hom.left ≫ Y'.obj.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, g.hom.w]))
  open_i := c.isOpenImmersion
  open_i' := (c.ofIsPullback sq).isOpenImmersion
  proper_p := c.isProper
  proper_p' := (c.ofIsPullback sq).isProper
  factorization := by ext; exact c.comm
  factorization' := by ext; exact (c.ofIsPullback sq).comm
  square := sq
  properSquare := IsPullback.of_hasPullback c.g g.hom.left
  openSquare := c.isPullback_i_ofIsPullback sq
  squareComm := by ext; exact sq.w
  properComm := by ext; exact pullback.condition
  openComm := by ext; exact (c.ofIsPullback_i_fst sq).symm

/-- Lift the recorded higher-stage exchange from its supplied coordinates to the
actual support and inverse-image coordinates, using only its equality fields.
Source: A2 (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def higherExchange {B : SixFunctorSpace D → Type (u + 2)}
    [∀ X, Category.{u + 2} (B X)] {O : SixFunctorPushStage D B}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData O T Q) (K : B Q.X) :
    (O.pull Q.g).obj ((O.support Q.f Q.compactification).obj K) ⟶
      (O.support Q.f' Q.compactification').obj ((O.pull Q.g').obj K) :=
  eqToHom (congrArg (fun F ↦ F.obj ((O.support Q.f Q.compactification).obj K))
      A.horizontal.symm) ≫
    A.stage.horizontal.map
      (eqToHom (congrArg (fun F ↦ F.obj K) A.compactSupport.symm)) ≫
    A.stage.compactExchange.app K ≫
    eqToHom (congrArg (fun F ↦ F.obj (A.stage.horizontal'.obj K)) A.compactSupport') ≫
    (O.support Q.f' Q.compactification').map
      (eqToHom (congrArg (fun F ↦ F.obj K) A.horizontal'))

/-- The actual exchange, with the canonical compactification comparison inserted
when a different target compactification is specified.
Source: A2 and the beta routes
(blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def exchange (s : PodCoefficientStage) {X Y X' Y' : SixFunctorSpace D}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated g.hom.left] [IsSeparated g'.hom.left]
    (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left)
    (c : Compactification f.hom.left) (c' : Compactification f'.hom.left)
    (K : Ctf S s X) :
    (pull S s g).obj ((support S s f c).obj K) ⟶
      (support S s f' c').obj ((pull S s g').obj K) := by
  apply ObjectProperty.homMk
  refine ?_ ≫ ((operations S s).comparison f' (c.ofIsPullback sq) c').hom.app
    (((operations S s).pull g').obj K.obj)
  cases s with
  | finite =>
    let RY' := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) Y'
    let F := CompactSupportFiniteProjection.fixedDerivedPull
      (C := C) (E := E) (n := m + 1) g
    let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1)))
    let F' := ProEtale.rightDerivedLowerShriekOfCompactification A (c.ofIsPullback sq)
    exact ObjectProperty.homMk
      ((finitePullCoordinates S g ((S.finite.support f c).obj K.obj)).hom ≫
        RY'.functor.map (F.map
          (CompactSupportFiniteProjection.fixedSupportRealization
            S.toSixFunctorFiniteOperations f c K.obj).hom) ≫
        RY'.functor.map
          ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c).app
            ((CompactSupportFiniteProjection.realization
              (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) X).inverse.obj
                K.obj.obj)) ≫
        (CompactSupportFiniteProjection.supportRealization S.toSixFunctorFiniteOperations
          f' (c.ofIsPullback sq) ((S.finite.pull g').obj K.obj) ≪≫
          RY'.functor.mapIso (F'.mapIso
            (CompactSupportFiniteProjection.fixedPullRealization
              S.toSixFunctorFiniteOperations g' K.obj))).inv)
  | integral => exact higherExchange (S.higher.integralExchange (compactifiedSquare sq c)) K.obj
  | rational => exact higherExchange (S.higher.rationalExchange (compactifiedSquare sq c)) K.obj
  | common => exact higherExchange (S.closure.commonStageExchange
      (compactifiedSquare sq c)) K.obj

attribute [local irreducible] finitePullCoordinates
  CompactSupportFiniteProjection.fixedSupportRealization
  CompactSupportFiniteProjection.fixedPullRealization
  CompactSupportFiniteProjection.supportRealization
  ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap

/-- Every displayed compact-support exchange is invertible on its actual finite-Tor
inputs. Source: A2 (blueprint: lem-sf-relative-product-base-change-factor-squares).
Proof: at finite coefficients use the proper base-change mate on the retained
etale-origin representative and the open base-change isomorphism, transported
through the fully faithful coefficient realization. At the other stages apply
the supplied compactExchange axiom, and conjugate by its equality fields and the
specified compactification comparison. Full inclusions reflect invertibility. -/
theorem exchange_isIso (s : PodCoefficientStage) {X Y X' Y' : SixFunctorSpace D}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated g.hom.left] [IsSeparated g'.hom.left]
    (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left)
    (c : Compactification f.hom.left) (c' : Compactification f'.hom.left)
    (K : Ctf S s X) : IsIso (exchange S s sq c c' K) := by
  apply (ObjectProperty.isIso_hom_iff (exchange S s sq c c' K)).mp
  cases s with
  | finite =>
    apply (ObjectProperty.isIso_hom_iff (exchange S .finite sq c c' K).hom).mp
    let Q := compactifiedSquare sq c
    let R := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) Y'
    let M := (CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) X).inverse.obj K.obj.obj
    have h := S.finiteCompactExchange Q K.obj K.property
    have hIso : IsIso (R.functor.map
        (((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing C.l E (m + 1))))) sq c).app M)) := h
    dsimp only [exchange, ObjectProperty.homMk]
    apply IsIso.comp_isIso'
    · apply IsIso.comp_isIso'
      · infer_instance
      · apply IsIso.comp_isIso'
        · infer_instance
        · exact IsIso.comp_isIso' hIso (by infer_instance)
    · infer_instance
  | integral =>
    have := S.integralExchange.compactExchange (compactifiedSquare sq c) K.obj K.property
    dsimp only [exchange, higherExchange, ObjectProperty.homMk]
    infer_instance
  | rational =>
    have := S.rationalExchange.compactExchange (compactifiedSquare sq c) K.obj K.property
    dsimp only [exchange, higherExchange, ObjectProperty.homMk]
    infer_instance
  | common =>
    have := S.commonExchange.compactExchange (compactifiedSquare sq c) K.obj K.property
    dsimp only [exchange, higherExchange, ObjectProperty.homMk]
    infer_instance

/-- The canonical exchange isomorphism, with no choice of its underlying arrow.
Source: beta and d2 (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def exchangeIso (s : PodCoefficientStage) {X Y X' Y' : SixFunctorSpace D}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated g.hom.left] [IsSeparated g'.hom.left]
    (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left)
    (c : Compactification f.hom.left) (c' : Compactification f'.hom.left)
    (K : Ctf S s X) :=
  letI := exchange_isIso S s sq c c' K
  asIso (exchange S s sq c c' K)

/-- The prescribed finite proper-counit/open projection, or the prescribed higher
projectionComponent, lifted through the full finite-Tor inclusion.
Source: PF in d1 and d4 (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def projection (s : PodCoefficientStage) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (c : Compactification f.hom.left)
    (K : Ctf S s X) (L : Ctf S s Y) :
    (tensor S s Y).obj ((support S s f c).obj K, L) ⟶
      (support S s f c).obj
        ((tensor S s X).obj (K, (pull S s f).obj L)) := by
  apply ObjectProperty.homMk
  cases s with
  | finite =>
    exact CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations
      f c K.obj ⟨L.obj.obj, L.property⟩
  | integral => exact compactSupportProjectionComponent S.higher.integralExchange f c K.obj L.obj
  | rational => exact compactSupportProjectionComponent S.higher.rationalExchange f c K.obj L.obj
  | common => exact compactSupportProjectionComponent S.closure.commonStageExchange f c K.obj L.obj

/-- A3 gives the actual inverses used in the six factors.
Source: A3 (blueprint: lem-sf-relative-product-base-change-factor-squares).
Proof: use finite projection invertibility on the retained finite-Tor objects,
or integralExchange.projection, rationalExchange.projection and commonExchange.projection.
The full inclusions reflect these isomorphisms; no new inverse is selected. -/
theorem projection_isIso (s : PodCoefficientStage) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (c : Compactification f.hom.left)
    (K : Ctf S s X) (L : Ctf S s Y) : IsIso (projection S s f c K L) := by
  apply (ObjectProperty.isIso_hom_iff (projection S s f c K L)).mp
  cases s with
  | finite =>
    have : LocallyOfFiniteType X.obj.hom := X.property.1
    have : QuasiCompact X.obj.hom := X.property.2
    have : LocallyOfFiniteType Y.obj.hom := Y.property.1
    have : IsLocallyNoetherian Y.obj.left :=
      LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
    have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by
      rw [f.hom.w]
      infer_instance
    have : QuasiCompact (f.hom.left ≫ Y.obj.hom) := by
      rw [f.hom.w]
      infer_instance
    have := locallyOfFiniteType_of_comp f.hom.left Y.obj.hom
    have := QuasiCompact.of_comp f.hom.left Y.obj.hom
    exact (compactSupportProjectionFormula S.toSixFunctorOperationDatum).1.isIso
      f c K.obj ⟨L.obj.obj, L.property⟩
  | integral =>
    exact S.integralExchange.projection (compactSupportProjectionSquare f c)
      K.obj L.obj K.property L.property
  | rational =>
    exact S.rationalExchange.projection (compactSupportProjectionSquare f c)
      K.obj L.obj K.property L.property
  | common =>
    exact S.commonExchange.projection (compactSupportProjectionSquare f c)
      K.obj L.obj K.property L.property

/-- The specified projection isomorphism; its inverse supplies d1 and d4.
Source: A3 (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def projectionIso (s : PodCoefficientStage) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (c : Compactification f.hom.left)
    (K : Ctf S s X) (L : Ctf S s Y) :=
  letI := projection_isIso S s f c K L
  asIso (projection S s f c K L)

/-- A product square of separated finite-type geometric k-schemes, with the supplied
compactifications. IsPullback retains every fibre product up to its canonical comparison.
Source: T = X times_B Y (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
structure Product (D : FiniteFieldDatum.{u}) where
  B : SixFunctorSpace D
  X : SixFunctorSpace D
  Y : SixFunctorSpace D
  T : SixFunctorSpace D
  [separatedB : IsSeparated B.obj.hom]
  [separatedX : IsSeparated X.obj.hom]
  [separatedY : IsSeparated Y.obj.hom]
  [separatedT : IsSeparated T.obj.hom]
  f : X ⟶ B
  g : Y ⟶ B
  u : T ⟶ X
  v : T ⟶ Y
  square : IsPullback u.hom.left v.hom.left f.hom.left g.hom.left
  cf : Compactification f.hom.left
  cg : Compactification g.hom.left
  cv : Compactification v.hom.left
  ch : Compactification (v ≫ g).hom.left

attribute [instance] Product.separatedB Product.separatedX Product.separatedY Product.separatedT

/-- Every morphism out of a separated geometric k-scheme is separated. This only
supplies the instance required by the domain restriction; it is no extra hypothesis.
Proof: f followed by the target structure map is the separated source structure map;
separatedness of a composite implies separatedness of its first factor.
Source: separated setting (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
@[instance] theorem mapSeparated {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y) :
    IsSeparated f.hom.left := by
  have : IsSeparated (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    infer_instance
  exact IsSeparated.of_comp f.hom.left Y.obj.hom

/-- The Cartesian base-change cube, including the actual map of the top products.
The u-face is specified as a commutative square; its pullback comparison is canonical.
The v-face and the two bottom faces give the actual base changes, not arbitrary maps.
Source: b, x, y, t (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
structure Change (G G' : Product D) where
  b : G'.B ⟶ G.B
  x : G'.X ⟶ G.X
  y : G'.Y ⟶ G.Y
  t : G'.T ⟶ G.T
  fSquare : IsPullback x.hom.left G'.f.hom.left G.f.hom.left b.hom.left
  gSquare : IsPullback y.hom.left G'.g.hom.left G.g.hom.left b.hom.left
  vSquare : IsPullback t.hom.left G'.v.hom.left G.v.hom.left y.hom.left
  uComm : t ≫ G.u = G'.u ≫ x

/-- The base change of the external tensor: distribute Lt* and then identify its
u- and v-pullbacks by canonical composition, in that order.
Source: Lt*H = H' (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def externalComparison (s : PodCoefficientStage) {G G' : Product D} (A : Change G G')
    (K : Ctf S s G.X) (L : Ctf S s G.Y) :=
  tensorPull S s A.t ((pull S s G.u).obj K) ((pull S s G.v).obj L) ≪≫
    (tensor S s G'.T).mapIso
      (Iso.prod (pullSquare S s A.t G'.u G.u A.x A.uComm K)
        (pullSquare S s A.t G'.v G.v A.y (by ext; exact A.vSquare.w) L))

/-- P, the pullback of K to the product.
Source: P (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
abbrev first (s : PodCoefficientStage) (G : Product D) (K : Ctf S s G.X) :=
  (pull S s G.u).obj K

/-- Q, compact support of the first input.
Source: Q (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
abbrev image (s : PodCoefficientStage) (G : Product D) (K : Ctf S s G.X) :=
  (support S s G.f G.cf).obj K

/-- H, the relative external tensor with the fixed order of its two factors.
Source: H (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
abbrev external (s : PodCoefficientStage) (G : Product D)
    (K : Ctf S s G.X) (L : Ctf S s G.Y) :=
  (tensor S s G.T).obj (first S s G K, (pull S s G.v).obj L)

/-- D0 through D6, in the displayed order. All seven are actual finite-Tor objects.
Source: the seven Di (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def object (s : PodCoefficientStage) (G : Product D)
    (K : Ctf S s G.X) (L : Ctf S s G.Y) : Fin 7 → Ctf S s G.B
  | 0 => (support S s (G.v ≫ G.g) G.ch).obj (external S s G K L)
  | 1 => (support S s G.g G.cg).obj
      ((support S s G.v G.cv).obj (external S s G K L))
  | 2 => (support S s G.g G.cg).obj ((tensor S s G.Y).obj
      ((support S s G.v G.cv).obj (first S s G K), L))
  | 3 => (support S s G.g G.cg).obj ((tensor S s G.Y).obj
      ((pull S s G.g).obj (image S s G K), L))
  | 4 => (support S s G.g G.cg).obj ((tensor S s G.Y).obj
      (L, (pull S s G.g).obj (image S s G K)))
  | 5 => (tensor S s G.B).obj ((support S s G.g G.cg).obj L, image S s G K)
  | 6 => (tensor S s G.B).obj (image S s G K, (support S s G.g G.cg).obj L)

/-- The six prescribed factor arrows: compositor; inverse PF for v; inverse inner
exchange tensored with identity; symmetry under g!; inverse PF for g; final symmetry.
Source: the six di (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def factor (s : PodCoefficientStage) (G : Product D)
    (K : Ctf S s G.X) (L : Ctf S s G.Y) (i : Fin 6) :
    object S s G K L i.castSucc ⟶ object S s G K L i.succ :=
  match i with
  | 0 => (composition S s G.v G.g G.cv G.cg G.ch (external S s G K L)).hom
  | 1 => (support S s G.g G.cg).map
      (projectionIso S s G.v G.cv (first S s G K) L).inv
  | 2 => (support S s G.g G.cg).map ((tensor S s G.Y).map
      (Prod.mkHom (exchangeIso S s G.square G.cf G.cv K).inv (𝟙 L)))
  | 3 => (support S s G.g G.cg).map
      (symmetry S s G.Y ((pull S s G.g).obj (image S s G K)) L).hom
  | 4 => (projectionIso S s G.g G.cg L (image S s G K)).inv
  | 5 => (symmetry S s G.B ((support S s G.g G.cg).obj L) (image S s G K)).hom

/-- The g-pullback comparison in beta3 and beta4: canonical composition first,
then g'* of the f-exchange. Source: beta3 and beta4
(blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def imagePullComparison (s : PodCoefficientStage) {G G' : Product D} (A : Change G G')
    (K : Ctf S s G.X) :=
  pullSquare S s A.y G'.g G.g A.b (by ext; exact A.gSquare.w) (image S s G K) ≪≫
    (pull S s G'.g).mapIso (exchangeIso S s A.fSquare G.cf G'.cf K)

/-- All seven beta comparisons, recursively in exactly the prescribed exchange order.
No beta is defined from the desired factor-square equation.
Source: beta0 through beta6 (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def beta (s : PodCoefficientStage) {G G' : Product D} (A : Change G G')
    (K : Ctf S s G.X) (L : Ctf S s G.Y) (i : Fin 7) :
    (pull S s A.b).obj (object S s G K L i) ≅
      object S s G' ((pull S s A.x).obj K) ((pull S s A.y).obj L) i :=
  match i with
  | 0 => exchangeIso S s (A.vSquare.paste_vert A.gSquare) G.ch G'.ch
        (external S s G K L) ≪≫
      (support S s (G'.v ≫ G'.g) G'.ch).mapIso (externalComparison S s A K L)
  | 1 => exchangeIso S s A.gSquare G.cg G'.cg
        ((support S s G.v G.cv).obj (external S s G K L)) ≪≫
      (support S s G'.g G'.cg).mapIso
        (exchangeIso S s A.vSquare G.cv G'.cv (external S s G K L) ≪≫
          (support S s G'.v G'.cv).mapIso (externalComparison S s A K L))
  | 2 => exchangeIso S s A.gSquare G.cg G'.cg
        ((tensor S s G.Y).obj ((support S s G.v G.cv).obj (first S s G K), L)) ≪≫
      (support S s G'.g G'.cg).mapIso
        (tensorPull S s A.y ((support S s G.v G.cv).obj (first S s G K)) L ≪≫
          (tensor S s G'.Y).mapIso
            (Iso.prod (exchangeIso S s A.vSquare G.cv G'.cv (first S s G K) ≪≫
              (support S s G'.v G'.cv).mapIso
                (pullSquare S s A.t G'.u G.u A.x A.uComm K)) (Iso.refl _)))
  | 3 => exchangeIso S s A.gSquare G.cg G'.cg
        ((tensor S s G.Y).obj ((pull S s G.g).obj (image S s G K), L)) ≪≫
      (support S s G'.g G'.cg).mapIso
        (tensorPull S s A.y ((pull S s G.g).obj (image S s G K)) L ≪≫
          (tensor S s G'.Y).mapIso (Iso.prod (imagePullComparison S s A K) (Iso.refl _)))
  | 4 => exchangeIso S s A.gSquare G.cg G'.cg
        ((tensor S s G.Y).obj (L, (pull S s G.g).obj (image S s G K))) ≪≫
      (support S s G'.g G'.cg).mapIso
        (tensorPull S s A.y L ((pull S s G.g).obj (image S s G K)) ≪≫
          (tensor S s G'.Y).mapIso (Iso.prod (Iso.refl _) (imagePullComparison S s A K)))
  | 5 => tensorPull S s A.b ((support S s G.g G.cg).obj L) (image S s G K) ≪≫
      (tensor S s G'.B).mapIso
        (Iso.prod (exchangeIso S s A.gSquare G.cg G'.cg L)
          (exchangeIso S s A.fSquare G.cf G'.cf K))
  | 6 => tensorPull S s A.b (image S s G K) ((support S s G.g G.cg).obj L) ≪≫
      (tensor S s G'.B).mapIso
        (Iso.prod (exchangeIso S s A.fSquare G.cf G'.cf K)
          (exchangeIso S s A.gSquare G.cg G'.cg L))

/-- The finite domain retains its actual bounded-below fixed-module complex and
FixedEtaleOriginWitness, together with its coefficient-realization identification.
Other stages are the completed/transported domains and need no finite-origin datum.
Source: witnessed domains (blueprint: lem-sf-relative-product-base-change-factor-squares). -/
def Witness (s : PodCoefficientStage) (X : SixFunctorSpace D) (K : Ctf S s X) :
    Type (u + 2) :=
  match s with
  | .finite =>
    Σ M : DerivedCategory.Plus (Sheaf (ProEt.topology X.obj.left)
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))))),
      (M.obj ≅ (CompactSupportFiniteProjection.realization
        (C := C) (E := E) (n := m + 1) (hn := Nat.succ_pos m) X).inverse.obj K.obj.obj) ×
        FixedEtaleOriginWitness X.obj.left
          (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))) M
  | .integral => PUnit
  | .rational => PUnit
  | .common => PUnit

/-- Each of the six individual relative-product factor squares commutes, with the
seven comparison isomorphisms defined independently above.

Source: latest blueprint sec-six-functors/sk-thm-sf-kunneth-relative/_section.md,
coherence (iii) and the six displayed factors
(blueprint: lem-sf-relative-product-base-change-factor-squares).

Proof:
1. At finite coefficients use normalized ringed derived tensor distribution and its
Koszul symmetry. Integral coherence holds on the actual strict quotient towers before
derived limit, by lem-pur-integral-coherence-tower, so it is equality of completed maps,
not an inference from separate reductions. Rationalization and common finite fields
transport these equations (def-weil-derived-pullback-tensor-hom).
2. For factor 0 apply vertical exchange pasting to v followed by g, evaluate at H,
and then use naturality for externalComparison. This gives the exchange order g then v.
3. For factor 1 reverse the invertible projection square for v along y
(prop-sf-pf-coherence), apply g'!, and use naturality of the g-exchange
(fix-lem-exchanges).
4. For factor 2 compare the two horizontal pastings of the Cartesian cube
(fix-lem-exchanges). Invert the inner f/g exchanges, tensor with identity on L',
and apply g'! and naturality of the g-exchange.
5. For factor 3 tensor distribution respects the signed symmetry; then use symmetry
naturality at imagePullComparison and exchange naturality under g!.
6. For factor 4 reverse the projection square for g along b, and use its second-input
naturality at the f-exchange. The input Q is finite-Tor by A4.
7. For factor 5 use signed pullback symmetry and its naturality at the exchanges for
g and f, obtaining precisely their two opposite tensor orders. These are the six
separate equations, with the stated canonical composition comparisons. -/
theorem factor_squares (s : PodCoefficientStage) (G G' : Product D) (A : Change G G')
    (K : Ctf S s G.X) (L : Ctf S s G.Y)
    (_wK : Witness S s G.X K) (_wL : Witness S s G.Y L) (i : Fin 6) :
    (pull S s A.b).map (factor S s G K L i) ≫ (beta S s A K L i.succ).hom =
      (beta S s A K L i.castSucc).hom ≫
        factor S s G' ((pull S s A.x).obj K) ((pull S s A.y).obj L) i := by
  sorry

end WeilConjectures.RelativeProductBaseChange
