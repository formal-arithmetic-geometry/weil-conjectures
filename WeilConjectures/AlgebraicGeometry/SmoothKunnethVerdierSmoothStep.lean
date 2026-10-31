/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpecializedSixFunctorKunnethMaps
public import WeilConjectures.AlgebraicGeometry.SixFunctorOrientation
public import WeilConjectures.AlgebraicGeometry.FiniteDualizingCondensedAgreement
public import WeilConjectures.SecSmoothPurity.FiniteNativeTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteIntrinsicRealizationComparisons
public import WeilConjectures.AlgebraicGeometry.CanonicalFiniteIntrinsicTensorComparison
public import WeilConjectures.AlgebraicGeometry.FinitePullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteRationalDerivedOperations
public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatumStages
public import WeilConjectures.AlgebraicGeometry.FiniteTateSiteDescentDefinitions
public import WeilConjectures.AlgebraicGeometry.DlLocallyConstructibleAdicHeart
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Smooth exceptional Künneth in the recorded pro-étale categories

Source: latest blueprint, package clause (5), final sentence
(blueprint: lem-sf-kunneth-verdier-smooth-step).
The objects and alpha are precisely those of the recorded specialized product maps.
The orientation is O.primary.component transported by its normalized counit mate.
The public helpers only express these maps at their required native endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.SmoothKunnethNative

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
  [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] (m : ℕ)

/-- The existing finite admissible condensed coefficient, at exponent m+1.
Source: finite coefficient convention
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
abbrev ring := FiniteCondensedDualizing.ring C.l E m

/-- Retain the underlying scheme in the orientation indexing category.
Source: finite-type setting
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
abbrev space (X : SepFinType D.k) : SixFunctorSpace D :=
  ⟨X.obj, X.property.1, X.property.2.1⟩

/-- The identical underlying arrow, with its orientation index.
Source: finite-type setting
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
abbrev arrow {X Y : SepFinType D.k} (f : X ⟶ Y) : space X ⟶ space Y :=
  ObjectProperty.homMk f.hom

variable (e : ∀ T : Scheme.{u}, FiniteCondensedDualizing.EncodingAt C.l E m T)

/-- The actual normalized equivalence to intrinsic pro-étale modules.
Source: section-action encoding followed by the intrinsic scalar equivalence
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def realization (X : Scheme.{u}) :
    CompactificationReindexing.D (ring (C := C) (E := E) m).X X ≌
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing C.l E (m + 1)) :=
  (e X).fixedDerived.trans
    (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing C.l E (m + 1)))

/-- The recorded pro-étale shifted line in native internal-module coordinates.
Source: the finite component of def-sf-orientation
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def line (X : SixFunctorSpace D) (d : ℕ) :=
  (realization m e X.obj.left).inverse.obj (sfOrientationReducedLine D C E m X d).obj

/-- Native support followed by normalized encoding, then intrinsic support.
Source: the prescribed open/proper realization and S.finiteSupport
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def support
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.succ_pos m))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.succ_pos m) X) :
    (CompactificationReindexing.F (ring (C := C) (E := E) m).X c).obj
      ((realization m e X.obj.left).inverse.obj K.obj) ≅
    (realization m e Y.obj.left).inverse.obj ((S.finite.support f c).obj K).obj := by
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let EX := (e X.obj.left).fixedDerived
  let EY := (e Y.obj.left).fixedDerived
  let QX := sfIntrinsicDerivedEquivalence X.obj.left A
  let QY := sfIntrinsicDerivedEquivalence Y.obj.left A
  let F := CompactificationReindexing.F (ring (C := C) (E := E) m).X c
  let FF := ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) c
  let σ := FiniteCondensedDualizing.supportEncoding C.l E m c e
  let first : F.obj (EX.inverse.obj (QX.inverse.obj K.obj)) ≅
      EY.inverse.obj (FF.obj (QX.inverse.obj K.obj)) :=
    EY.unitIso.app _ ≪≫ EY.inverse.mapIso (σ.app _) ≪≫
      EY.inverse.mapIso (FF.mapIso (EX.counitIso.app _))
  let second : FF.obj (QX.inverse.obj K.obj) ≅
      QY.inverse.obj ((S.finite.support f c).obj K).obj :=
    QY.unitIso.app _ ≪≫ QY.inverse.mapIso
      ((sfIntrinsicCompactSupportComparison A c).symm.app _ ≪≫
        (sixFunctorFiniteSupport D C E (m + 1) (Nat.succ_pos m) f c).mapIso
          (QX.counitIso.app K.obj) ≪≫ (S.finiteSupport f c).symm.app K)
  exact first ≪≫ EY.inverse.mapIso second

/-- The degree-zero line is the native coefficient unit, with its actual root/site
normalization. Source: the unit comparison in def-sf-orientation
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def lineUnit (r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    (X : SixFunctorSpace D) : line m e X 0 ≅ 𝟙_ _ := by
  let EX := (e X.obj.left).fixedDerived
  letI : EX.functor.Monoidal := FiniteNativeTensor.encodingMonoidal
    (Padic.coefficientExtensionRing C.l E (m + 1)) X.obj.left (e X.obj.left)
  exact EX.inverse.mapIso
    ((sfOrientationFiniteSiteUnit D C E m r hA X).symm ≪≫
      FiniteCondensedDualizing.siteUnit C.l E m X.obj.left) ≪≫
    EX.inverse.mapIso (Functor.Monoidal.εIso EX.functor) ≪≫
    (EX.unitIso.app _).symm



/-- The tensor comparison obtained from the recorded intrinsic tensor model and
normalized native encoding. Source: finite tensor realization
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def tensorCoordinates (X : SixFunctorSpace D)
    (K L : proEtaleDerivedCategory X.obj.left
      (Padic.coefficientExtensionRing C.l E (m + 1))) :
    (realization m e X.obj.left).inverse.obj
        ((finiteIntrinsicDerivedTensor C.l E X.obj.left m).obj (K, L)) ≅
      (realization m e X.obj.left).inverse.obj K ⊗
        (realization m e X.obj.left).inverse.obj L := by
  let EX := (e X.obj.left).fixedDerived
  let QX := sfIntrinsicDerivedEquivalence X.obj.left
    (Padic.coefficientExtensionRing C.l E (m + 1))
  letI : EX.functor.Monoidal := FiniteNativeTensor.encodingMonoidal
    (Padic.coefficientExtensionRing C.l E (m + 1)) X.obj.left (e X.obj.left)
  letI : EX.inverse.Monoidal := EX.inverseMonoidal
  let a : QX.inverse.obj
      ((finiteIntrinsicDerivedTensor C.l E X.obj.left m).obj (K, L)) ≅
      QX.inverse.obj K ⊗ QX.inverse.obj L :=
    QX.inverse.mapIso
      ((IntegralProjectionReduction.canonicalFiniteIntrinsicTensorComparison
        (C := C) (E := E) m X).app (K, L)) ≪≫ (QX.unitIso.app _).symm
  exact EX.inverse.mapIso a ≪≫
    (Functor.Monoidal.μIso EX.inverse (QX.inverse.obj K) (QX.inverse.obj L)).symm

/-- The existing intrinsic inverse-image comparison in native coordinates.
Source: normalized section-action pullback and intrinsic realization
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def pullCoordinates {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : proEtaleDerivedCategory Y.obj.left
      (Padic.coefficientExtensionRing C.l E (m + 1))) :
    (realization m e X.obj.left).inverse.obj
      ((finiteDerivedPullback C.l E m f.hom.left).obj K) ≅
    (CompactificationReindexing.P (ring (C := C) (E := E) m).X f.hom.left).obj
      ((realization m e Y.obj.left).inverse.obj K) :=
  (e X.obj.left).fixedDerived.inverse.mapIso
    ((IntegralProjectionReduction.FiniteIntrinsicRealization.inversePullback
      (C := C) (E := E) m f).app K) ≪≫
    (FiniteNativeTensor.inverseEncodingPull
      (Padic.coefficientExtensionRing C.l E (m + 1)) e f.hom.left).symm.app _

/-- Transport of canonicalFinitePullbackTensor, with the specified endpoint
coordinates. This definition uses that canonical map, not a new tensorator.
Source: def-pur-finite-pullback-tensor-comparison, canonical finite map
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def pullTensor {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K L : CompactificationReindexing.D (ring (C := C) (E := E) m).X Y.obj.left) :
    (CompactificationReindexing.P (ring (C := C) (E := E) m).X f.hom.left).obj (K ⊗ L) ≅
    (CompactificationReindexing.P (ring (C := C) (E := E) m).X f.hom.left).obj K ⊗
      (CompactificationReindexing.P (ring (C := C) (E := E) m).X f.hom.left).obj L := by
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  letI := dlAdicGeometricResidueInvertible D C Y.obj.left
  let RX := realization m e X.obj.left
  let RY := realization m e Y.obj.left
  let P := CompactificationReindexing.P (ring (C := C) (E := E) m).X f.hom.left
  let MK := RY.functor.obj K
  let ML := RY.functor.obj L
  let src : K ⊗ L ≅ RY.inverse.obj
      ((finiteIntrinsicDerivedTensor C.l E Y.obj.left m).obj (MK, ML)) :=
    (RY.unitIso.app K ⊗ᵢ RY.unitIso.app L) ≪≫
      (tensorCoordinates m e Y MK ML).symm
  exact P.mapIso src ≪≫ (pullCoordinates m e f _).symm ≪≫
    RX.inverse.mapIso (canonicalFinitePullbackTensor C.l E f.hom.left m MK ML) ≪≫
    tensorCoordinates m e X _ _ ≪≫
    (pullCoordinates m e f MK ⊗ᵢ pullCoordinates m e f ML) ≪≫
    (P.mapIso (RY.unitIso.app K).symm ⊗ᵢ P.mapIso (RY.unitIso.app L).symm)

/-- A proof-only domain obligation: the transported, explicitly constructed lines
are constructible of finite Tor amplitude. Source: the locally free Tate lines
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def LinesConstructible : Prop := ∀ (X : SixFunctorSpace D) (d : ℕ),
  (constantModelBoundedConstructible (ring (C := C) (E := E) m).X X.obj.left ⊓
    DerivedCategory.finiteTorAmplitude _) (line m e X d)

/-- Bundle the actual shifted line using its proof-only domain certificate.
Source: finite-Tor orientation domain
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def lineObject (h : LinesConstructible m e) (X : SixFunctorSpace D) (d : ℕ) :
    ConstantModelConstructibleFiniteTor (ring (C := C) (E := E) m).X X.obj.left :=
  ⟨line m e X d, h X d⟩

/-- The pro-étale component O.primary.component, transported by its actual support
counit mate into precisely the exceptional adjunction J used by kv-maps.
Source: def-sf-orientation, finite component and unit-normalized realization
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def unitComponent
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_pos m)} (O : SfOrientationDatum S)
    (h : LinesConstructible m e) {X Y : SepFinType D.k} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left)
    (J : SixOperationsLocalizingAdjunction (ring (C := C) (E := E) m).X c) :
    lineObject m e h (space X) d ⟶
      (ProductComparisons.exceptional (ring (C := C) (E := E) m) J).obj
        (lineObject m e h (space Y) 0) := by
  letI : IsSeparated (arrow f).hom.left := inferInstanceAs (IsSeparated f.hom.left)
  letI : SmoothOfRelativeDimension d (arrow f).hom.left :=
    inferInstanceAs (SmoothOfRelativeDimension d f.hom.left)
  let a := O.primary.component (arrow f) d c
  exact (ProductComparisons.adjunction (ring (C := C) (E := E) m) J).homEquiv _ _
    ⟨(support m e S.toSixFunctorFiniteOperations (arrow f) c
        (sfOrientationReducedLine D C E m (space X) d)).hom ≫
      (realization m e Y.obj.left).inverse.map
        (((S.finite.support (arrow f) c).map a.hom) ≫
          (S.finite.exceptionalAdjunction (arrow f) c).counit.app _).hom⟩

/-- The theta tensor formula for the same exceptional adjunction as kv-maps.
Source: def-sf-orientation, general coefficient convention
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def gamma
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_pos m)} (O : SfOrientationDatum S)
    (h : LinesConstructible m e)
    {H : CompactSupportComposition.CoherentData (ring (C := C) (E := E) m).X D.k}
    (A : RelativeKunneth.IsoFamily (ring (C := C) (E := E) m) H)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    {X Y : SepFinType D.k} (f : X ⟶ Y) [IsSeparated f.hom.left]
    (d : ℕ) [SmoothOfRelativeDimension d f.hom.left] (c : Compactification f.hom.left)
    (J : SixOperationsLocalizingAdjunction (ring (C := C) (E := E) m).X c)
    (L : ConstantModelConstructibleFiniteTor (ring (C := C) (E := E) m).X Y.obj.left) :
    line m e (space X) d ⊗
      (CompactificationReindexing.P (ring (C := C) (E := E) m).X f.hom.left).obj L.obj ⟶
    ((ProductComparisons.exceptional (ring (C := C) (E := E) m) J).obj L).obj := by
  let Λ := ring (C := C) (E := E) m
  let U := lineObject m e h (space Y) 0
  let G := ProductComparisons.exceptional Λ J
  let ω := G.obj U
  let idSquare : IsPullback (𝟙 X.obj.left) f.hom.left f.hom.left
      (𝟙 Y.obj.left) := IsPullback.of_id_fst
  let dId := RelativeKunneth.identityDiagram f idSquare
  let cId := RelativeKunneth.identityModels f idSquare c
  let K := RelativeKunneth.IsoFamily.exteriorObject Λ A dId ω L
  let hpf : IsIso (CompactificationReindexing.pf Λ.X c
      ((CompactificationReindexing.P Λ.X (𝟙 X.obj.left)).obj ω.obj) L.obj) :=
    (A.factors dId cId ω L).1
  let ε := (ProductComparisons.adjunction Λ J).counit.app U
  let j := (leftDerivedUpperStarId Λ.X X.obj.left).app ω.obj
  let θ : K ⟶ G.obj L := (ProductComparisons.adjunction Λ J).homEquiv _ _
    ⟨@inv _ _ _ _ (CompactificationReindexing.pf Λ.X c
        ((CompactificationReindexing.P Λ.X (𝟙 X.obj.left)).obj ω.obj) L.obj) hpf ≫
      (((CompactificationReindexing.F Λ.X c).map j.hom ≫ ε.hom) ⊗ₘ 𝟙 L.obj) ≫
      ((lineUnit m e r hA (space Y)).hom ⊗ₘ 𝟙 L.obj) ≫ (λ_ L.obj).hom⟩
  exact ((unitComponent m e O h f d c J).hom ⊗ₘ 𝟙 _) ≫
    (j.inv ⊗ₘ 𝟙 _) ≫ θ.hom

/-- The ordinary pro-étale root-line presentation of the recorded reduced line.
Source: the coefficient comparison of def-sf-orientation
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def rootCoordinates (r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    (X : SixFunctorSpace D) (d : ℕ) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  sfOrientationFiniteSiteLine C.l E X.obj.left (sfOrientationPrimeUnit D C X) m r hA d

/-- The canonical pullback of the shifted native line, from the same root/site maps.
Source: twist pullback in def-sf-orientation
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def linePull (r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (d : ℕ) :
    (CompactificationReindexing.P (ring (C := C) (E := E) m).X f.hom.left).obj
      (line m e Y d) ≅ line m e X d := by
  let A := finiteTateCoefficient C.l E m
  let N := C.l ^ (r + 1)
  let hN : 0 < N := pow_pos (Fact.out : C.l.Prime).pos _
  let hX : IsUnit (N : Γ(X.obj.left, ⊤)) := by
    simpa only [N, Nat.cast_pow] using (sfOrientationPrimeUnit D C X).pow (r + 1)
  let hY : IsUnit (N : Γ(Y.obj.left, ⊤)) := by
    simpa only [N, Nat.cast_pow] using (sfOrientationPrimeUnit D C Y).pow (r + 1)
  let PX := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X.obj.left).mapDerivedCategory
  let PY := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y.obj.left).mapDerivedCategory
  let P := (ProEtale.upperStar (ModuleCat.{u + 1} A) f.hom.left).leftDerivedFunctor
  exact (FiniteNativeTensor.inverseEncodingPull
      (Padic.coefficientExtensionRing C.l E (m + 1)) e f.hom.left).app _ ≪≫
    (e X.obj.left).fixedDerived.inverse.mapIso
      (P.mapIso (rootCoordinates m r hA Y d).symm ≪≫
        (ProEtale.derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} A)
          f.hom.left).app _ ≪≫
        PX.mapIso (sfOrientationEtaleLinePullback A N hN hA f.hom.left hX hY d) ≪≫
        rootCoordinates m r hA X d)

/-- Multiplication of shifted native lines via the prescribed root tensor product.
Source: twist multiplication and shift addition in def-sf-orientation
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def lineProduct (r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    (X : SixFunctorSpace D) (d d' : ℕ) :
    line m e X d ⊗ line m e X d' ≅ line m e X (d + d') := by
  let A := finiteTateCoefficient C.l E m
  let N := C.l ^ (r + 1)
  let hN : 0 < N := pow_pos (Fact.out : C.l.Prime).pos _
  let hX : IsUnit (N : Γ(X.obj.left, ⊤)) := by
    simpa only [N, Nat.cast_pow] using (sfOrientationPrimeUnit D C X).pow (r + 1)
  let EX := (e X.obj.left).fixedDerived
  let V := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X.obj.left).mapDerivedCategory
  letI : EX.functor.Monoidal := FiniteNativeTensor.encodingMonoidal
    (Padic.coefficientExtensionRing C.l E (m + 1)) X.obj.left (e X.obj.left)
  letI : EX.inverse.Monoidal := EX.inverseMonoidal
  letI : V.Monoidal := FiniteNativeTensor.siteMonoidal
    (Padic.coefficientExtensionRing C.l E (m + 1)) X.obj.left
  exact (Functor.Monoidal.μIso EX.inverse _ _) ≪≫
    EX.inverse.mapIso
      ((rootCoordinates m r hA X d).symm ⊗ᵢ (rootCoordinates m r hA X d').symm) ≪≫
    EX.inverse.mapIso ((Functor.Monoidal.μIso V _ _) ≪≫
      V.mapIso (sfOrientationEtaleProduct A N hN hA X.obj.left hX d d') ≪≫
      rootCoordinates m r hA X (d + d'))



/-- Separation of the structural map implies separation of arrows over the base.
Source: finite-type setting
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
instance separated {k : Type u} [Field k] {X Y : SepFinType k} (f : X ⟶ Y) :
    IsSeparated f.hom.left := by
  have : IsSeparated (f.hom.left ≫ Y.obj.hom) := by
    simpa only [Over.w] using (inferInstanceAs (IsSeparated X.obj.hom))
  exact IsSeparated.of_comp f.hom.left Y.obj.hom

/-- The canonical source product comparison, using the recorded intrinsic tensor
comparison at all three pullbacks and the recorded root-line constraints.
Source: the canonical comparison in the smooth step
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def canonical (G : ProductComparisons.Geometry D.k) (r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    (d₁ d₂ : ℕ)
    (L₁ : CompactificationReindexing.D (ring (C := C) (E := E) m).X G.Y₁.obj.left)
    (L₂ : CompactificationReindexing.D (ring (C := C) (E := E) m).X G.Y₂.obj.left) :=
  let Λ := ring (C := C) (E := E) m
  let P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ CompactificationReindexing.P Λ.X f
  let F := G.q ≫ G.v
  let B₁ := (P G.f₁.hom.left).obj L₁
  let B₂ := (P G.f₂.hom.left).obj L₂
  let T₁ := line m e (space G.X₁) d₁
  let T₂ := line m e (space G.X₂) d₂
  let pure :=
    (RelativeKunneth.pullPath Λ G.r₁.hom.left G.f₁.hom.left
      ((G.q ≫ G.v ≫ G.t₁).hom.left)
      (by
        rw [← G.path₁, Category.assoc, G.exchange₁.w, ← Category.assoc]
        rw [G.relativeProduct.w]
        rfl) L₁ ⊗ᵢ
      RelativeKunneth.pullPath Λ G.r₂.hom.left G.f₂.hom.left
        ((G.q ≫ G.v ≫ G.t₂).hom.left)
        (by rw [← G.path₂, Category.assoc, G.exchange₂.w]; rfl) L₂) ≪≫
      ((leftDerivedUpperStarComp Λ.X F.hom.left G.t₁.hom.left).app L₁ ⊗ᵢ
        (leftDerivedUpperStarComp Λ.X F.hom.left G.t₂.hom.left).app L₂) ≪≫
      (pullTensor m e (arrow F) _ _).symm
  let lines := (linePull m e r hA (arrow G.r₁) d₁ ⊗ᵢ
    linePull m e r hA (arrow G.r₂) d₂) ≪≫
      lineProduct m e r hA (space G.W) d₁ d₂
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology G.W.obj.left) Ab.{u + 1}) (condensedRingObj Λ.X G.W.obj.left))
  (pullTensor m e (arrow G.r₁) T₁ B₁ ⊗ᵢ
    pullTensor m e (arrow G.r₂) T₂ B₂) ≪≫
    Functor.Monoidal.μIso (tensor _)
      ((P G.r₁.hom.left).obj T₁, (P G.r₁.hom.left).obj B₁)
      ((P G.r₂.hom.left).obj T₂, (P G.r₂.hom.left).obj B₂) ≪≫ (lines ⊗ᵢ pure)

end WeilConjectures.SmoothKunnethNative

namespace WeilConjectures
open SmoothKunnethNative

set_option maxHeartbeats 1600000 in
-- The recorded native product tuple has a large dependent type.
set_option synthInstance.maxHeartbeats 160000 in
/-- The displayed conjugacy proposition, with the canonical geometric instances
expanded inside a definition so downstream proofs can unfold every abbreviation.
The existential certificates supply only domain and inverse proofs, never maps.
Source: package clause (5), smooth exceptional Künneth compatibility
(blueprint: lem-sf-kunneth-verdier-smooth-step). -/
def smoothExceptionalKunnethCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_pos m)} (O : SfOrientationDatum S)
    (e : ∀ T : Scheme.{u}, FiniteCondensedDualizing.EncodingAt C.l E m T)
    (hne : ringChar D.k ≠ C.l)
    (hΛ : IsLocalizingAdmissibleCoefficient C.l (ring (C := C) (E := E) m).X)
    (J : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y) (c : Compactification f.hom.left),
      SixOperationsLocalizingAdjunction (ring (C := C) (E := E) m).X c)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    (G : ProductComparisons.Geometry D.k) (c : ProductComparisons.Models G) (d₁ d₂ : ℕ)
    [SmoothOfRelativeDimension d₁ G.f₁.hom.left]
    [SmoothOfRelativeDimension d₂ G.f₂.hom.left]
    (L₁ : ConstantModelConstructibleFiniteTor
      (ring (C := C) (E := E) m).X G.Y₁.obj.left)
    (L₂ : ConstantModelConstructibleFiniteTor
      (ring (C := C) (E := E) m).X G.Y₂.obj.left) : Prop :=
    let Λ := ring (C := C) (E := E) m
    let R := ProductComparisons.relativeDatum D C.l hne
    let A := R.product Λ hΛ
    let α := (specializedSixFunctorKunnethMaps Λ D C.l hne hΛ J).2.1 G c L₁ L₂
    letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension d₁) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (n := d₁)
    letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension d₂) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (n := d₂)
    letI : SmoothOfRelativeDimension d₁ G.u.hom.left :=
      MorphismProperty.of_isPullback G.exchange₁
        (inferInstanceAs (SmoothOfRelativeDimension d₁ G.f₁.hom.left))
    letI : SmoothOfRelativeDimension d₂ G.v.hom.left :=
      MorphismProperty.of_isPullback G.exchange₂
        (inferInstanceAs (SmoothOfRelativeDimension d₂ G.f₂.hom.left))
    letI : SmoothOfRelativeDimension d₁ G.q.hom.left :=
      MorphismProperty.of_isPullback G.relativeProduct
        (inferInstanceAs (SmoothOfRelativeDimension d₁ G.u.hom.left))
    letI : SmoothOfRelativeDimension (d₁ + d₂) (G.q ≫ G.v).hom.left :=
      smoothOfRelativeDimension_comp (n := d₁) (m := d₂) G.q.hom.left G.v.hom.left
    ∃ hline : LinesConstructible m e,
    let γ₁ := gamma m e O hline A r hA G.f₁ d₁ c.f₁ (J G.f₁ c.f₁) L₁
    let γ₂ := gamma m e O hline A r hA G.f₂ d₂ c.f₂ (J G.f₂ c.f₂) L₂
    let γ := gamma m e O hline A r hA (G.q ≫ G.v) (d₁ + d₂) c.relative.total
      (J (G.q ≫ G.v) c.relative.total) (RelativeKunneth.IsoFamily.exteriorObject Λ A G.target L₁ L₂)
    ∃ hγ : IsIso γ,
      ((CompactificationReindexing.P Λ.X G.r₁.hom.left).map γ₁ ⊗ₘ
        (CompactificationReindexing.P Λ.X G.r₂.hom.left).map γ₂) ≫ α.hom ≫
        @inv _ _ _ _ γ hγ = (canonical m e G r hA d₁ d₂ L₁.obj L₂.obj).hom ∧
      IsIso α

set_option maxHeartbeats 1600000 in
-- Elaborate the same recorded coefficient and product interfaces in the signature.
set_option synthInstance.maxHeartbeats 160000 in
/-- Conjugating exceptional Künneth by the smooth orientations gives exactly
canonical pullback--tensor, and consequently exceptional Künneth is invertible.
The existential `hγ` packages the invertibility of the actual general-coefficient
orientation map so that its inverse is a well-typed morphism; it supplies no map.

Source: `sk-thm-sf-package/_section.md`, clause (5), final sentence
(blueprint: lem-sf-kunneth-verdier-smooth-step).

Proof: (1) Finite smooth purity, cohomological smoothness and the unit orientation
identify every general-coefficient orientation with the specified theta tensor
formula; both it and the product orientation are isomorphisms. Smooth relative
dimensions are preserved by the two product base changes and add under composition.
(2) Transpose the exceptional map for (f,id). The inverse compact-support exchange,
the pulled counit and projection coherence identify its transpose with theta
composed with the dualizing base-change map. The orientation base-change equation
therefore identifies this map with the canonical pullback--tensor comparison.
(3) Factor the product as (f1,id) followed by (id,f2). The two identity-factor
formulas, factor symmetry and the right-adjoint composition comparison identify
the two-factor exceptional Künneth map. Orientation composition and the canonical
pullback/tensor coherence give the displayed equality. Every other factor is
invertible, hence alpha is an isomorphism. This also covers empty schemes,
dimension zero, identity morphisms and zero complexes. -/
theorem exceptionalKunneth_smooth_step
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_pos m)} (O : SfOrientationDatum S)
    (e : ∀ T : Scheme.{u}, FiniteCondensedDualizing.EncodingAt C.l E m T)
    (hne : ringChar D.k ≠ C.l)
    (hΛ : IsLocalizingAdmissibleCoefficient C.l (ring (C := C) (E := E) m).X)
    (J : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y) (c : Compactification f.hom.left),
      SixOperationsLocalizingAdjunction (ring (C := C) (E := E) m).X c)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    (G : ProductComparisons.Geometry D.k) (c : ProductComparisons.Models G) (d₁ d₂ : ℕ)
    [SmoothOfRelativeDimension d₁ G.f₁.hom.left]
    [SmoothOfRelativeDimension d₂ G.f₂.hom.left]
    (L₁ : ConstantModelConstructibleFiniteTor
      (ring (C := C) (E := E) m).X G.Y₁.obj.left)
    (L₂ : ConstantModelConstructibleFiniteTor
      (ring (C := C) (E := E) m).X G.Y₂.obj.left) :
    smoothExceptionalKunnethCompatibility O e hne hΛ J r hA G c d₁ d₂ L₁ L₂ := by
  sorry

end WeilConjectures
