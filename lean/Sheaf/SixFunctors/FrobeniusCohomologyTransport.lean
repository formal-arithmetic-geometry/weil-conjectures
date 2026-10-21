/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.IsomorphismDerivedPullback
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfCommonStageDirectImage
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.SixFunctors.FrobeniusSquareCartesian
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.FrobeniusGeometricExchange

/-!
# Frobenius transport on ordinary and compactly supported cohomology

Source: Deligne, Weil II (1.1.7), (1.1.10)--(1.1.14), and the Weil blueprint
(blueprint: def-weil-frobenius-cohomology-transport).

Each transport is the recorded point transport followed by the point fibre of the
recorded Frobenius exchange. The compactification is retained over the finite field.
Finite, integral, rational and algebraically closed coefficients use their actual
categories and operations. No operation or comparison map is an arbitrary input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
open FrobeniusExchange

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- The structure morphism of the model, as an arrow over k₀.
Source: blueprint structure-map convention; Deligne, Weil II (1.1.10)
(blueprint: def-weil-frobenius-cohomology-transport). -/
abbrev frobeniusCohomologyModelMap : Y₀ ⟶ sfWeilCohomologyPoint D :=
  Over.homMk Y₀.hom

/-- The base change of the retained compactification, with target Spec k itself.
Source: blueprint compact transport formula; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyCompactification (c₀ : Compactification Y₀.hom) :
    Compactification (D.geometricFiber Y₀).hom where
  Z := (D.geometricFiber
    (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)).left
  i := fiberMap D (zlCompactificationOpen D (frobeniusCohomologyModelMap D Y₀) c₀)
  g := (D.geometricFiber
    (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)).hom
  comm := (Over.w ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
      (zlCompactificationOpen D (frobeniusCohomologyModelMap D Y₀) c₀))).symm
  isOpenImmersion := (geometricCompactification D (frobeniusCohomologyModelMap D Y₀)
    c₀).isOpenImmersion
  isProper := inferInstanceAs (IsProper (pullback.snd (c₀.g ≫ 𝟙 _)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))


/-- The direct recipe for the actual structure square over Spec k.
Source: blueprint ordinary transport formula; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyDirectModel :
    SupportModel (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom :=
  .direct (D.frobenius_square_cartesian Y₀ (sfWeilCohomologyPoint D)
    (frobeniusCohomologyModelMap D Y₀)).2.2.2.2.2.2.2.w

/-- The compact recipe keeps the middle model and its geometric Frobenius.
Source: blueprint compact transport formula; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyCompactModel (c₀ : Compactification Y₀.hom) :
    SupportModel (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom :=
  .compact (frobeniusCohomologyCompactification D Y₀ c₀)
    (galois D (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀))
    (D.frobenius_square_cartesian
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)
      (sfWeilCohomologyPoint D)
      (zlCompactificationProper D (frobeniusCohomologyModelMap D Y₀) c₀)).2.2.2.2.2.2.2.w
    (D.frobenius_square_cartesian Y₀
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)
      (zlCompactificationOpen D (frobeniusCohomologyModelMap D Y₀) c₀)).2.2.2.2.2.1

/-- Ordinary finite-coefficient transport: iota followed by Fib of the ambient mate.
The positive exponent is n+1, which includes every exponent at least one.
Source: blueprint ordinary transport formula; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusOrdinaryTransportFinite (n : ℕ)
    (K : proEtaleDerivedCategory (D.geometricFiber Y₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let F := proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom
    (Padic.coefficientExtensionRing l E (n + 1))
  frobeniusPointTransportFinite D l hl E n (F.obj K) ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u + 2, u + 1}.map
        ((finiteExchange (Padic.coefficientExtensionRing l E (n + 1))
          (D.geometricFiber Y₀).hom (D.geometricFiber Y₀).hom
          (galois D Y₀) (frobeniusPointIso D).hom
          (D.frobenius_square_cartesian Y₀ (sfWeilCohomologyPoint D)
            (frobeniusCohomologyModelMap D Y₀)).2.2.2.2.2.2.2.w).app K)

/-- Compact finite transport, using the specified compactification and the same point map.
The tensor-pullback exchange is expressed in the recorded intrinsic pullback coordinates.
Source: blueprint compact transport formula; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCompactTransportFinite (c₀ : Compactification Y₀.hom) (n : ℕ)
    (K : proEtaleDerivedCategory (D.geometricFiber Y₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let c := frobeniusCohomologyCompactification D Y₀ c₀
  let F := sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))
  let e := finiteCompact l E (n + 1) (Nat.succ_pos n) c
    (galois D Y₀)
    (galois D (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀))
    (frobeniusPointIso D).hom
    (D.frobenius_square_cartesian
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)
      (sfWeilCohomologyPoint D)
      (zlCompactificationProper D (frobeniusCohomologyModelMap D Y₀) c₀)).2.2.2.2.2.2.2.w
    (D.frobenius_square_cartesian Y₀
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)
      (zlCompactificationOpen D (frobeniusCohomologyModelMap D Y₀) c₀)).2.2.2.2.2.1
  frobeniusPointTransportFinite D l hl E n (F.obj K) ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u + 2, u + 1}.map
        ((openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
          (frobeniusPointIso D).hom).inv.app (F.obj K) ≫ e.app K ≫
          F.map ((openSquareDerivedPullbackModel
            (Padic.coefficientExtensionRing l E (n + 1)) (galois D Y₀)).hom.app K))

section IntegralAndRational
variable (R : SupportModel (D.geometricFiber Y₀).hom
  (galois D Y₀) (frobeniusPointIso D).hom)

/-- Integral transport for either retained recipe. The exchange is formed on whole
coefficient systems before the total inverse limit, as in the dependency.
Source: blueprint integral transport formula; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusTransportIntegral
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  let F := modelFunctor l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom R E
  frobeniusPointTransportIntegralConstructible D l hl E (F.obj K) ≫
    (pointIntegralFibre D l hl E).map
      ((modelExchange l D.k (zlClosurePrimeUnit D l hl)
        (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom R E).app K)

/-- Rational transport is point transport followed by the literal localized integral
exchange, with the uniquely normalized rational-pullback object identification.
Source: blueprint rational transport formula; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusTransportRational
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  let F := modelRationalFunctor l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom R E
  let e : (rationalDerivedPullback l E (frobeniusPointIso D).hom).obj (F.obj K) =
      frobeniusPointRationalPullbackObj D l hl E (F.obj K) :=
    (rationalDerivedPullback_existsUnique l E
      (frobeniusPointIso D).hom).exists.choose_spec.2.1 (F.obj K)
  let ex : (rationalDerivedPullback l E (frobeniusPointIso D).hom).obj (F.obj K) ⟶
      F.obj ((rationalDerivedPullback l E (galois D Y₀)).obj K) := by
    simpa only [F, modelRationalSource, modelRationalTarget, Functor.comp_obj] using
      (modelRationalExchange l D.k (zlClosurePrimeUnit D l hl)
      (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom R E).app K
  frobeniusPointTransportRational D l hl E (F.obj K) ≫
    (pointRationalFibre D l hl E).map
      (eqToHom e.symm ≫ ex)

end IntegralAndRational

/-- Both finite transports on the node's bounded constructible domain, at exponent n+1.
Source: blueprint two transport formulas; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyTransportFinite (c₀ : Compactification Y₀.hom) (n : ℕ)
    (K : (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber Y₀).left).FullSubcategory) :=
  (frobeniusOrdinaryTransportFinite D l hl E Y₀ n K.obj,
    frobeniusCompactTransportFinite D l hl E Y₀ c₀ n K.obj)

/-- Both integral transports use the actual completed integral constructible category.
Source: blueprint two transport formulas; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyTransportIntegral (c₀ : Compactification Y₀.hom)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (frobeniusTransportIntegral D l hl E Y₀ (frobeniusCohomologyDirectModel D Y₀) K,
    frobeniusTransportIntegral D l hl E Y₀ (frobeniusCohomologyCompactModel D Y₀ c₀) K)

/-- Both rational transports use raw scalar localization of integral representatives.
Source: blueprint two transport formulas; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyTransportRational (c₀ : Compactification Y₀.hom)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (frobeniusTransportRational D l hl E Y₀ (frobeniusCohomologyDirectModel D Y₀) K,
    frobeniusTransportRational D l hl E Y₀ (frobeniusCohomologyCompactModel D Y₀ c₀) K)

/-- Induced finite-coefficient maps in every cohomological degree.
Source: blueprint final cohomology clause; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyMapFinite (c₀ : Compactification Y₀.hom) (n : ℕ)
    (K : (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber Y₀).left).FullSubcategory) (i : ℤ) :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let H := DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) i
  let τ := frobeniusCohomologyTransportFinite D l hl E Y₀ c₀ n K
  (H.map τ.1, H.map τ.2)

/-- Induced integral maps in all integer degrees, on the recorded complete point target.
Source: blueprint final cohomology clause; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyMapIntegral (c₀ : Compactification Y₀.hom)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) (i : ℤ) :=
  let H := DerivedCategory.coefficientFgCohomology
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}) i
  let τ := frobeniusCohomologyTransportIntegral D l hl E Y₀ c₀ K
  (H.map τ.1, H.map τ.2)

/-- Induced rational maps in all integer degrees.
Source: blueprint final cohomology clause; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyMapRational (c₀ : Compactification Y₀.hom)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) (i : ℤ) :=
  let H := DerivedCategory.coefficientFdCohomology E i
  let τ := frobeniusCohomologyTransportRational D l hl E Y₀ c₀ K
  (H.map τ.1, H.map τ.2)

/-- Exact coefficient transport to an algebraic closure in an independent universe.
The intermediate ULifts put the two fields and module carriers in the common size;
restriction along their ring equivalences preserves the specified scalar action.
Source: blueprint coefficient transport convention; Deligne, Weil II (1.1.10)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyCoefficientExtension {F : Type u} [Field F]
    {Ω : Type v} [Field Ω] (φ : F →+* Ω) :
    @DerivedCategory (ModuleCat.{u} F) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian.{u} _) ⥤
      @DerivedCategory (ModuleCat.{max u v} Ω) _ _ (HasDerivedCategory.standard _) :=
  let ψ : ULift.{v, u} F →+* ULift.{u, v} Ω :=
    (ULift.ringEquiv : ULift.{u, v} Ω ≃+* Ω).symm.toRingHom.comp
      (φ.comp (ULift.ringEquiv : ULift.{v, u} F ≃+* F).toRingHom)
  let G := ModuleCat.extendScalars.{max u v, max u v, max u v} ψ
  letI : G.Additive := (ModuleCat.extendRestrictScalarsAdj ψ).left_adjoint_additive
  letI : PreservesFiniteLimits G :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (letI := ψ.toAlgebra; inferInstanceAs (Module.Flat (ULift.{v, u} F) (ULift.{u, v} Ω)))
  letI : PreservesColimits G :=
    (ModuleCat.extendRestrictScalarsAdj ψ).leftAdjoint_preservesColimits
  letI : HasDerivedCategory.{u} (ModuleCat.{u} F) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  (ModuleCat.uliftFunctor.{v, u} F ⋙
    ModuleCat.restrictScalars.{max u v, max u v, u}
      (ULift.ringEquiv : ULift.{v, u} F ≃+* F).toRingHom ⋙ G ⋙
    ModuleCat.restrictScalars.{max u v, v, max u v}
      (ULift.ringEquiv : ULift.{u, v} Ω ≃+* Ω).symm.toRingHom).mapDerivedCategory

/-- Algebraically closed transport is represented at the object's own finite field.
Realize its rational composite in D(Ω) by canonical exact coefficient transport;
this also works when the scheme and algebraic closure have different universes.
Source: blueprint algebraically closed transport formula; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusTransportQbar (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (R : SupportModel (D.geometricFiber Y₀).hom
      (galois D Y₀) (frobeniusPointIso D).hom)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (frobeniusCohomologyCoefficientExtension.{u, v} (K.stage.val.subtype.comp
    (Shrink.algEquiv ℚ_[l] K.stage.val).toRingHom)).map
      (frobeniusTransportRational D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) Y₀ R K.obj).hom

/-- The ordinary and compactly supported cohomology transports, with all operations
fixed to the geometric Frobenius and the retained model compactification. Finite and
integral versions above use the identical two-arrow recipe; applying the recorded
cohomology functors gives the induced maps in every integer degree.
Source: blueprint two transport composites; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyTransport (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (c₀ : Compactification Y₀.hom)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (frobeniusTransportQbar D l hl Y₀ Ω (frobeniusCohomologyDirectModel D Y₀) K,
    frobeniusTransportQbar D l hl Y₀ Ω (frobeniusCohomologyCompactModel D Y₀ c₀) K)

/-- Induced algebraically closed coefficient maps, after the canonical size transport.
Source: blueprint final cohomology clause; Deligne, Weil II (1.1.14)
(blueprint: def-weil-frobenius-cohomology-transport). -/
def frobeniusCohomologyMap (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (c₀ : Compactification Y₀.hom)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (i : ℤ) :=
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) i
  let τ := frobeniusCohomologyTransport D l hl Y₀ Ω c₀ K
  (H.map τ.1, H.map τ.2)

end WeilConjectures
