/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.AdicPurityRootComparisons
public import Sheaf.Paper.PointReductionUnits
import Sheaf.NumberTheory.FrobeniusRootsOfUnityPower
import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.FrobeniusGeometricExchange
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.InverseImagePullbackComparisonDerived
import Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso
import Sheaf.Paper.PointSectionsScalarExtension

/-! # Geometric Frobenius on the cohomology of a Tate line

Source: Deligne, Weil I (2.2), pp. 280--281; Weil II (1.1.7), (1.2.5)(iv),
(1.2.7); main-20261015, def-weil-frobenius-coefficient-twists, scalar clauses
(blueprint: lem-pur-twist-frobenius-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v w w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ChangeOfRings

namespace WeilConjectures.TwistFrobeniusScalar

/-- The scalar q^(-m), using unit inversion also for integral and quotient coefficients.
Source: Weil I (2.2), geometric Frobenius is inverse arithmetic Frobenius
(blueprint: lem-pur-twist-frobenius-scalar). -/
def scalar (R : Type w) [CommRing R] (q : ℕ) : ℤ → R
  | .ofNat n => Ring.inverse (q : R) ^ n
  | .negSucc n => (q : R) ^ (n + 1)

/-- Compatibility for the specified coefficient comparison: that very map is invertible
and intertwines the two Frobenius operators. Source: blueprint scalar-compatibility clause
(blueprint: lem-pur-twist-frobenius-scalar). -/
def CoefficientCompatibility {R : Type w₁} {S : Type w₂} [CommRing R] [CommRing S]
    (c : R →+* S) (M : ModuleCat.{w₃} R) (N : ModuleCat.{max w₂ w₃} S)
    (f : End M) (g : End N) (e : (ModuleCat.extendScalars c).obj M ⟶ N) : Prop :=
  IsIso e ∧ (ModuleCat.extendScalars c).map f ≫ e = e ≫ g

/-- Reduction on the actual lifted integral coefficient ring.
Source: blueprint A_E,n = O_E / varpi_E^n
(blueprint: lem-pur-twist-frobenius-scalar). -/
def reduction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)) :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
      ULift.ringEquiv.toRingHom)

/-- The integral-to-field map in the recorded cohomology coefficient sizes.
Source: blueprint O_E to E
(blueprint: lem-pur-twist-frobenius-scalar). -/
def localization (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+* E :=
  (Padic.coefficientExtensionIntegers l E).subtype.comp ULift.ringEquiv.toRingHom

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The identity compactification of the finite-field point; only the ordinary component
is used below. Source: blueprint Y₀ = Spec k₀ convention
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev pointCompactification : Compactification (sfWeilCohomologyPoint D).hom :=
  Compactification.ofIsProper (sfWeilCohomologyPoint D).hom

/-- The geometric fibre of Spec k₀, with its canonical identification with Spec k.
Source: blueprint point specialization
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev geometricPoint := (D.geometricFiber (sfWeilCohomologyPoint D)).left

/-- The published finite signed line placed in degree zero. The positive quotient level
is n+1. Source: blueprint finite Tate twist
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev finiteLine (n : ℕ) (m : ℤ) :
    AlgebraicGeometry.Scheme.proEtaleDerivedCategory (geometricPoint D)
      (Padic.coefficientExtensionRing l E (n + 1)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (finiteCoefficientTwist l E (geometricPoint D) n m)

/-- The actual ordinary sections functor for finite coefficients, with the same point
and exchange recipe as the specified transport. Source: blueprint RΓ
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev finiteSections (n : ℕ) :=
  frobeniusCohomologyFiniteFunctor D l E (sfWeilCohomologyPoint D)
    (pointCompactification D) n false

/-- Ordinary H^i of the finite signed line. Source: blueprint cohomology clause
(blueprint: lem-pur-twist-frobenius-scalar). -/
def finiteH (n : ℕ) (m i : ℤ) :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) i).obj
      ((finiteSections D l E n).obj (finiteLine D l E n m))

/-- H^0 of transport followed by the finite canonical Weil structure, rather than an
independently supplied cyclotomic action. Source: blueprint displayed F_m
(blueprint: lem-pur-twist-frobenius-scalar). -/
def finiteF (n : ℕ) (m : ℤ) : End (finiteH D l E n m 0) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) 0).map
      (frobeniusOrdinaryTransportFinite D l hl E (sfWeilCohomologyPoint D) n
          (finiteLine D l E n m) ≫
        (finiteSections D l E n).map
          ((AlgebraicGeometry.Scheme.openSquareDerivedPullbackModel
              (Padic.coefficientExtensionRing l E (n + 1))
              (D.geometricFrobenius (sfWeilCohomologyPoint D)).hom).inv.app
                (finiteLine D l E n m) ≫
            (FrobeniusCoefficientTwists.finiteDerivedLineMap l E
              (D.geometricFrobenius (sfWeilCohomologyPoint D)).hom n m).hom))

/-- The intrinsic complete integral line on the geometric point.
Source: blueprint integral Tate twist
(blueprint: lem-pur-twist-frobenius-scalar). -/
def integralLine (m : ℤ) :=
  letI := sfWeilPrimeInvertible D l hl (sfWeilCohomologyPoint D)
  sfIntegralTwistingCoefficient l E (geometricPoint D) m

/-- The recorded integral ordinary RΓ functor. Source: blueprint RΓ
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev integralSections :=
  frobeniusCohomologyIntegralFunctor D l hl E (sfWeilCohomologyPoint D)
    (pointCompactification D) false

/-- Integral H^i, retaining the coefficient-size lift of the recorded point fibre.
Source: blueprint integral cohomology
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev integralH (m i : ℤ) :=
  (DerivedCategory.coefficientFgCohomology _ _ i).obj
    ((integralSections D l hl E).obj (integralLine D l hl E m))

/-- Integral H^0(F_m), with the canonical completed-to-ordinary pullback comparison.
Source: blueprint displayed F_m
(blueprint: lem-pur-twist-frobenius-scalar). -/
def integralF (m : ℤ) : End (integralH D l hl E m 0) :=
  letI := sfWeilPrimeInvertible D l hl (sfWeilCohomologyPoint D)
  (DerivedCategory.coefficientFgCohomology _ _ 0).map
    (frobeniusTransportIntegral D l hl E (sfWeilCohomologyPoint D)
        (frobeniusCohomologyDirectModel D (sfWeilCohomologyPoint D))
        (integralLine D l hl E m) ≫
      (integralSections D l hl E).map
        (ObjectProperty.homMk
          (FrobeniusCoefficientTwists.integralDerivedLineMap l E
            (D.geometricFrobenius (sfWeilCohomologyPoint D)).hom m).hom))

/-- The rational line with its actual canonical Weil structure.
Source: blueprint rational coefficient line
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev rationalLine (m : ℤ) :=
  FrobeniusCoefficientTwists.rationalWeilLine D l hl (sfWeilCohomologyPoint D) E m

/-- Rational RΓ of that line. Source: blueprint RΓ
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev rationalSections :=
  frobeniusCohomologyRationalFunctor D l hl E (sfWeilCohomologyPoint D)
    (pointCompactification D) false

/-- H^i(s,E(m)). Source: blueprint rational cohomology
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev rationalH (m i : ℤ) :=
  (DerivedCategory.coefficientFdCohomology E i).obj
    ((rationalSections D l hl E).obj (rationalLine D l hl E m).carrier)

/-- The rational transport-then-Weil-structure operator, exactly the ordinary component
of global geometric Frobenius. Source: blueprint F_m and global F
(blueprint: lem-pur-twist-frobenius-scalar). -/
def rationalF (m : ℤ) : End (rationalH D l hl E m 0) :=
  (DerivedCategory.coefficientFdCohomology E 0).map
    ((frobeniusCohomologyTransportRational D l hl E (sfWeilCohomologyPoint D)
      (pointCompactification D) (rationalLine D l hl E m).carrier).1 ≫
      (rationalSections D l hl E).map (rationalLine D l hl E m).str.hom)

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The same Weil line in the actual common-stage category.
Source: blueprint algebraically closed coefficient twist
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev qbarLine (m : ℤ) :=
  FrobeniusCoefficientTwists.commonWeilLine D l hl (sfWeilCohomologyPoint D) Ω m

/-- The recorded ordinary cohomology realization in D(Ω), allowing independent scheme
and coefficient universes. Source: blueprint common-stage RΓ
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev qbarSections :=
  frobeniusCohomologyQbarFunctor D l hl (sfWeilCohomologyPoint D) Ω
    (pointCompactification D) false

/-- H^i(s,Ω(m)) in the recorded standard derived localization.
Source: blueprint algebraically closed cohomology
(blueprint: lem-pur-twist-frobenius-scalar). -/
def qbarH (m i : ℤ) :=
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) i).obj
    ((qbarSections D l hl Ω).obj (qbarLine D l hl Ω m).carrier)

/-- The ordinary common-stage geometric Frobenius is the same transport-then-structure
composite, realized in D(Ω). Source: blueprint displayed F_m
(blueprint: lem-pur-twist-frobenius-scalar). -/
def qbarF (m : ℤ) : End (qbarH D l hl Ω m 0) :=
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) 0).map
    (eqToHom (frobeniusCohomologyQbarSourceEq D l hl (sfWeilCohomologyPoint D) Ω
        (pointCompactification D) false (qbarLine D l hl Ω m).carrier) ≫
      (frobeniusCohomologyTransport D l hl (sfWeilCohomologyPoint D) Ω
        (pointCompactification D) (qbarLine D l hl Ω m).carrier).1 ≫
      eqToHom (frobeniusCohomologyQbarTargetEq D l hl (sfWeilCohomologyPoint D) Ω
        (pointCompactification D) false (qbarLine D l hl Ω m).carrier).symm ≫
      (qbarSections D l hl Ω).map (qbarLine D l hl Ω m).str.hom)

/-- Ordinary scalar extension of the root-defined signed line, in the universal
coefficient-change model. Source: blueprint coefficient-twist scalar extension
(blueprint: lem-pur-twist-frobenius-scalar).
Proof: the two completed coefficient maps agree after every quotient projection.
The balanced map sends s tensor x to s times twistScalarMaps(x). On a root-line
trivializing cover it is multiplication and is invertible. Pure tensors determine
it uniquely; the published twistLineScalarIso has exactly this normalization. -/
theorem scalarSheafLine_existsUnique
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) :
    ∃! e : (completedOrdinaryScalarExtension l E L ι (geometricPoint D)).obj
        (integralTwistLine l E (geometricPoint D) m) ≅
          integralTwistLine l L (geometricPoint D) m,
      ∀ (U : (geometricPoint D).ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L (geometricPoint D)).obj.obj U)
        (x : (integralTwistLine l E (geometricPoint D) m).val.obj U),
        e.hom.val.app U (completedScalarTensorSection l E L ι (geometricPoint D) _ U s x) =
          s • (@id ((integralTwistLine l L (geometricPoint D) m).val.obj U)
            ((@twistScalarMaps l _ E _ _ _ (geometricPoint D)
              (sfWeilPrimeInvertible D l hl (sfWeilCohomologyPoint D))
              L _ _ _ ι m).val.app U x)) := by
  sorry

/-- The uniquely root-normalized universal sheaf scalar comparison.
Source: blueprint scalar-extension clause (blueprint: lem-pur-twist-frobenius-scalar). -/
def scalarSheafLine
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) :=
  (scalarSheafLine_existsUnique D l hl E L ι m).exists.choose

/-- The completed line comparison is pinned by the actual universal counit and
completion map, not by a choice of a basis. Source: blueprint scalar-extension clause
(blueprint: lem-pur-twist-frobenius-scalar).
Proof: the signed line is flat, K-flat in degree zero, and derived complete.
The universal counit computes its ordinary tensor. The preceding normalized
sheaf comparison identifies that tensor with the target line. The completion map
is invertible on this complete object, so its inverse gives e. Its invertibility
and the displayed equation give uniqueness. -/
theorem scalarIntegralLine_existsUnique
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) :
    ∃! e : (integralScalarExtension l E L ι (geometricPoint D)).obj
        (integralLine D l hl E m).obj ≅ (integralLine D l hl L m).obj,
      (completedScalarComparison l E L ι (geometricPoint D)).app
          (integralLine D l hl E m).obj ≫ e.hom =
        completedScalarCounit l E L ι (geometricPoint D)
          ((CochainComplex.singleFunctor _ 0).obj
            (integralTwistLine l E (geometricPoint D) m)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (completedOrdinaryScalarExtension l E L ι (geometricPoint D)) (.up ℤ) 0).hom.app
              (integralTwistLine l E (geometricPoint D) m)) ≫
        (DerivedCategory.singleFunctor _ 0).map (scalarSheafLine D l hl E L ι m).hom := by
  sorry

/-- The canonical completed scalar comparison on signed lines.
Source: blueprint scalar-extension clause (blueprint: lem-pur-twist-frobenius-scalar). -/
def scalarIntegralLine
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) :=
  (scalarIntegralLine_existsUnique D l hl E L ι m).exists.choose

/-- Localization of the prescribed integral line comparison, with the recorded raw
localization object equality. Source: blueprint rational twists and scalar extension
(blueprint: lem-pur-twist-frobenius-scalar). -/
def scalarRationalLine
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) :
    (sfRationalScalarExtension l E (geometricPoint D) 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj (rationalLine D l hl E m).carrier ≅
        (rationalLine D l hl L m).carrier :=
  eqToIso ((sfRationalScalarExtension_existsUnique l E (geometricPoint D) 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
        (rationalLine D l hl E m).carrier) ≪≫
    (sfRationalConstructibleLocalization l L (geometricPoint D)).mapIso
      (ObjectProperty.isoMk _ (scalarIntegralLine D l hl E L ι m))

/-- The actual derived cohomology scalar comparison followed by the root-normalized
line identification. Its first factor is normalized by frobeniusCohomologyIntegralScalar
and pointRationalSectionsScalarExtensionIso through pointRationalFibreScalarIso.
Source: blueprint scalar-extension clause (blueprint: lem-pur-twist-frobenius-scalar). -/
def scalarRationalSections
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) :=
  (frobeniusCohomologyRationalScalar D l hl E (sfWeilCohomologyPoint D)
    (pointCompactification D) false L ι).app (rationalLine D l hl E m).carrier ≪≫
      (rationalSections D l hl L).mapIso (scalarRationalLine D l hl E L ι m)

/-- H⁰ of the actual derived scalar comparison, preceded by the exact tensor/homology
comparison. Source: blueprint H⁰ scalar extension
(blueprint: lem-pur-twist-frobenius-scalar). -/
def scalarRationalH
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) :
    (ModuleCat.extendScalars ι.toRingHom).obj (rationalH D l hl E m 0) ⟶
      rationalH D l hl L m 0 :=
  (DerivedCategory.fieldDerivedHomologyIso ι.toRingHom 0).inv.app
      ((rationalSections D l hl E).obj (rationalLine D l hl E m).carrier).obj ≫
    (DerivedCategory.coefficientFdCohomology L 0).map
      (scalarRationalSections D l hl E L ι m).hom

/-- The unique embedding of the least finite coefficient model into E, over Q_l.
Source: blueprint common finite stage (blueprint: lem-pur-twist-frobenius-scalar).
Proof: the least stage is Q_l itself, presented by Shrink of the bottom intermediate
field. Its inverse base-field equivalence followed by algebraMap into E gives j.
Both composites into Ω are the base-field map. Every element of the least stage
comes from Q_l, proving uniqueness, also for the identity embedding. -/
theorem baseEmbedding_existsUnique (ι : E →ₐ[Padic l] Ω) :
    ∃! j : AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω) →ₐ[Padic l] E,
      ι.toRingHom.comp j.toRingHom =
        frobeniusCohomologyStageEmbedding.{u, v} l Ω (Padic.finiteCoefficientBase l Ω) := by
  sorry

/-- The specified least-stage embedding, uniquely pinned by its composite into Ω.
Source: blueprint common finite stage (blueprint: lem-pur-twist-frobenius-scalar). -/
def baseEmbedding (ι : E →ₐ[Padic l] Ω) :=
  (baseEmbedding_existsUnique l E Ω ι).exists.choose

/-- The canonical Ω comparison through the least finite coefficient stage.
The tower is the published balanced tensor tower; the last equality is exactly
that defining the recorded Qbar functor, whose maps use
frobeniusCohomologyRealizedComparison. No realization map is replaced by a basis choice.
Source: blueprint scalar-extension clause (blueprint: lem-pur-twist-frobenius-scalar). -/
def scalarQbarSections (ι : E →ₐ[Padic l] Ω) (m : ℤ) :=
  (frobeniusCohomologyCoefficientExtension ι.toRingHom).mapIso
      ((DerivedCategory.pointFiniteDimensional E).ι.mapIso
        (scalarRationalSections D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
            (Padic.finiteCoefficientBase l Ω)) E (baseEmbedding l E Ω ι) m).symm) ≪≫
    (frobeniusCoefficientTower (baseEmbedding l E Ω ι).toRingHom ι.toRingHom).app
      ((rationalSections D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
          (Padic.finiteCoefficientBase l Ω))).obj
          (rationalLine D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
              (Padic.finiteCoefficientBase l Ω)) m).carrier).obj ≪≫
    eqToIso (congrArg (fun φ ↦ (frobeniusCohomologyCoefficientExtension φ).obj
      ((rationalSections D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
          (Padic.finiteCoefficientBase l Ω))).obj
            (rationalLine D l hl
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
                (Padic.finiteCoefficientBase l Ω)) m).carrier).obj)
      (baseEmbedding_existsUnique l E Ω ι).exists.choose_spec) ≪≫
    (eqToIso (frobeniusCohomologyQbarSourceEq D l hl (sfWeilCohomologyPoint D) Ω
      (pointCompactification D) false (qbarLine D l hl Ω m).carrier)).symm

/-- The ordinary Ω tensor and the recorded coefficient-size model are identified
by their actual pure tensors. Source: blueprint common coefficient realization
(blueprint: lem-pur-twist-frobenius-scalar).
Proof: lift each factor and use the two inverse coefficient-ring equivalences.
The displayed balanced map has inverse sending up(a) tensor up(x) to a tensor x.
These maps respect scalar balancing and are inverse. Pure tensors generate, giving
naturality and uniqueness without imposing any equality between u and v. -/
theorem coefficientModulesIso_existsUnique (ι : E →ₐ[Padic l] Ω) :
    ∃! e : ModuleCat.extendScalars.{u, v, u} ι.toRingHom ≅
        frobeniusCoefficientModules ι.toRingHom,
      ∀ (M : ModuleCat.{u} E) (a : Ω) (x : M),
        e.hom.app M (a ⊗ₜ[E, ι.toRingHom] x) =
          ULift.up a ⊗ₜ[ULift.{v, u} E, frobeniusCoefficientLiftHom ι.toRingHom] ULift.up x := by
  sorry

/-- Canonical Ω tensor/homology followed by H⁰ of scalarQbarSections.
Source: blueprint H⁰ common-stage scalar extension
(blueprint: lem-pur-twist-frobenius-scalar). -/
def scalarQbarH (ι : E →ₐ[Padic l] Ω) (m : ℤ) :
    (ModuleCat.extendScalars ι.toRingHom).obj (rationalH D l hl E m 0) ⟶
      qbarH D l hl Ω m 0 :=
  letI : HasDerivedCategory.{u} (ModuleCat.{u} E) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  letI : (frobeniusCoefficientModules ι.toRingHom).Additive := by
    dsimp [frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteLimits (frobeniusCoefficientModules ι.toRingHom) := by
    dsimp [frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteColimits (frobeniusCoefficientModules ι.toRingHom) := by
    dsimp [frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  (coefficientModulesIso_existsUnique l E Ω ι).exists.choose.hom.app
      (rationalH D l hl E m 0) ≫
    ((frobeniusCoefficientModules ι.toRingHom).mapDerivedCategoryHomologyFunctorIso 0).hom.app
      ((rationalSections D l hl E).obj (rationalLine D l hl E m).carrier).obj ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) 0).map
      (scalarQbarSections D l hl E Ω ι m).hom

/-- The actual integral direct image on the point, retained as the object representative
of the recorded rational operation. Source: blueprint integral-to-rational passage
(blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev integralPointObject (m : ℤ) :=
  ((frobeniusCohomologyRationalOperation D l hl E (sfWeilCohomologyPoint D)
    (pointCompactification D) false).obj (rationalLine D l hl E m).carrier).obj

/-- The ordinary integral operation and the integral representative of its raw
rational localization have the same derived sections object.
Source: blueprint integral-to-rational passage and unchanged-object rationalization
(blueprint: lem-pur-twist-frobenius-scalar).
Proof: unfold the ordinary recipe (compact = false) in both operations. The integral
operation is directImageFunctor, and modelRationalFunctor is its localizedFunctor.
The latter wraps exactly the same integral object. The rational signed line wraps
sfIntegralTwistingCoefficient, which is integralLine. Finally pointIntegralFibre
only adds its membership proof to pointFibreIntegralAmbient. Erasing these wrappers
and proof fields gives the displayed equality; no direct-image or sections map is
changed. -/
theorem integralPointSections_eq (m : ℤ) :
    ((integralSections D l hl E).obj (integralLine D l hl E m)).obj =
      (pointFibreIntegralAmbient D l E).obj (integralPointObject D l hl E m).obj := by
  sorry

/-- The equality identification of the two unchanged integral representatives.
Source: blueprint raw localization convention
(blueprint: lem-pur-twist-frobenius-scalar). -/
def integralPointSectionsIso (m : ℤ) :=
  eqToIso (integralPointSections_eq D l hl E m)

/-- The two ordinary localization tensor encodings have their prescribed pure tensors.
Source: blueprint integral-to-rational passage
(blueprint: lem-pur-twist-frobenius-scalar).
Proof: send a tensor x to up(a) tensor x. The coefficient-ring equivalences respect
balancing and the inverse removes the lift. These formulas are natural in every
module and inverse on pure tensors, which generate; hence they fix the iso uniquely. -/
theorem localizationTensorIso_existsUnique :
    ∃! e : ModuleCat.extendScalars.{u + 1, u, u + 1} (localization l E) ≅
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E) ⋙
          pointFibreCoefficientDown E,
      ∀ (M : ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) (a : E) (x : M),
        e.hom.app M (a ⊗ₜ[_, localization l E] x) =
          ULift.up a ⊗ₜ[_, pointIntegralToField l E] x := by
  sorry

/-- Canonical localization of H⁰. The middle factors commute exact tensor and
coefficient identification with H⁰. The final factors use the recorded rational
normalization (including its size-descent counit), not an unspecified line isomorphism.
Source: blueprint integral-to-rational passage
(blueprint: lem-pur-twist-frobenius-scalar). -/
def localizationH (m : ℤ) :
    (ModuleCat.extendScalars (localization l E)).obj (integralH D l hl E m 0) ⟶
      (ModuleCat.uliftFunctor.{u + 1, u} E).obj (rationalH D l hl E m 0) :=
  letI : HasDerivedCategory.{u} (ModuleCat.{u} E) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} E) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} E)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (localizationTensorIso_existsUnique l E).exists.choose.hom.app
      (integralH D l hl E m 0) ≫
    (pointFibreCoefficientDown E).map
      ((ModuleCat.extendScalars (pointIntegralToField l E)).map
        ((DerivedCategory.homologyFunctor _ 0).map
          (integralPointSectionsIso D l hl E m).hom)) ≫
    (pointFibreCoefficientDown E).map
      (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategoryHomologyFunctorIso 0).hom.app
          ((pointFibreIntegralAmbient D l E).obj
            (integralPointObject D l hl E m).obj)) ≫
    ((pointFibreCoefficientDown E).mapDerivedCategoryHomologyFunctorIso 0).hom.app
      ((pointFibreRationalAmbient D l E).obj (integralPointObject D l hl E m).obj) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} E) 0).map
      ((pointFibreRationalDownIso D l E).hom.app (integralPointObject D l hl E m).obj ≫
        (pointRationalNormalization D l hl E
          ((frobeniusCohomologyRationalOperation D l hl E (sfWeilCohomologyPoint D)
            (pointCompactification D) false).obj (rationalLine D l hl E m).carrier)).inv) ≫
    ((ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategoryHomologyFunctorIso 0).inv.app
      ((rationalSections D l hl E).obj (rationalLine D l hl E m).carrier).obj

/-- All signed quotient maps, in the recorded restriction-of-scalars category.
Source: blueprint finite reduction (blueprint: lem-pur-twist-frobenius-scalar). -/
abbrev SignedQuotients (n : ℕ) := ∀ m : ℤ,
  integralTwistLine l E (geometricPoint D) m ⟶
    (scalarReductionRestriction l E (geometricPoint D) n).obj
      (finiteCoefficientTwist l E (geometricPoint D) n m)

/-- The existing nonnegative quotient family, extended by its unique dual evaluation
formula. Source: blueprint finite reduction, including negative twists
(blueprint: lem-pur-twist-frobenius-scalar).
Proof: retain adicPurityRootQuotients at every nonnegative exponent. On a root-line
trivializing cover a dual is determined by evaluation on the positive generator.
Reducing that evaluation defines the unique dual map, independently of the local
basis. These maps glue and satisfy the displayed equation on every slice. -/
theorem signedQuotients_existsUnique (n : ℕ) :
    ∃! c : SignedQuotients D l E n,
      (∀ d : ℕ, c (d : ℤ) = adicPurityRootQuotients l E n (geometricPoint D) d) ∧
      ∀ (j : ℕ) (U : (geometricPoint D).ProEtᵒᵖ)
        (φ : (integralTwistLine l E (geometricPoint D) (Int.negSucc j)).val.obj U)
        (x : (integralTwistLine l E (geometricPoint D) ((j + 1 : ℕ) : ℤ)).val.obj U),
        (((c (Int.negSucc j)).val.app U φ).app
          (Opposite.op (Over.mk (𝟙 U.unop))))
            ((c ((j + 1 : ℕ) : ℤ)).val.app U x) =
          (completedIntegralCommRingProjectionUnrestricted l E (geometricPoint D) n).hom.app U
            ((φ.app (Opposite.op (Over.mk (𝟙 U.unop)))) x) := by
  sorry

/-- The specified signed quotient maps, with every evaluation fixed.
Source: blueprint finite reduction (blueprint: lem-pur-twist-frobenius-scalar). -/
def signedQuotients (n : ℕ) := (signedQuotients_existsUnique D l E n).exists.choose

/-- Ordinary reduction is identified with the finite signed line by its balanced map.
Source: blueprint finite reduction (blueprint: lem-pur-twist-frobenius-scalar).
Proof: balance the preceding semilinear map. On a trivializing cover it is the
multiplication isomorphism A tensor O to A, including dual powers. Hence it is an
isomorphism globally. Local pure tensors generate, proving uniqueness. -/
theorem reductionSheafLine_existsUnique (n : ℕ) (m : ℤ) :
    ∃! e : (scalarReductionExtension l E (geometricPoint D) n).obj
        (integralTwistLine l E (geometricPoint D) m) ≅
          finiteCoefficientTwist l E (geometricPoint D) n m,
      ∀ (U : (geometricPoint D).ProEtᵒᵖ)
        (a : (integralCoefficientCommRingSheaf l E (geometricPoint D) n).obj.obj U)
        (x : (integralTwistLine l E (geometricPoint D) m).val.obj U),
        e.hom.val.app U (sfReductionTensor l E (geometricPoint D) n _ U a x) =
          a • (@id ((finiteCoefficientTwist l E (geometricPoint D) n m).val.obj U)
            ((signedQuotients D l E n m).val.app U x)) := by
  sorry

/-- The balanced line reduction with its actual section normalization.
Source: blueprint finite reduction (blueprint: lem-pur-twist-frobenius-scalar). -/
def reductionSheafLine (n : ℕ) (m : ℤ) :=
  (reductionSheafLine_existsUnique D l E n m).exists.choose

/-- Derived line reduction, fixed by the very counit used by sfIntegralReductionTower.
Source: blueprint finite reduction (blueprint: lem-pur-twist-frobenius-scalar).
Proof: the signed integral line is locally free, hence K-flat in degree zero.
The universal derived reduction counit is invertible on its single complex. Follow
it by the single-complex comparison and the balanced line reduction. This gives
the displayed isomorphism, whose hom is specified literally and therefore unique.
The quotient units and all adjacent transitions are those of sfIntegralReductionTower. -/
theorem reductionDerivedLine_existsUnique (n : ℕ) (m : ℤ) :
    ∃! e : (scalarReductionDerivedExtension l E (geometricPoint D) n).obj
        (integralLine D l hl E m).obj ≅ finiteLine D l E n m,
      e.hom =
        (scalarReductionCounit l E (geometricPoint D) n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            ((CochainComplex.singleFunctor _ 0).obj
              (integralTwistLine l E (geometricPoint D) m))) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (scalarReductionExtension l E (geometricPoint D) n) (.up ℤ) 0).hom.app
              (integralTwistLine l E (geometricPoint D) m)) ≫
        (DerivedCategory.singleFunctor _ 0).map (reductionSheafLine D l E n m).hom := by
  sorry

/-- The prescribed K-flat derived line reduction.
Source: blueprint finite reduction (blueprint: lem-pur-twist-frobenius-scalar). -/
def reductionDerivedLine (n : ℕ) (m : ℤ) :=
  (reductionDerivedLine_existsUnique D l hl E n m).exists.choose

/-- The canonical finite reduction of the actual integral direct image: evaluate its
whole-system counit and the canonical direct-image evaluation mate. These are the
quotient projections, rather than an arbitrary map between the same objects.
Source: blueprint cohomology and finite reduction
(blueprint: lem-pur-twist-frobenius-scalar). -/
def reductionOperation (n : ℕ) (m : ℤ) :=
  (((FrobeniusExchange.models l E).system (Spec (.of D.k))).reductionEvaluation n).inv.app
      (integralPointObject D l hl E m).obj ≫
    (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map
      ((FrobeniusExchange.operationReduction l E
        (FrobeniusExchange.systemDirect l E
          (D.geometricFiber (sfWeilCohomologyPoint D)).hom)).app
            (integralLine D l hl E m).obj) ≫
    (FrobeniusExchange.systemDirectEvaluation l E
      (D.geometricFiber (sfWeilCohomologyPoint D)).hom n).app
        ((FrobeniusExchange.reduction l E (geometricPoint D)).obj
          (integralLine D l hl E m).obj) ≫
    (AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage
      (D.geometricFiber (sfWeilCohomologyPoint D)).hom
      (Padic.coefficientExtensionRing l E (n + 1))).map
        ((((FrobeniusExchange.models l E).system (geometricPoint D)).reductionEvaluation n).hom.app
          (integralLine D l hl E m).obj) ≫
    (AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage
      (D.geometricFiber (sfWeilCohomologyPoint D)).hom
      (Padic.coefficientExtensionRing l E (n + 1))).map
        (reductionDerivedLine D l hl E n m).hom

/-- Derive the recorded identity-on-sections restriction comparison in the exact
localizations used by finiteH and integralH. Source: blueprint coefficient-size convention
(blueprint: lem-pur-twist-frobenius-scalar). -/
def reductionRestrictionSections (n : ℕ) :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n).Additive := inferInstance
  letI : PreservesFiniteLimits (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso
    (scalarReductionRestriction l E (Spec (.of D.k)) n)
    (pointIntegralSections l E D.k)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointUnitIntegralSectionsRestrictionIso D l E n) ≪≫
    Functor.mapDerivedCategoryCompIso
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
      (pointUnitIntegralRestriction l E n)

/-- The derived semilinear quotient on actual cohomology, using the reduction unit
of sfIntegralReductionTower and the identity-on-sections restriction comparison.
Source: blueprint H⁰ finite reduction (blueprint: lem-pur-twist-frobenius-scalar). -/
def reductionSections (n : ℕ) (m : ℤ) :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (pointIntegralSections l E D.k).mapDerivedCategory.map
      ((sfDerivedReductionUnit l E (Spec (.of D.k)) n).app
        (integralPointObject D l hl E m).obj) ≫
    (reductionRestrictionSections D l E n).hom.app
      ((scalarReductionDerivedExtension l E (Spec (.of D.k)) n).obj
        (integralPointObject D l hl E m).obj) ≫
    (pointUnitIntegralRestriction l E n).mapDerivedCategory.map
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
          (reductionOperation D l hl E n m))

/-- The canonical balanced H⁰ reduction, obtained by the ordinary tensor/restriction
adjunction from H⁰ of the prescribed derived quotient map. No flatness of the finite
quotient is assumed. Source: blueprint finite-reduction isomorphism
(blueprint: lem-pur-twist-frobenius-scalar). -/
def reductionH (n : ℕ) (m : ℤ) :
    (ModuleCat.extendScalars (reduction l E n)).obj (integralH D l hl E m 0) ⟶
      finiteH D l E n m 0 :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (reduction l E n)).homEquiv _ _).symm
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) 0).map
        ((integralPointSectionsIso D l hl E m).hom ≫ reductionSections D l hl E n m) ≫
      ((pointUnitIntegralRestriction l E n).mapDerivedCategoryHomologyFunctorIso 0).inv.app
        ((finiteSections D l E n).obj (finiteLine D l E n m)))

/-- Geometric Frobenius on the cohomology of every signed Tate line, including
finite reduction, integral localization and field extension.
Source: Weil I (2.2), Weil II (1.1.7), (1.2.5)(iv), (1.2.7), and the scalar
sentences of blueprint def-weil-frobenius-coefficient-twists
(blueprint: lem-pur-twist-frobenius-scalar).

Proof:
1. Choose a compatible primitive l-power root system using
   lem-pur-frobenius-roots-of-unity-power. The Lagrange idempotents split every
   root section into clopen pieces with a unique root label. Thus these roots
   trivialize def-pur-roots-of-unity-sheaf as sheaves, compatibly with the power
   transitions; def-pur-sheaf-inverse-limit gives the integral root generator.
2. The completed coefficient comparison of lem-pur-twist-sheaf-locally-free gives
   the integral and finite first lines. Tensor powers and evaluation give all
   signed lines of def-coefficient-twists-detailed. The constant finite sheaf has
   its coefficient ring as sections: all nonempty labels agree on pairwise
   fibre products. The continuous-coefficient description of
   lem-weil-pbc-continuous-coefficients-immersion-restriction gives the same
   assertion for the completed integral line on the one-point space.
3. The structure map of the geometric point is an isomorphism. Exact sections
   from lem-weil-point-proetale-sections-exact and def-weil-finite-coefficient-point
   therefore put each free line in degree zero. Rationalization tensors its
   integral representative with E; the common-stage fibre then extends to Ω.
4. Expand def-weil-frobenius-cohomology-transport, the mate of
   def-weil-frobenius-square-exchange and def-weil-frobenius-point-transport.
   The identity direct-image unit and counit cancel. The canonical lambda of
   lem-weil-isomorphism-derived-pullback cancels the inverse-image coprojection
   via def-weil-inverse-image-pullback-comparison: x maps to x tensor 1 and back
   to x. At integral coefficients check this at every positive finite quotient.
5. The roots comparison of lem-pur-roots-of-unity-inverse-image-iso introduces no
   additional field automorphism. Restriction sends a root zeta to gamma(zeta).
   By lem-pur-frobenius-roots-of-unity-power, geometric Frobenius is the inverse
   q-power action, hence multiplies the compatible root generator by q inverse.
6. The coefficient factor fixes scalars. The tensor-power structure of
   def-weil-frobenius-coefficient-twists gives q^(-m) for positive m. Its degree
   zero structure fixes 1. For m negative use the dual generator: evaluation on
   the positive generator gives q^(-m). Here q is a unit because l differs from p.
7. The canonical finite reduction sends each tensor generator to its reduction,
   and a dual generator to the unique functional evaluating to 1. Consequently
   the balanced map on sections is a line isomorphism even without flatness of
   the finite quotient. It intertwines q^(-m) on each pure tensor.
8. Rationalization and lem-weil-point-sections-scalar-extension give the integral
   localization and finite-field-extension isomorphisms. The same roots generate
   after extension, so the scalar has the same image under each coefficient map.
   Identity and tower compatibility make the common-stage Ω comparison independent
   of stage. The comparisons named in the conclusion are these actual balanced
   maps: their formulas on root tensors and dual evaluations show invertibility.
   Their linearity and the common scalar give the asserted intertwining equations.
9. The rational operator is exactly the ordinary component of
   def-weil-global-geometric-frobenius, the same transport-then-structure composite;
   the Ω operator is its common-stage realization. Specialize to m = 1 and
   m = -d to obtain q inverse and q^d, also for d = 0. -/
theorem twist_frobenius_scalar (m : ℤ) :
    (∀ n : ℕ,
      (∀ i : ℤ, i ≠ 0 → Subsingleton (finiteH D l E n m i)) ∧
      Nonempty (finiteH D l E n m 0 ≃ₗ[
        ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))]
          ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) ∧
      ∀ x : finiteH D l E n m 0, (finiteF D l hl E n m).hom x =
        scalar (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) D.q m • x) ∧
    ((∀ i : ℤ, i ≠ 0 → Subsingleton (integralH D l hl E m i)) ∧
      Nonempty (integralH D l hl E m 0 ≃ₗ[
        ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)]
          ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) ∧
      ∀ x : integralH D l hl E m 0, (integralF D l hl E m).hom x =
        scalar (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) D.q m • x) ∧
    ((∀ i : ℤ, i ≠ 0 → Subsingleton (rationalH D l hl E m i)) ∧
      Nonempty (rationalH D l hl E m 0 ≃ₗ[E] E) ∧
      ∀ x : rationalH D l hl E m 0,
        (rationalF D l hl E m).hom x = scalar E D.q m • x) ∧
    ((∀ i : ℤ, i ≠ 0 → Subsingleton (qbarH D l hl Ω m i)) ∧
      Nonempty (qbarH D l hl Ω m 0 ≃ₗ[Ω] Ω) ∧
      ∀ x : qbarH D l hl Ω m 0,
        (qbarF D l hl Ω m).hom x = scalar Ω D.q m • x) ∧
    (∀ n : ℕ, CoefficientCompatibility (reduction l E n)
      (integralH D l hl E m 0) (finiteH D l E n m 0)
      (integralF D l hl E m) (finiteF D l hl E n m)
      (reductionH D l hl E n m)) ∧
    CoefficientCompatibility (localization l E)
      (integralH D l hl E m 0)
      ((ModuleCat.uliftFunctor.{u + 1, u} E).obj (rationalH D l hl E m 0))
      (integralF D l hl E m)
      ((ModuleCat.uliftFunctor.{u + 1, u} E).map (rationalF D l hl E m))
      (localizationH D l hl E m) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
      (ι : E →ₐ[Padic l] L), CoefficientCompatibility ι.toRingHom
        (rationalH D l hl E m 0) (rationalH D l hl L m 0)
        (rationalF D l hl E m) (rationalF D l hl L m)
        (scalarRationalH D l hl E L ι m)) ∧
    (∀ ι : E →ₐ[Padic l] Ω, CoefficientCompatibility ι.toRingHom
      (rationalH D l hl E m 0) (qbarH D l hl Ω m 0)
      (rationalF D l hl E m) (qbarF D l hl Ω m)
      (scalarQbarH D l hl E Ω ι m)) := by
  sorry

end WeilConjectures.TwistFrobeniusScalar
