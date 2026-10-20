/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ProperCompactCoincidence
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.FrobeniusGeometricExchange

/-! # Proper coincidence and Frobenius

Source: main-20261015, prop-cohomological-finiteness, Proof Step 6;
Deligne, Weil I (1.3), p. 274 (blueprint: lem-pod-proper-coincidence-frobenius).

The comparison is constructed from identity open extension, before applying
point fibres or cohomology. All exchanges and transports are the recorded maps.

## Main declarations

* `properFrobeniusFiniteComparison`, `properFrobeniusIntegralIso`,
  `properFrobeniusRationalIso`, `properFrobeniusQbarComparison`: the canonical
  identity-compactification comparisons, before taking cohomology.
* `properCoincidenceFrobeniusFinite`, `properCoincidenceFrobeniusIntegral`,
  `properCoincidenceFrobeniusRational`, `properCoincidenceFrobenius`: the exchange
  square, its point-complex square, and the equality in every integer degree.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures
open FrobeniusExchange

-- The published overlay marks these recipe wrappers irreducible. Expose only
-- their existing definitions while elaborating the canonical comparisons.
set_option allowUnsafeReducibility true in
attribute [local reducible] FrobeniusExchange.modelFunctor
  FrobeniusExchange.modelRationalSource FrobeniusExchange.modelRationalTarget

variable (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀)))
  [IsProper Y₀.hom]

/-! The recorded transport APIs expect the geometric fibre as an object over
the base point, together with the finiteness and prime-to-characteristic
instances that are implicit in their definitions.  These are canonical
instances supplied by the finite-field datum and the proper base change. -/
/-- The geometric fibre has its recorded structure morphism over Spec k.
Source: blueprint proper-case base change
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusFiberOver :
    (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
  ⟨(D.geometricFiber Y₀).hom⟩

/-- The geometric point is over itself by the identity.
Source: blueprint proper-case base change
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusBaseOver :
    (Spec (.of D.k)).Over (Spec (.of D.k)) :=
  ⟨𝟙 _⟩

/-- The geometric structure morphism is over the geometric point.
Source: blueprint proper-case base change
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusFiberHomOver :
    (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) :=
  ⟨Category.comp_id _⟩

/-- The proper geometric structure morphism is separated.
Source: blueprint proper-case base change
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusFiberSeparated :
    IsSeparated (D.geometricFiber Y₀).hom :=
  inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The geometric fibre is locally of finite type by proper base change.
Source: blueprint proper-case base change
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusFiberLocallyFiniteType :
    LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
  (fiber_finiteType D Y₀).1

/-- The geometric fibre is quasi-compact by proper base change.
Source: blueprint proper-case base change
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusFiberQuasiCompact :
    QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
  (fiber_finiteType D Y₀).2

/-- The base-changed structure map remains proper.
Source: blueprint proper-case base change
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusFiberProper : IsProper (D.geometricFiber Y₀).hom :=
  inferInstanceAs (IsProper (pullback.snd Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The retained identity compactification base changes to the identity compactification.
Source: blueprint proper-case identity compactification
(blueprint: lem-pod-proper-coincidence-frobenius).
Proof: unfold the retained middle model and its two arrows. Cancel composition
with the identity structure map. Functoriality of geometric base change sends
the identity open arrow to the identity; proof irrelevance identifies the records. -/
theorem properFrobeniusCompactification_eq :
    frobeniusCohomologyCompactification D Y₀ (Compactification.ofIsProper Y₀.hom) =
      Compactification.ofIsProper (D.geometricFiber Y₀).hom := by
  sorry

/-- Canonical finite comparison: change the equal compactification record, then
apply the adjunction-normalized identity-open isomorphism and the left unitor.
Source: blueprint proper-case Step 1
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusFiniteComparison (A : Type u) [CommRing A] [Finite A] :
    sfIntrinsicCompactSupport
        (frobeniusCohomologyCompactification D Y₀ (Compactification.ofIsProper Y₀.hom)) A ≅
      proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom A :=
  eqToIso (congrArg (fun c ↦ sfIntrinsicCompactSupport c A)
      (properFrobeniusCompactification_eq D Y₀)) ≪≫
    isoWhiskerRight (sfIntrinsicDerivedOpenId A (D.geometricFiber Y₀).left)
      (proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom A) ≪≫
    Functor.leftUnitor _

variable (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Identity open extension on entire derived coefficient systems, fixed by the
ordinary system adjunction and the section-normalized identity pullback.
Source: blueprint proper-case Step 2
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusSystemOpenId (X : Scheme.{u}) :
    systemDerivedOpen l E (𝟙 X) ≅ 𝟭 _ :=
  ((systemDerivedOpenAdjunction l E (𝟙 X)).ofNatIsoRight
    (integralComparisonSystemUnit l E X)).leftAdjointUniq Adjunction.id

/-- The geometric point residue units inherited from the finite-field datum.
Source: blueprint prime-to-characteristic convention
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusPointPrime :
    ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
  frobeniusPointPrimeInvertible D l Fact.out

/-- The geometric fibre residue units inherited from the finite-field datum.
Source: blueprint prime-to-characteristic convention
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusFiberPrime :
    ∀ x : (D.geometricFiber Y₀).left,
      Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
  sfWeilPrimeInvertible D l Fact.out Y₀

/-- Canonical integral comparison on ambient completed-module derived categories.
It first uses the recorded projection-normalized compact realization, then
cancels identity open extension on whole systems, and applies the total limit.
Source: blueprint proper-case Step 2
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusIntegralAmbient :
    sfCompactSupportFiniteIntegralFunctor l D.k (zlClosurePrimeUnit D l Fact.out)
        (frobeniusCohomologyCompactification D Y₀ (Compactification.ofIsProper Y₀.hom)) E ⋙
        (sfIntegralConstructible l E (Spec (.of D.k))).ι ≅
      (sfIntegralConstructible l E (D.geometricFiber Y₀).left).ι ⋙
        integralDirectImage l E (D.geometricFiber Y₀).hom :=
  compactRealization l E D.k (zlClosurePrimeUnit D l Fact.out) (D.geometricFiber Y₀).hom _ ≪≫
    isoWhiskerLeft (sfIntegralConstructible l E (D.geometricFiber Y₀).left).ι
      (eqToIso (congrArg (fun c ↦ compactImage l E (D.geometricFiber Y₀).hom c)
          (properFrobeniusCompactification_eq D Y₀)) ≪≫
        isoWhiskerRight
          (isoWhiskerLeft (reduction l E (D.geometricFiber Y₀).left)
            (isoWhiskerRight (properFrobeniusSystemOpenId l E (D.geometricFiber Y₀).left)
              (systemDirect l E (D.geometricFiber Y₀).hom) ≪≫ Functor.leftUnitor _))
          (coefficientSequenceLimit l E (Spec (.of D.k))))

/-- The same canonical comparison in the full constructible subcategory.
Source: blueprint proper-case Step 2
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusIntegralComparison
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (modelFunctor l D.k (zlClosurePrimeUnit D l Fact.out) (D.geometricFiber Y₀).hom
      (galois D Y₀) (frobeniusPointIso D).hom
      (frobeniusCohomologyCompactModel D Y₀ (Compactification.ofIsProper Y₀.hom)) E).obj K ≅
    (modelFunctor l D.k (zlClosurePrimeUnit D l Fact.out) (D.geometricFiber Y₀).hom
      (galois D Y₀) (frobeniusPointIso D).hom
      (frobeniusCohomologyDirectModel D Y₀) E).obj K :=
  ObjectProperty.isoMk _ ((properFrobeniusIntegralAmbient D Y₀ l E).app K)


/-- The geometric Frobenius is the recorded scheme isomorphism.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusGaloisIso : IsIso (galois D Y₀) :=
  inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)

/-- The recorded integral operation at the fixed identity compactification.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusIntegralFunctor (compact : Bool) :
    sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left ⥤
      sfIntegralConstructibleCategory l E (Spec (.of D.k)) :=
  modelFunctor l D.k (zlClosurePrimeUnit D l Fact.out) (D.geometricFiber Y₀).hom
      (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then
        frobeniusCohomologyCompactModel D Y₀ (Compactification.ofIsProper Y₀.hom)
      else frobeniusCohomologyDirectModel D Y₀) E

/-- The recorded integral exchange for that same operation.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusIntegralExchange (compact : Bool) :=
  modelExchange l D.k (zlClosurePrimeUnit D l Fact.out) (D.geometricFiber Y₀).hom
      (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then
        frobeniusCohomologyCompactModel D Y₀ (Compactification.ofIsProper Y₀.hom)
      else frobeniusCohomologyDirectModel D Y₀) E

/-- The recorded rational operation at the fixed identity compactification.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusRationalFunctor (compact : Bool) :
    sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left ⥤
      sfRationalConstructibleCategory l E (Spec (.of D.k)) :=
  modelRationalFunctor l D.k (zlClosurePrimeUnit D l Fact.out) (D.geometricFiber Y₀).hom
      (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then
        frobeniusCohomologyCompactModel D Y₀ (Compactification.ofIsProper Y₀.hom)
      else frobeniusCohomologyDirectModel D Y₀) E

/-- The recorded rational exchange for that same operation.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusRationalExchange (compact : Bool) :=
  modelRationalExchange l D.k (zlClosurePrimeUnit D l Fact.out) (D.geometricFiber Y₀).hom
      (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then
        frobeniusCohomologyCompactModel D Y₀ (Compactification.ofIsProper Y₀.hom)
      else frobeniusCohomologyDirectModel D Y₀) E

/-- The canonical integral comparison is natural on every constructible morphism.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusIntegralIso :
    properFrobeniusIntegralFunctor D Y₀ l E true ≅
      properFrobeniusIntegralFunctor D Y₀ l E false :=
  NatIso.ofComponents (properFrobeniusIntegralComparison D Y₀ l E)
    (fun a ↦ ObjectProperty.hom_ext _
      ((properFrobeniusIntegralAmbient D Y₀ l E).hom.naturality a))

/-- Localization determines a unique natural comparison from its integral components.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius).
Proof: Localize the constructed integral comparison and its inverse. Naturality
holds on pure tensor maps by integral naturality and then on every tensor by
additivity. The component formula determines the natural isomorphism uniquely. -/
theorem properFrobeniusRationalIso_existsUnique :
    ∃! κ : properFrobeniusRationalFunctor D Y₀ l E true ≅
        properFrobeniusRationalFunctor D Y₀ l E false,
      ∀ K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left,
        HEq (κ.hom.app K)
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).map
            ((properFrobeniusIntegralIso D Y₀ l E).hom.app K.obj)) := by
  sorry

/-- The canonical rational comparison, fixed by localization of integral maps.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusRationalIso :=
  (properFrobeniusRationalIso_existsUnique D Y₀ l E).exists.choose

/-- Every positive coefficient quotient is finite.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
instance properFrobeniusFiniteRingFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

/-- Exact finite point fibre in the precise size used by the recorded transports.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusFiniteFibre (A : Type u) [CommRing A] :=
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (pointFiniteSections D.k A).mapDerivedCategory.{u + 2, u + 1}

/-- Finite-coefficient cohomology in the size used by the recorded induced maps.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusFiniteHomology (A : Type u) [CommRing A] (i : ℤ) :=
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i

/-- The finite compact exchange in the recorded intrinsic inverse-image coordinates.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusFiniteExchange (n : ℕ)
    (K : proEtaleDerivedCategory (D.geometricFiber Y₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let c₀ := Compactification.ofIsProper Y₀.hom
  let c := frobeniusCohomologyCompactification D Y₀ c₀
  let F := sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))
  (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
      (frobeniusPointIso D).hom).inv.app (F.obj K) ≫
    (finiteCompact l E (n + 1) (Nat.succ_pos n) c (galois D Y₀)
      (galois D (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀))
      (frobeniusPointIso D).hom
      (D.frobenius_square_cartesian
        (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)
        (sfWeilCohomologyPoint D)
        (zlCompactificationProper D (frobeniusCohomologyModelMap D Y₀) c₀)).2.2.2.2.2.2.2.w
      (D.frobenius_square_cartesian Y₀
        (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)
        (zlCompactificationOpen D (frobeniusCohomologyModelMap D Y₀) c₀)).2.2.2.2.2.1).app K ≫
    F.map ((openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
      (galois D Y₀)).hom.app K)

/-- Finite comparison at exponent n+1, with every positive exponent included.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusFiniteIso (n : ℕ) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  properFrobeniusFiniteComparison D Y₀ (Padic.coefficientExtensionRing l E (n + 1))

/-- Finite comparison on point complexes, obtained by applying the point fibre.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusFinitePointIso (n : ℕ)
    (K : proEtaleDerivedCategory (D.geometricFiber Y₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  (properFrobeniusFiniteFibre D (Padic.coefficientExtensionRing l E (n + 1))).mapIso
    ((properFrobeniusFiniteIso D Y₀ l E n).app K)

/-- The pulled finite comparison uses Lg_Y^*M, without identifying it with M.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusFinitePulledPointIso (n : ℕ)
    (K : proEtaleDerivedCategory (D.geometricFiber Y₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  properFrobeniusFinitePointIso D Y₀ l E n
    ((sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
      (galois D Y₀)).obj K)

/-- Both compatibility clauses and the induced equality in every degree, for A_{E,n+1}.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius).
Proof: Use the identity compactification. Identity open extension has its
adjunction-normalized identity comparison, so its open-square exchange is
the identity under these comparisons (lem-trf-open-square-exchange). The two
proper mates coincide, proving the exchange square. Naturality of point
transport (lem-weil-frobenius-point-transport-natural), followed by functoriality
of the point fibre, gives the complex square. Apply cohomology in degree i. -/
theorem properCoincidenceFrobeniusFinite (n : ℕ)
    (K : (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber Y₀).left).FullSubcategory) :
    (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
        (frobeniusPointIso D).hom).map ((properFrobeniusFiniteIso D Y₀ l E n).hom.app K.obj) ≫
      (finiteExchange (Padic.coefficientExtensionRing l E (n + 1))
        (D.geometricFiber Y₀).hom (D.geometricFiber Y₀).hom
        (galois D Y₀) (frobeniusPointIso D).hom
        (D.frobenius_square_cartesian Y₀ (sfWeilCohomologyPoint D)
          (frobeniusCohomologyModelMap D Y₀)).2.2.2.2.2.2.2.w).app K.obj =
      properFrobeniusFiniteExchange D Y₀ l E n K.obj ≫
        (properFrobeniusFiniteIso D Y₀ l E n).hom.app
          ((sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) (galois D
            Y₀)).obj K.obj) ∧
    (properFrobeniusFinitePointIso D Y₀ l E n K.obj).hom ≫ (frobeniusCohomologyTransportFinite D l
      Fact.out E Y₀
        (Compactification.ofIsProper Y₀.hom) n K).1 =
      (frobeniusCohomologyTransportFinite D l Fact.out E Y₀
        (Compactification.ofIsProper Y₀.hom) n K).2 ≫ (properFrobeniusFinitePulledPointIso D Y₀ l E
          n K.obj).hom ∧
    ∀ i : ℤ,
      (properFrobeniusFiniteHomology (Padic.coefficientExtensionRing l E (n + 1)) i).map
        (properFrobeniusFinitePointIso D Y₀ l E n K.obj).hom ≫
          (frobeniusCohomologyMapFinite D l Fact.out E Y₀
          (Compactification.ofIsProper Y₀.hom) n K i).1 =
        (frobeniusCohomologyMapFinite D l Fact.out E Y₀
          (Compactification.ofIsProper Y₀.hom) n K i).2 ≫
          (properFrobeniusFiniteHomology (Padic.coefficientExtensionRing l E (n + 1)) i).map
            (properFrobeniusFinitePulledPointIso D Y₀ l E n K.obj).hom := by
  sorry

/-- The canonical integral comparison after the recorded point fibre.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusIntegralPointIso
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (pointIntegralFibre D l Fact.out E).mapIso
    ((properFrobeniusIntegralIso D Y₀ l E).app K)

/-- The same integral point comparison at the pulled input.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusIntegralPulledPointIso
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  properFrobeniusIntegralPointIso D Y₀ l E
    ((@constructibleIntegralPullback l _ E _ _ _
      (D.geometricFiber Y₀).left (D.geometricFiber Y₀).left (galois D Y₀)
      (properFrobeniusFiberPrime D Y₀ l) (properFrobeniusFiberPrime D Y₀ l)).obj K)

/-- The recorded integral cohomology functor.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusIntegralHomology (i : ℤ) :=
  DerivedCategory.coefficientFgCohomology
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}) i

/-- Both compatibility clauses and their degreewise consequence, for integral coefficients.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius).
Proof: Use the identity compactification at every coefficient index. The
restriction-of-scalars comparison becomes the ordinary direct-image comparison
because identity open extension has identity unit and counit. Thus the two
strict systems, including quotient transitions, agree under the constructed
comparison. The open-adjunction mate on simultaneous section representatives
is the identity system map. The integral exchange composites have the same
alpha and beta normalizations and the same whole-system map before total limit;
this proves the exchange square, without arguing from bare finite evaluations.
Naturality of point transport (lem-weil-frobenius-point-transport-natural),
followed by functoriality of the point fibre, gives the complex square.
Apply cohomology in every integer degree. -/
theorem properCoincidenceFrobeniusIntegral
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (constructibleIntegralPullback l E (frobeniusPointIso D).hom).map ((properFrobeniusIntegralIso D
      Y₀ l E).hom.app K) ≫
        (properFrobeniusIntegralExchange D Y₀ l E false).app K =
      (properFrobeniusIntegralExchange D Y₀ l E true).app K ≫
        (properFrobeniusIntegralIso D Y₀ l E).hom.app ((@constructibleIntegralPullback l _ E _ _ _
          (D.geometricFiber Y₀).left (D.geometricFiber Y₀).left (galois D Y₀)
          (properFrobeniusFiberPrime D Y₀ l) (properFrobeniusFiberPrime D Y₀ l)).obj K) ∧
    (properFrobeniusIntegralPointIso D Y₀ l E K).hom ≫ (frobeniusCohomologyTransportIntegral D l
      Fact.out E Y₀
        (Compactification.ofIsProper Y₀.hom) K).1 =
      (frobeniusCohomologyTransportIntegral D l Fact.out E Y₀
        (Compactification.ofIsProper Y₀.hom) K).2 ≫ (properFrobeniusIntegralPulledPointIso D Y₀ l E
          K).hom ∧
    ∀ i : ℤ,
      (properFrobeniusIntegralHomology l E i).map (properFrobeniusIntegralPointIso D Y₀ l E K).hom ≫
        (frobeniusCohomologyMapIntegral D l Fact.out E Y₀
          (Compactification.ofIsProper Y₀.hom) K i).1 =
        (frobeniusCohomologyMapIntegral D l Fact.out E Y₀
          (Compactification.ofIsProper Y₀.hom) K i).2 ≫ (properFrobeniusIntegralHomology l E i).map
            (properFrobeniusIntegralPulledPointIso D Y₀ l E K).hom := by
  sorry

/-- The canonical rational comparison after the recorded point fibre.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusRationalPointIso
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (pointRationalFibre D l Fact.out E).mapIso
    ((properFrobeniusRationalIso D Y₀ l E).app K)

/-- The same rational point comparison at the pulled input.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusRationalPulledPointIso
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  properFrobeniusRationalPointIso D Y₀ l E
    ((@rationalDerivedPullback l _ E _ _ _
      (D.geometricFiber Y₀).left (D.geometricFiber Y₀).left (galois D Y₀)
      (properFrobeniusFiberPrime D Y₀ l) (properFrobeniusFiberPrime D Y₀ l)).obj K)

/-- The recorded rational cohomology functor.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusRationalHomology (i : ℤ) :=
  DerivedCategory.coefficientFdCohomology E i

/-- Both compatibility clauses and their degreewise consequence, for rational coefficients.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius).
Proof: The integral exchange equality holds on whole systems before the
total inverse limit: cancel identity system open extension. Scalar localization
preserves this equality and its specified comparisons. Naturality of point
transport then gives the complex equality; apply degreewise cohomology. -/
theorem properCoincidenceFrobeniusRational
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (rationalDerivedPullback l E (frobeniusPointIso D).hom).map ((properFrobeniusRationalIso D Y₀ l
      E).hom.app K) ≫
        (properFrobeniusRationalExchange D Y₀ l E false).app K =
      (properFrobeniusRationalExchange D Y₀ l E true).app K ≫
        (properFrobeniusRationalIso D Y₀ l E).hom.app ((@rationalDerivedPullback l _ E _ _ _
          (D.geometricFiber Y₀).left (D.geometricFiber Y₀).left (galois D Y₀)
          (properFrobeniusFiberPrime D Y₀ l) (properFrobeniusFiberPrime D Y₀ l)).obj K) ∧
    (properFrobeniusRationalPointIso D Y₀ l E K).hom ≫ (frobeniusCohomologyTransportRational D l
      Fact.out E Y₀
        (Compactification.ofIsProper Y₀.hom) K).1 =
      (frobeniusCohomologyTransportRational D l Fact.out E Y₀
        (Compactification.ofIsProper Y₀.hom) K).2 ≫ (properFrobeniusRationalPulledPointIso D Y₀ l E
          K).hom ∧
    ∀ i : ℤ,
      (properFrobeniusRationalHomology E i).map (properFrobeniusRationalPointIso D Y₀ l E K).hom ≫
        (frobeniusCohomologyMapRational D l Fact.out E Y₀
          (Compactification.ofIsProper Y₀.hom) K i).1 =
        (frobeniusCohomologyMapRational D l Fact.out E Y₀
          (Compactification.ofIsProper Y₀.hom) K i).2 ≫ (properFrobeniusRationalHomology E i).map
            (properFrobeniusRationalPulledPointIso D Y₀ l E K).hom := by
  sorry


variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Source or target of the recorded common-stage exchange, with its coefficient action.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusQbarSide (compact target : Bool) :=
  (stageAction l D.k (zlClosurePrimeUnit D l Fact.out) (D.geometricFiber Y₀).hom
    (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then
      frobeniusCohomologyCompactModel D Y₀ (Compactification.ofIsProper Y₀.hom)
    else frobeniusCohomologyDirectModel D Y₀) Ω target).functor

/-- The recorded common-stage exchange at the identity compactification.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusQbarExchange (compact : Bool) :=
  commonStageExchange l D.k (zlClosurePrimeUnit D l Fact.out) (D.geometricFiber Y₀).hom
    (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then
      frobeniusCohomologyCompactModel D Y₀ (Compactification.ofIsProper Y₀.hom)
    else frobeniusCohomologyDirectModel D Y₀) Ω

/-- The canonical proper comparison on a common-stage object, before either pullback.
It is the same-stage class of the localized identity-open cancellation, including
its specified inverse. Thus the coefficient stage is retained, and no arbitrary
isomorphism is selected.
Source: main-20261015, prop-cohomological-finiteness, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusQbarComparison
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
    (Spec (.of D.k))).ι K.stage).mapIso
      ((properFrobeniusRationalIso D Y₀ l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)).app K.obj)

/-- The source comparison is uniquely fixed by its canonical finite-stage class.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius).
Proof: The integral comparison is the identity-open cancellation on whole systems.
It commutes with coefficient extension because the scalar adjunction mates
and the normalized total-limit comparisons preserve the same units. Localize
and descend the resulting natural isomorphism by the recorded stage system.
The common-stage pullback formulas identify its components with the displayed
canonical pullback of the constructed comparison. This fixes every component,
so natural-isomorphism extensionality proves uniqueness. -/
theorem properFrobeniusQbarSourceIso_existsUnique :
    ∃! κ : properFrobeniusQbarSide D Y₀ l Ω true false ≅
        properFrobeniusQbarSide D Y₀ l Ω false false,
      ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left,
        HEq (κ.hom.app K)
          ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).map
            (properFrobeniusQbarComparison D Y₀ l Ω K).hom) := by
  sorry

/-- The canonical common-stage source comparison, with specified representative.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusQbarSourceIso :=
  (properFrobeniusQbarSourceIso_existsUnique D Y₀ l Ω).exists.choose

/-- The target comparison is uniquely fixed by its canonical finite-stage class.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius).
Proof: The integral comparison is the identity-open cancellation on whole systems.
It commutes with coefficient extension because the scalar adjunction mates
and the normalized total-limit comparisons preserve the same units. Localize
and descend the resulting natural isomorphism by the recorded stage system.
The common-stage pullback object formula identifies its components with the
constructed comparison at the pulled input. This fixes every component, so
natural-isomorphism extensionality proves uniqueness. -/
theorem properFrobeniusQbarTargetIso_existsUnique :
    ∃! κ : properFrobeniusQbarSide D Y₀ l Ω true true ≅
        properFrobeniusQbarSide D Y₀ l Ω false true,
      ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left,
        HEq (κ.hom.app K)
          (properFrobeniusQbarComparison D Y₀ l Ω
            ((@commonStageDerivedPullback l _ Ω _ _ _
              (D.geometricFiber Y₀).left (D.geometricFiber Y₀).left (galois D Y₀)
              (properFrobeniusFiberPrime D Y₀ l)
              (properFrobeniusFiberPrime D Y₀ l)).obj K)).hom := by
  sorry

/-- The canonical common-stage target comparison, with specified representative.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusQbarTargetIso :=
  (properFrobeniusQbarTargetIso_existsUnique D Y₀ l Ω).exists.choose

/-- The Qbar point comparison is exact coefficient transport of the rational one.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusQbarPointIso
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (frobeniusCohomologyCoefficientExtension.{u, v} (K.stage.val.subtype.comp
    (Shrink.algEquiv ℚ_[l] K.stage.val).toRingHom)).mapIso
      (((DerivedCategory.pointFiniteDimensional
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)).ι).mapIso
        (properFrobeniusRationalPointIso D Y₀ l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) K.obj))

/-- The Qbar target point comparison uses the pulled input at the same coefficient stage.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusQbarPulledPointIso
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (frobeniusCohomologyCoefficientExtension.{u, v} (K.stage.val.subtype.comp
    (Shrink.algEquiv ℚ_[l] K.stage.val).toRingHom)).mapIso
      (((DerivedCategory.pointFiniteDimensional
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)).ι).mapIso
        (properFrobeniusRationalPulledPointIso D Y₀ l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) K.obj))

/-- Cohomology after exact coefficient transport to the independent closure universe.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius). -/
def properFrobeniusQbarHomology (i : ℤ) :=
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) i

/-- Both compatibility clauses and their degreewise consequence for Qbar coefficients.
Source: main-20261015, proper-case Step 6
(blueprint: lem-pod-proper-coincidence-frobenius).
Proof: Represent the object and maps at their common finite coefficient field.
Identity open extension cancels before the total inverse limit; the integral
exchange square therefore holds for the specified whole-system maps. Its
rational localization descends to the common-stage exchange square, with the
source and target comparisons specified above. Naturality of point transport
gives the complex equality; exact extension to the algebraic closure preserves
it. Functoriality of cohomology gives the equality in every integer degree. -/
theorem properCoincidenceFrobenius
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :
    (properFrobeniusQbarSourceIso D Y₀ l Ω).hom.app K ≫
        (properFrobeniusQbarExchange D Y₀ l Ω false).app K =
      (properFrobeniusQbarExchange D Y₀ l Ω true).app K ≫
        (properFrobeniusQbarTargetIso D Y₀ l Ω).hom.app K ∧
    (properFrobeniusQbarPointIso D Y₀ l Ω K).hom ≫ (frobeniusCohomologyTransport D l Fact.out Y₀ Ω
        (Compactification.ofIsProper Y₀.hom) K).1 =
      (frobeniusCohomologyTransport D l Fact.out Y₀ Ω
        (Compactification.ofIsProper Y₀.hom) K).2 ≫ (properFrobeniusQbarPulledPointIso D Y₀ l Ω
          K).hom ∧
    ∀ i : ℤ,
      (properFrobeniusQbarHomology.{u, v} Ω i).map (properFrobeniusQbarPointIso D Y₀ l Ω K).hom ≫
        (frobeniusCohomologyMap D l Fact.out Y₀ Ω
          (Compactification.ofIsProper Y₀.hom) K i).1 =
        (frobeniusCohomologyMap D l Fact.out Y₀ Ω
          (Compactification.ofIsProper Y₀.hom) K i).2 ≫ (properFrobeniusQbarHomology.{u, v} Ω i).map
            (properFrobeniusQbarPulledPointIso D Y₀ l Ω K).hom := by
  sorry

end WeilConjectures
