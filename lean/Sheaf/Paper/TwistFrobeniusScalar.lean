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
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.FrobeniusGeometricExchange
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.Paper.IsomorphismComparisonScalarExtension
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.Algebra.Homology.FlatSingleDerivedNormalization
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import all Sheaf.Paper.AdicPurityRootComparisons
import Sheaf.Paper.SignedTwistFirstReduction
import all Sheaf.Paper.SignedLineScalarTensorTower

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

set_option linter.style.haveILetI false in
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
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  first
  | letI := sfWeilPrimeInvertible D l hl (sfWeilCohomologyPoint D)
    obtain ⟨c, hc, _⟩ := isomorphismScalarSheafModel_existsUnique l E L ι (geometricPoint D)
    let M := integralTwistLine l E (geometricPoint D) m
    obtain ⟨t, ht, htu⟩ := twistLineScalarIso_existsUnique l E (geometricPoint D) L ι m
    refine ⟨(c.app M).symm ≪≫ t, ?_, ?_⟩
    · intro U a x
      have h := congrArg (fun z ↦ (c.inv.app M).val.app U z) (hc M U a x)
      have hi : (c.inv.app M).val.app U
          (completedScalarTensorSection l E L ι (geometricPoint D) M U a x) =
            integralOrdinaryTensorSection l E L ι (geometricPoint D) M U a x := by
        rw [← h]
        exact congrArg (fun f ↦ f.val.app U
          (integralOrdinaryTensorSection l E L ι (geometricPoint D) M U a x))
            (c.hom_inv_id_app M)
      change t.hom.val.app U ((c.inv.app M).val.app U _) = _
      rw [hi]
      exact ht U a x
    · intro e he
      have h : c.app M ≪≫ e = t := by
        apply htu
        intro U a x
        change e.hom.val.app U ((c.hom.app M).val.app U _) = _
        exact (congrArg (fun z ↦ e.hom.val.app U z) (hc M U a x)).trans (he U a x)
      calc
        e = (c.app M).symm ≪≫ (c.app M ≪≫ e) := (Iso.symm_self_id_assoc (c.app M) e).symm
        _ = (c.app M).symm ≪≫ t := congrArg (fun f ↦ (c.app M).symm ≪≫ f) h

/-- The uniquely root-normalized universal sheaf scalar comparison.
Source: blueprint scalar-extension clause (blueprint: lem-pur-twist-frobenius-scalar). -/
def scalarSheafLine
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) :=
  (scalarSheafLine_existsUnique D l hl E L ι m).exists.choose

attribute [local irreducible] completedScalarChangeData completedCoefficientMap
  scalarSheafLine

private theorem scalarCounit_isIso
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (S : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E S) ℤ) :
    IsIso (completedScalarCounit l E L ι S P) := by
  obtain ⟨b, hb, _⟩ := isomorphismScalarModel_existsUnique l E L ι S
  have heq := hb.1 P
  let : IsIso (b.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E L ι S P) := by
    rw [heq]
    infer_instance
  exact
    IsIso.of_isIso_comp_left (b.hom.app (DerivedCategory.Q.obj P)) _

private theorem intrinsicComplete_unrestricted (S : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E S))
    (hK : IsSfDerivedComplete l E S K) : IsDerivedCompleteUnrestricted l E S K := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
  exact ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E S D₀ hl₀ K).mp hK⟩

private theorem isoFactor_existsUnique
    {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
    [IsIso f] [IsIso g] : ∃! e : Y ≅ Z, f ≫ e.hom = g := by
  refine ⟨(asIso f).symm ≪≫ asIso g, IsIso.hom_inv_id_assoc f g, ?_⟩
  intro e he
  apply Iso.ext
  apply (cancel_epi f).1
  exact he.trans (IsIso.hom_inv_id_assoc f g).symm

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
  classical
  let := sfWeilPrimeInvertible D l hl (sfWeilCohomologyPoint D)
  let S := geometricPoint D
  let P := (CochainComplex.singleFunctor _ 0).obj (integralTwistLine l E S m)
  let := scalarCounit_isIso l E L ι S P
  have hcomplete := intrinsicComplete_unrestricted l E S (integralLine D l hl E m).obj
    (integralLine D l hl E m).property.1
  let := ((finiteFreeCompletedScalarComparison l E L ι S).2.1 _ hcomplete).1
  exact isoFactor_existsUnique
    ((completedScalarComparison l E L ι S).app (integralLine D l hl E m).obj)
    (completedScalarCounit l E L ι S P ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (completedOrdinaryScalarExtension l E L ι S) (.up ℤ) 0).hom.app
            (integralTwistLine l E S m)) ≫
      (DerivedCategory.singleFunctor _ 0).map (scalarSheafLine D l hl E L ι m).hom)

/-- The canonical completed scalar comparison on signed lines.
Source: blueprint scalar-extension clause (blueprint: lem-pur-twist-frobenius-scalar). -/
def scalarIntegralLine
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) :=
  (scalarIntegralLine_existsUnique D l hl E L ι m).exists.choose

attribute [local irreducible] scalarIntegralLine

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

set_option linter.unusedSectionVars false in
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
  let e : AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      (Padic.finiteCoefficientBase l Ω) ≃ₐ[Padic l] Padic l :=
    (Shrink.algEquiv (Padic l) (Padic.finiteCoefficientBase l Ω).val).trans
      (IntermediateField.botEquiv (Padic l) Ω)
  let j := (Algebra.ofId (Padic l) E).comp e.toAlgHom
  have hj : ι.toRingHom.comp j.toRingHom =
      frobeniusCohomologyStageEmbedding.{u, v} l Ω (Padic.finiteCoefficientBase l Ω) := by
    ext x
    obtain ⟨a, rfl⟩ := e.symm.surjective x
    simp only [j, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, e.apply_symm_apply,
      Algebra.ofId_apply, AlgHom.commutes]
    change (algebraMap (Padic l) Ω) a =
      ((Padic.finiteCoefficientBase l Ω).val.subtype)
        ((Shrink.algEquiv (Padic l) (Padic.finiteCoefficientBase l Ω).val) (e.symm a))
    rw [show (Shrink.algEquiv (Padic l) (Padic.finiteCoefficientBase l Ω).val)
      (e.symm a) = (IntermediateField.botEquiv (Padic l) Ω).symm a from
        (Shrink.algEquiv (Padic l) (Padic.finiteCoefficientBase l Ω).val).apply_symm_apply _]
    rw [IntermediateField.botEquiv_symm]
    rfl
  refine ⟨j, hj, ?_⟩
  intro k hk
  ext x
  apply ι.injective
  exact congrArg (fun f : _ →+* Ω ↦ f x) (hk.trans hj.symm)

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

set_option linter.unusedSectionVars false in
set_option linter.style.haveILetI false in
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
  letI := ι.toRingHom.toAlgebra
  letI := ULift.algebra'
  let e (M : ModuleCat.{u} E) :
      (ModuleCat.extendScalars.{u, v, u} ι.toRingHom).obj M ≃ₗ[Ω]
        (frobeniusCoefficientModules ι.toRingHom).obj M :=
    (ULift.moduleEquiv : ULift.{0} ((ModuleCat.extendScalars ι.toRingHom).obj M) ≃ₗ[Ω]
      (ModuleCat.extendScalars ι.toRingHom).obj M).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.uliftEquiv E Ω Ω M
  let α : ModuleCat.extendScalars.{u, v, u} ι.toRingHom ≅
      frobeniusCoefficientModules ι.toRingHom :=
    NatIso.ofComponents (fun M ↦ (e M).toModuleIso) (by
      intro M N f
      ext x
      rfl)
  refine ⟨α, ?_, ?_⟩
  · intro M a x
    rfl
  · intro β hβ
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact hβ M 1 x

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
  with_unfolding_all rfl

/-- The equality identification of the two unchanged integral representatives.
Source: blueprint raw localization convention
(blueprint: lem-pur-twist-frobenius-scalar). -/
def integralPointSectionsIso (m : ℤ) :=
  eqToIso (integralPointSections_eq D l hl E m)

set_option linter.style.haveILetI false in
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
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  letI := (localization l E).toAlgebra
  let e (M : ModuleCat.{u + 1} R) :
      (ModuleCat.extendScalars.{u + 1, u, u + 1} (localization l E)).obj M ≃ₗ[E]
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E) ⋙
          pointFibreCoefficientDown E).obj M) :=
    let N := (ModuleCat.restrictScalars (pointIntegralToField l E)).obj
      (ModuleCat.of (ULift.{u + 1, u} E) (ULift.{u + 1, u} E))
    letI : Module E N := Module.compHom N
      (ULift.ringEquiv : ULift.{u + 1, u} E ≃+* E).symm.toRingHom
    letI : IsScalarTower R E N := ⟨fun r a x ↦ by
      apply ULift.down_injective
      exact mul_assoc ((localization l E) r) a x.down⟩
    let f : E ≃ₗ[E] N :=
      { toFun := ULift.up
        invFun := ULift.down
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    TensorProduct.AlgebraTensorModule.congr f (.refl R M)
  let α : ModuleCat.extendScalars.{u + 1, u, u + 1} (localization l E) ≅
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E) ⋙
        pointFibreCoefficientDown E :=
    NatIso.ofComponents (fun M ↦ (e M).toModuleIso) (by
      intro M N f
      ext x
      rfl)
  refine ⟨α, ?_, ?_⟩
  · intro M a x
    rfl
  · intro β hβ
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact hβ M 1 x

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

section SignedQuotientProof

set_option Elab.async false
-- Inline the instance aliases to keep normalization of coefficient sheaves fast.
set_option linter.style.haveILetI false

private theorem positiveQuotients_comparison (S : Scheme.{u}) (n : ℕ) :
    ∃ B : ∀ r : ℕ,
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (completedIntegralCommRingProjectionUnrestricted l E S n)
        (integralTwistLine l E S (r : ℤ)) ≅
          finiteCoefficientTwist l E S n (r : ℤ),
      ∀ (r : ℕ) (U : S.ProEtᵒᵖ)
        (a : (integralCoefficientCommRingSheaf l E S n).obj.obj U)
        (x : (integralTwistLine l E S (r : ℤ)).val.obj U),
        (B r).hom.val.app U (SheafOfModules.scalarExtensionSection
          (completedIntegralCommRingProjectionUnrestricted l E S n)
          _ U a x) = a • (@id ((finiteCoefficientTwist l E S n (r : ℤ)).val.obj U)
            ((adicPurityRootQuotients l E n S r).val.app U x)) := by
  classical
  letI : HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology S)
      AddCommGrpCat.{u + 1} := inferInstance
  letI : (AlgebraicGeometry.Scheme.ProEt.topology S).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := inferInstance
  letI : ∀ U : S.ProEt,
      HasWeakSheafify ((AlgebraicGeometry.Scheme.ProEt.topology S).over U)
        AddCommGrpCat.{u + 1} := by infer_instance
  letI : ∀ U : S.ProEt,
      ((AlgebraicGeometry.Scheme.ProEt.topology S).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u + 1} := by infer_instance
  let p := completedIntegralCommRingProjectionUnrestricted l E S n
  let L := AlgebraicGeometry.Scheme.purTwistIntegralModule S l E
  let N := AlgebraicGeometry.Scheme.purTwistFiniteOne S l E n
  obtain ⟨b, hb⟩ := signedTwistFirstReduction l E S n
  let B := SheafOfModules.positiveComparison.{u + 1, u, u + 1} p L N b
  let c : AdicPurityRootQuotients l E n S := fun r ↦
    SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} p
        (integralTwistLine l E S (r : ℤ)) ≫
      (scalarReductionRestriction l E S n).map (B r).hom
  have hc (r : ℕ) (U : S.ProEtᵒᵖ) (x : (integralTwistLine l E S (r : ℤ)).val.obj U) :
      (c r).val.app U x = (B r).hom.val.app U
        (SheafOfModules.scalarExtensionSection p _ U 1 x) := rfl
  have hnorm : IsAdicPurityRootQuotients l E n S c := by
    refine ⟨?_, ?_, ?_⟩
    · intro U a
      rw [hc]
      exact (SheafOfModules.scalarExtensionUnitIso_tmul p U 1 a).trans (one_mul (p.hom.app U a))
    · intro U a x
      rw [hc]
      exact hb U (AlgebraicGeometry.Scheme.purTwistIntegralTensor S l E U a x)
    · intro r U x y
      rw [hc, hc, hc]
      exact SheafOfModules.positiveComparison_tmul.{u + 1, u, u + 1} p L N b r U 1 x y
  have heq : c = adicPurityRootQuotients l E n S :=
    (adicPurityRootQuotients_existsUnique l E n S).unique hnorm
      (adicPurityRootQuotients_existsUnique l E n S).choose_spec.1
  refine ⟨B, ?_⟩
  intro r U a x
  rw [← heq, hc]
  change (B r).hom.val.app U (SheafOfModules.scalarExtensionSection p _ U a x) =
    a • (B r).hom.val.app U (SheafOfModules.scalarExtensionSection p _ U 1 x)
  calc
    _ = (B r).hom.val.app U (a • SheafOfModules.scalarExtensionSection p _ U 1 x) := by
      congr 1
      exact (SheafOfModules.scalarExtensionSection_smul p _ U a 1 x).trans
        (congrArg (fun z ↦ SheafOfModules.scalarExtensionSection p _ U z x) (mul_one a))
        |>.symm
    _ = _ := ((B r).hom.val.app U).hom.map_smul a _

/-- The existing nonnegative quotient family, extended by its unique dual evaluation
formula. Source: blueprint finite reduction, including negative twists
(blueprint: lem-pur-twist-frobenius-scalar).
Proof: the normalized first-line quotient and ordinary tensor base change give
isomorphisms on all nonnegative powers. Their unit maps satisfy the three root
quotient clauses, so uniqueness identifies them with adicPurityRootQuotients.
For a negative power, extend the corresponding functional to the quotient tensor
and precompose with the inverse positive comparison. The pure-tensor evaluation
formula proves the required equation. To prove uniqueness, precompose a competing
functional with the positive comparison on each slice. Tensor generation and
scalar linearity reduce to positive quotient sections, and naturality reduces
their evaluations to the specified identity-slice equations. -/
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
  classical
  suffices h : ∀ S : Scheme.{u}, ∃! c : (∀ m : ℤ, integralTwistLine l E S m ⟶
      (scalarReductionRestriction l E S n).obj (finiteCoefficientTwist l E S n m)),
      (∀ d : ℕ, c (d : ℤ) = adicPurityRootQuotients l E n S d) ∧
      ∀ (j : ℕ) (U : S.ProEtᵒᵖ)
        (φ : (integralTwistLine l E S (Int.negSucc j)).val.obj U)
        (x : (integralTwistLine l E S ((j + 1 : ℕ) : ℤ)).val.obj U),
        (((c (Int.negSucc j)).val.app U φ).app
          (Opposite.op (Over.mk (𝟙 U.unop))))
            ((c ((j + 1 : ℕ) : ℤ)).val.app U x) =
          (completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U
            ((φ.app (Opposite.op (Over.mk (𝟙 U.unop)))) x) by
    exact h (geometricPoint D)
  intro S
  letI : HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology S)
      AddCommGrpCat.{u + 1} := inferInstance
  letI : (AlgebraicGeometry.Scheme.ProEt.topology S).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := inferInstance
  letI : ∀ U : S.ProEt,
      HasWeakSheafify ((AlgebraicGeometry.Scheme.ProEt.topology S).over U)
        AddCommGrpCat.{u + 1} := by infer_instance
  letI : ∀ U : S.ProEt,
      ((AlgebraicGeometry.Scheme.ProEt.topology S).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u + 1} := by infer_instance
  let Q := ∀ m : ℤ, integralTwistLine l E S m ⟶
    (scalarReductionRestriction l E S n).obj (finiteCoefficientTwist l E S n m)
  let p := completedIntegralCommRingProjectionUnrestricted l E S n
  obtain ⟨B, hB⟩ := positiveQuotients_comparison l E S n
  let d (r : ℕ) : integralTwistLine l E S (Int.negSucc r) ⟶
      (scalarReductionRestriction l E S n).obj
        (finiteCoefficientTwist l E S n (Int.negSucc r)) :=
    SheafOfModules.scalarDualBaseMap p (integralTwistLine l E S ((r + 1 : ℕ) : ℤ)) ≫
      (scalarReductionRestriction l E S n).map
        (SheafOfModules.homObjMap (R := integralCoefficientCommRingSheaf l E S n)
          (B (r + 1)).inv (𝟙 (SheafOfModules.unit (integralCoefficientSheaf l E S n))))
  let c : Q := fun m ↦ match m with
    | .ofNat r => adicPurityRootQuotients l E n S r
    | .negSucc r => d r
  have heval (r : ℕ) (U : S.ProEtᵒᵖ)
      (φ : (integralTwistLine l E S (Int.negSucc r)).val.obj U)
      (x : (integralTwistLine l E S ((r + 1 : ℕ) : ℤ)).val.obj U) :
      (((c (Int.negSucc r)).val.app U φ).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
          ((c ((r + 1 : ℕ) : ℤ)).val.app U x) =
        p.hom.app U ((φ.app (Opposite.op (Over.mk (𝟙 U.unop)))) x) := by
    have hx := hB (r + 1) U 1 x
    simp only [one_smul, id_eq] at hx
    have hi : (B (r + 1)).inv.val.app U
        ((adicPurityRootQuotients l E n S (r + 1)).val.app U x) =
          SheafOfModules.scalarExtensionSection p _ U 1 x := by
      rw [← hx]
      exact congrArg (fun f ↦ f.val.app U
        (SheafOfModules.scalarExtensionSection p _ U 1 x)) (B (r + 1)).hom_inv_id
    change (SheafOfModules.scalarDualBaseSection p _ U φ).app
      (Opposite.op (Over.mk (𝟙 U.unop))) ((B (r + 1)).inv.val.app U _) = _
    rw [hi]
    have h := SheafOfModules.scalarDualBaseSection_tmul p
      (integralTwistLine l E S ((r + 1 : ℕ) : ℤ)) U φ
      (Opposite.op (Over.mk (𝟙 U.unop))) 1 x
    simpa only [Over.mk, CostructuredArrow.mk_left, Opposite.unop_op,
      Opposite.op_unop, mul_one, integralTwistLine, coefficientTwistLine] using h
  refine ⟨c, ⟨fun _ ↦ rfl, heval⟩, ?_⟩
  intro f hf
  funext m
  cases m with
  | ofNat r => exact hf.1 r
  | negSucc r =>
    let P := integralTwistLine l E S ((r + 1 : ℕ) : ℤ)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    let T := PresheafOfModules.restrictOver
      (integralCoefficientCommRingSheaf l E S n).obj U.unop
    have : IsIso (T.map (B (r + 1)).hom.val) := by
      have : IsIso (B (r + 1)).hom.val :=
        (SheafOfModules.forget _).map_isIso (B (r + 1)).hom
      exact T.map_isIso (B (r + 1)).hom.val
    apply (cancel_epi (T.map (B (r + 1)).hom.val)).mp
    apply SheafOfModules.scalarDual_section_ext p P U
    intro W a x
    let V := Opposite.op W.unop.left
    have hrestrict (g : Q) :
        ((g (Int.negSucc r)).val.app U φ).app W
          ((adicPurityRootQuotients l E n S (r + 1)).val.app V x) =
        ((g (Int.negSucc r)).val.app V
          ((integralTwistLine l E S (Int.negSucc r)).val.map W.unop.hom.op φ)).app
            (Opposite.op (Over.mk (𝟙 V.unop)))
              ((adicPurityRootQuotients l E n S (r + 1)).val.app V x) := by
      rw [PresheafOfModules.naturality_apply (g (Int.negSucc r)).val]
      change _ = ((g (Int.negSucc r)).val.app U φ).app
        (Opposite.op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom))) _
      exact (PresheafOfModules.restrictOver_hom_app_congr
        ((g (Int.negSucc r)).val.app U φ) (Category.id_comp W.unop.hom) _).symm
    change ((f (Int.negSucc r)).val.app U φ).app W
        ((B (r + 1)).hom.val.app V
          (SheafOfModules.scalarExtensionSection p P V a x)) =
      ((c (Int.negSucc r)).val.app U φ).app W
        ((B (r + 1)).hom.val.app V
          (SheafOfModules.scalarExtensionSection p P V a x))
    rw [hB, map_smul, map_smul]
    congr 1
    refine (hrestrict f).trans (Eq.trans ?_ (hrestrict c).symm)
    have hh := hf.2 r V
      ((integralTwistLine l E S (Int.negSucc r)).val.map W.unop.hom.op φ) x
    rw [hf.1 (r + 1)] at hh
    exact hh.trans (heval r V _ x).symm

end SignedQuotientProof

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

set_option linter.style.haveILetI false in
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
  letI := sfWeilPrimeInvertible D l hl (sfWeilCohomologyPoint D)
  let S := geometricPoint D
  have hfree := (AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free.{u, 0} S l E).2.2.1.2.2.1
  letI := hfree
  have hf := coefficientTwistLine_exact S
    (R := completedIntegralCommRingSheafUnrestricted l E S)
    (AlgebraicGeometry.Scheme.purTwistIntegralModule S l E) m
  have hflat : SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology S)
      (R := completedIntegralCommRingSheafUnrestricted l E S)
      (integralTwistLine l E S m) := ⟨hf.2.1, hf.2.2⟩
  obtain ⟨hK, _⟩ := SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization
    (completedIntegralCommRingSheafUnrestricted l E S) (integralTwistLine l E S m) hflat
  letI := unrestrictedTowerCounit_isIso l E S n
    ((CochainComplex.singleFunctor _ 0).obj (integralTwistLine l E S m)) hK
  let e := asIso ((scalarReductionCounit l E S n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj (integralTwistLine l E S m)))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (scalarReductionExtension l E S n) (.up ℤ) 0).app
          (integralTwistLine l E S m)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (reductionSheafLine D l E n m)
  refine ⟨e, rfl, ?_⟩
  intro f hf
  exact Iso.ext hf

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
   m = -d to obtain q inverse and q^d, also for d = 0.
   (blueprint: lem-pur-twist-frobenius-scalar-finite-integral). -/
theorem twist_frobenius_scalar_finite_integral (m : ℤ) :
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
        scalar (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) D.q m • x) := by
  sorry

/-- The rational and algebraically closed coefficient pieces of the Frobenius scalar
statement. This is the rational/common-stage part of the source argument.
Source: Weil II (1.1.7), (1.2.7); (blueprint: lem-pur-twist-frobenius-scalar-rational-qbar).
The proof uses the exact point-sections comparison, the canonical Weil line maps,
and scalar extension along the coefficient tower. -/
theorem twist_frobenius_scalar_rational_qbar (m : ℤ) :
    ((∀ i : ℤ, i ≠ 0 → Subsingleton (rationalH D l hl E m i)) ∧
      Nonempty (rationalH D l hl E m 0 ≃ₗ[E] E) ∧
      ∀ x : rationalH D l hl E m 0,
        (rationalF D l hl E m).hom x = scalar E D.q m • x) ∧
    ((∀ i : ℤ, i ≠ 0 → Subsingleton (qbarH D l hl Ω m i)) ∧
      Nonempty (qbarH D l hl Ω m 0 ≃ₗ[Ω] Ω) ∧
      ∀ x : qbarH D l hl Ω m 0,
        (qbarF D l hl Ω m).hom x = scalar Ω D.q m • x) := by
  sorry

/-- The finite reduction and integral localization compatibility pieces.
Source: Weil II (1.1.7), (blueprint: lem-pur-twist-frobenius-scalar-reduction-localization).
The proof follows the canonical reduction counit and the localization tensor
comparison, checking the displayed Frobenius intertwining equation on generators. -/
theorem twist_frobenius_scalar_reduction_localization (m : ℤ) :
    (∀ n : ℕ, CoefficientCompatibility (reduction l E n)
      (integralH D l hl E m 0) (finiteH D l E n m 0)
      (integralF D l hl E m) (finiteF D l hl E n m)
      (reductionH D l hl E n m)) ∧
    CoefficientCompatibility (localization l E)
      (integralH D l hl E m 0)
      ((ModuleCat.uliftFunctor.{u + 1, u} E).obj (rationalH D l hl E m 0))
      (integralF D l hl E m)
      ((ModuleCat.uliftFunctor.{u + 1, u} E).map (rationalF D l hl E m))
      (localizationH D l hl E m) := by
  sorry

private theorem scalar_map_field {K : Type w₁} {L : Type w₂} [Field K] [Field L]
    (c : K →+* L) (q : ℕ) (m : ℤ) : c (scalar K q m) = scalar L q m := by
  cases m <;> simp [scalar, Ring.inverse_eq_inv]

private theorem compatibility_of_scalar
    {K : Type w₁} {L : Type w₂} [Field K] [Field L] (c : K →+* L)
    (M : ModuleCat.{w₃} K) (N : ModuleCat.{max w₂ w₃} L)
    (f : End M) (g : End N) (e : (ModuleCat.extendScalars c).obj M ⟶ N)
    [IsIso e] (q : ℕ) (m : ℤ)
    (hf : ∀ x : M, f.hom x = scalar K q m • x)
    (hg : ∀ x : N, g.hom x = scalar L q m • x) :
    CoefficientCompatibility c M N f g e := by
  refine ⟨inferInstance, ?_⟩
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change e.hom ((ModuleCat.extendScalars c).map f ((1 : L) ⊗ₜ[K, c] x)) =
    g.hom (e.hom ((1 : L) ⊗ₜ[K, c] x))
  rw [ModuleCat.ExtendScalars.map_tmul, hf, hg]
  have ht : (1 : L) ⊗ₜ[K, c] (scalar K q m • x) =
      c (scalar K q m) • ((1 : L) ⊗ₜ[K, c] x) := by
    let := c.toAlgebra
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rfl
  rw [ht, e.hom.map_smul, scalar_map_field]

attribute [local irreducible] scalarRationalH scalarQbarH

private theorem scalarRationalH_isIso
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m : ℤ) : IsIso (scalarRationalH D l hl E L ι m) := by
  unfold scalarRationalH
  infer_instance

private theorem scalarQbarH_isIso (ι : E →ₐ[Padic l] Ω) (m : ℤ) :
    IsIso (scalarQbarH D l hl E Ω ι m) := by
  unfold scalarQbarH
  infer_instance


attribute [local irreducible] reductionH localizationH finiteF integralF rationalF qbarF
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The scalar extension compatibilities for finite coefficient fields and the common
algebraic closure. Source: Weil II (1.1.7).
(blueprint: lem-pur-twist-frobenius-scalar-field-extensions).
The proof transports the canonical rational and common-stage Weil structures through the
normalized coefficient comparisons and uses their pure-tensor formulas. -/
theorem twist_frobenius_scalar_field_extensions (m : ℤ) :
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
      (ι : E →ₐ[Padic l] L), CoefficientCompatibility ι.toRingHom
        (rationalH D l hl E m 0) (rationalH D l hl L m 0)
        (rationalF D l hl E m) (rationalF D l hl L m)
        (scalarRationalH D l hl E L ι m)) ∧
    (∀ ι : E →ₐ[Padic l] Ω, CoefficientCompatibility ι.toRingHom
      (rationalH D l hl E m 0) (qbarH D l hl Ω m 0)
      (rationalF D l hl E m) (qbarF D l hl Ω m)
      (scalarQbarH D l hl E Ω ι m)) := by
  have hE := (twist_frobenius_scalar_rational_qbar D l hl E Ω m).1.2.2
  constructor
  · intro L _ _ _ ι
    have hL := (twist_frobenius_scalar_rational_qbar D l hl L Ω m).1.2.2
    let := scalarRationalH_isIso D l hl E L ι m
    exact compatibility_of_scalar ι.toRingHom _ _ _ _ _ D.q m hE hL
  · intro ι
    have hΩ := (twist_frobenius_scalar_rational_qbar D l hl E Ω m).2.2.2
    let := scalarQbarH_isIso D l hl E Ω ι m
    exact compatibility_of_scalar ι.toRingHom _ _ _ _ _ D.q m hE hΩ

/-- Assemble the four component statements into the full geometric Frobenius scalar
theorem. Source: Weil I (2.2), Weil II (1.1.7), (blueprint: lem-pur-twist-frobenius-scalar).
Each component is exactly one conjunct of the displayed target, so conjunction
introduction gives the result. -/
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
  obtain ⟨h₁, h₂⟩ := twist_frobenius_scalar_finite_integral D l hl E m
  obtain ⟨h₃, h₄⟩ := twist_frobenius_scalar_rational_qbar D l hl E Ω m
  obtain ⟨h₅, h₆⟩ := twist_frobenius_scalar_reduction_localization D l hl E m
  obtain ⟨h₇, h₈⟩ := twist_frobenius_scalar_field_extensions D l hl E Ω m
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩

end WeilConjectures.TwistFrobeniusScalar
