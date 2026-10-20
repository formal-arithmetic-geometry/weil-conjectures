/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module
public import Sheaf.Paper.DirectImagesConstructible
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.PointFibreEquivalence
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Determinant
public import Sheaf.Paper.CoefficientCohomologyModules
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfIntegralDirectImageConstructible
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.SmoothPurityQbar
/-! # Ordinary and compactly supported coefficient cohomology

Source: Weil blueprint main-20261015, sec-six-functors-basics/sk-def-sf-admissible,
ordinary and compactly supported cohomology
(blueprint: def-weil-ordinary-compact-cohomology).

The four coefficient constructions evaluate the recorded ordinary/compact direct images
at the geometric point. Constants, signed twists and Weil-forgetful specializations use
those same constructions. `ordinaryCompactCohomology` collects the actual operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]

/-- Ordinary finite-level derived sections, using the recorded direct-image and point-section
functors.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-sf-admissible/def-weil-ordinary-compact-cohomology.md.
Source: blueprint main-20261015, ordinary and compact cohomology
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteOrdinarySections (n : ℕ) (hn : 1 ≤ n) (K : proEtaleDerivedCategory Y
    (Padic.coefficientExtensionRing l E n)) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapDerivedCategory).obj
    ((proEtaleConstantDerivedDirectImage (Y ↘ Spec (.of D.k))
      (Padic.coefficientExtensionRing l E n)).obj K)

/-- Ordinary finite-level cohomology is homology of those actual sections complexes.
Source: blueprint node def-weil-ordinary-compact-cohomology.
Source: blueprint main-20261015, ordinary and compact cohomology
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteOrdinaryCohomology (n : ℕ) (hn : 1 ≤ n) (K : proEtaleDerivedCategory Y
    (Padic.coefficientExtensionRing l E n)) (i : ℤ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1, u}
    (Padic.coefficientExtensionRing l E n))) i).obj
      (finiteOrdinarySections D l E Y n hn K)

/-- Compactly supported finite-level derived sections, using the specified compactification.
Source: blueprint main-20261015, ordinary and compact cohomology
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteCompactSections (c : Compactification (Y ↘ Spec (.of D.k))) (n : ℕ) (hn : 1 ≤ n)
    (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapDerivedCategory).obj
    ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n)).obj K)

/-- Compactly supported finite-level cohomology.
Source: blueprint main-20261015, ordinary and compact cohomology
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteCompactCohomology (c : Compactification (Y ↘ Spec (.of D.k))) (n : ℕ) (hn : 1 ≤ n)
    (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) (i : ℤ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1, u}
    (Padic.coefficientExtensionRing l E n))) i).obj
      (finiteCompactSections D l E Y c n hn K)

/-- The tower-defined integral ordinary image, in its constructible category.
The chosen Roos vertex is determined up to isomorphism by the recorded derived limit;
its data are not chosen from a mere unstructured existence assertion.
Source: blueprint ordinary-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralImage (K : sfIntegralConstructibleCategory l E Y) :
    sfIntegralConstructibleCategory l E (Spec (.of D.k)) := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (Y ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  let h := sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
    E (Y ↘ Spec (.of D.k)) K.obj K.property
  letI := h.1.choose
  let L : SfIntegralDirectImage l E (Y ↘ Spec (.of D.k)) K.obj := h.1.choose_spec.some
  exact ⟨L.obj, (h.2.1 L).1⟩

/-- Integral RΓ is the recorded geometric-point fibre of Ra_*.
Source: blueprint ordinary-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralOrdinarySections (K : sfIntegralConstructibleCategory l E Y) :=
  (pointIntegralFibre D l hl E).obj (integralImage D l hl E Y K)

/-- Integral H^i is the cohomology module of RΓ in every integer degree.
Source: blueprint cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralOrdinaryCohomology (K : sfIntegralConstructibleCategory l E Y) (i : ℤ) :=
  (DerivedCategory.coefficientFgCohomology _ _ i).obj
    (integralOrdinarySections D l hl E Y K)

/-- Integral RΓ_c is the point fibre of the recorded compact-support value.
Source: blueprint compact-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralCompactSections (c : Compactification (Y ↘ Spec (.of D.k)))
    (K : sfIntegralConstructibleCategory l E Y) :
    (DerivedCategory.pointFgComplete
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
      (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})).FullSubcategory := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (Y ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  exact (pointIntegralFibre D l hl E).obj
    (sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl) c K)

/-- Integral H_c^i is cohomology of the compact sections complex.
Source: blueprint cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralCompactCohomology (c : Compactification (Y ↘ Spec (.of D.k)))
    (K : sfIntegralConstructibleCategory l E Y) (i : ℤ) :=
  (DerivedCategory.coefficientFgCohomology _ _ i).obj
    (integralCompactSections D l hl E Y c K)

/-- Ra_* on a rational object uses its recorded integral representative and localization.
Source: blueprint ordinary-cohomology formula, rational coefficients
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalImage (K : sfRationalConstructibleCategory l E Y) :
    sfRationalConstructibleCategory l E (Spec (.of D.k)) :=
  (sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj
    (integralImage D l hl E Y K.obj)

/-- Rational RΓ uses the recorded rational point fibre, including coefficient descent.
Source: blueprint ordinary-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalOrdinarySections (K : sfRationalConstructibleCategory l E Y) :=
  (pointRationalFibre D l hl E).obj (rationalImage D l hl E Y K)

/-- Rational H^i is the ordinary cohomology module over E.
Source: blueprint cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalOrdinaryCohomology (K : sfRationalConstructibleCategory l E Y) (i : ℤ) :=
  (DerivedCategory.coefficientFdCohomology E i).obj (rationalOrdinarySections D l hl E Y K)

/-- Rational RΓ_c uses the actual rationalized compact-support value.
Source: blueprint compact-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalCompactSections (c : Compactification (Y ↘ Spec (.of D.k)))
    (K : sfRationalConstructibleCategory l E Y) :
    (DerivedCategory.pointFiniteDimensional E).FullSubcategory := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (Y ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  exact (pointRationalFibre D l hl E).obj
    (sfRationalCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl) c K.obj)

/-- Rational H_c^i is the cohomology module of RΓ_c.
Source: blueprint cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalCompactCohomology (c : Compactification (Y ↘ Spec (.of D.k)))
    (K : sfRationalConstructibleCategory l E Y) (i : ℤ) :=
  (DerivedCategory.coefficientFdCohomology E i).obj (rationalCompactSections D l hl E Y c K)

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Stagewise Ra_* retains the actual finite field of definition of its input.
Source: blueprint ordinary-cohomology formula, algebraically closed coefficients
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarImage (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) :=
  ⟨K.stage, rationalImage D l hl (Coefficient.{u} l Ω K.stage) Y K.obj⟩

/-- Algebraically closed RΓ uses the recorded stagewise geometric-point fibre.
Source: blueprint ordinary-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarOrdinarySections (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  (pointQbarFibre D l hl Ω).obj (qbarImage D l hl Y Ω K)

/-- Algebraically closed H^i is Ω tensor the finite-stage cohomology module.
Source: blueprint cohomology formula, stagewise target
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarOrdinaryCohomology (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) (i : ℤ) :=
  (DerivedCategory.coefficientQbarCohomology l Ω i).obj (qbarOrdinarySections D l hl Y Ω K)

/-- Algebraically closed RΓ_c uses the recorded finite-stage compact-support value.
Source: blueprint compact-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarCompactSections (c : Compactification (Y ↘ Spec (.of D.k)))
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    DerivedCategory.PointFdQbar l Ω := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (Y ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  exact (pointQbarFibre D l hl Ω).obj
    (sfQbarCompactSupportValue l D.k (finiteFieldDatumPrimeUnit D l hl) Ω c K.stage K.obj.obj)

/-- Algebraically closed H_c^i applies the recorded coefficient cohomology functor.
Source: blueprint cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarCompactCohomology (c : Compactification (Y ↘ Spec (.of D.k)))
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) (i : ℤ) :=
  (DerivedCategory.coefficientQbarCohomology l Ω i).obj (qbarCompactSections D l hl Y Ω c K)

/-- The finite constant object at the source's exponent n, obtained by reindexing
its published exponent j+1 presentation. This includes n=1.
Source: blueprint coefficient-object paragraph
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteCohomologyCoefficient (n : ℕ) (hn : 1 ≤ n) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) :=
  cast (congrArg (fun j : ℕ ↦ proEtaleDerivedCategory Y
    (Padic.coefficientExtensionRing l E j)) (Nat.sub_add_cancel hn))
    (finiteConstantCoefficientObject l E Y (n - 1))

/-- The completed constant coefficient object with its recorded constructibility proof.
Source: blueprint coefficient-object paragraph
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralCohomologyCoefficient : sfIntegralConstructibleCategory l E Y :=
  constantWeilIntegralObject l E D hl Y

/-- E_Y is the recorded rationalization of the completed constant coefficient object.
Source: blueprint coefficient-object paragraph
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalCohomologyCoefficient : sfRationalConstructibleCategory l E Y :=
  constantWeilRationalObject l E D hl Y

/-- The recorded constantCoefficientPair, in the intrinsic integral presentation at E₀.
Its underlying complex is retained verbatim; only the constructibility proof/interface
and the raw rationalization wrapper change.
Source: blueprint coefficient-object paragraph, algebraically closed coefficients
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarCohomologyCoefficient (E₀ : Padic.FiniteCoefficientFields l Ω) :
    generalAlgebraicallyClosedConstructibleCategory l Ω Y :=
  ⟨E₀, (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E₀) Y).obj
    ⟨(AlgebraicallyClosedCoefficients.constantCoefficientPair D l hl Ω Y E₀).obj.obj.obj,
      (integralConstantCoefficient_constructible l (Coefficient.{u} l Ω E₀) Y D hl).2.1⟩⟩

/-- Λ_Y(m) at finite level is the published derived tensor with the signed Tate line,
reindexed from exponent j+1 to the positive exponent n supplied by the node.
Source: blueprint twisted-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteTwistedCoefficient (n : ℕ) (hn : 1 ≤ n) (m : ℤ) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) := by
  letI := smoothQbarResidueInvertible D l hl Y
  exact cast (congrArg (fun j : ℕ ↦ proEtaleDerivedCategory Y
    (Padic.coefficientExtensionRing l E j)) (Nat.sub_add_cancel hn))
    ((finiteComplexTwist l E Y (n - 1) m).obj
      (finiteConstantCoefficientObject l E Y (n - 1)))

/-- The integral constant object derived-tensored with the recorded signed coefficient line.
Source: blueprint Λ_Y(m) formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralTwistedCoefficient (m : ℤ) : sfIntegralConstructibleCategory l E Y := by
  letI := smoothQbarResidueInvertible D l hl Y
  exact (constructibleIntegralTensor l E Y).obj
    (integralCohomologyCoefficient D l hl E Y,
      intrinsicIntegralCoefficientTwist D l hl E Y m)

/-- Rational Λ_Y(m) is scalar extension of the same integral derived tensor.
Source: blueprint Λ_Y(m) formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalTwistedCoefficient (m : ℤ) : sfRationalConstructibleCategory l E Y :=
  (sfRationalConstructibleLocalization l E Y).obj (integralTwistedCoefficient D l hl E Y m)

/-- Algebraically closed Λ_Y(m) uses the actual common-stage derived tensor twist.
Source: blueprint Λ_Y(m) formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarTwistedCoefficient (E₀ : Padic.FiniteCoefficientFields l Ω) (m : ℤ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω Y := by
  letI := smoothQbarResidueInvertible D l hl Y
  exact (intrinsicQbarComplexTwistFunctor D l hl Y Ω m).obj
    (qbarCohomologyCoefficient D l hl Y Ω E₀)

/-- The ordinary and compactly supported constant-coefficient abbreviations,
using exactly the two cohomology constructions on the specified coefficient object.
Source: blueprint constant-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteConstantCohomology (c : Compactification (Y ↘ Spec (.of D.k))) (n : ℕ) (hn : 1 ≤ n)
    (i : ℤ) :=
  (finiteOrdinaryCohomology D l E Y n hn (finiteCohomologyCoefficient l E Y n hn) i,
    finiteCompactCohomology D l E Y c n hn (finiteCohomologyCoefficient l E Y n hn) i)

/-- The ordinary and compactly supported signed-twist abbreviations,
using exactly the two cohomology constructions on the specified coefficient object.
Source: blueprint twisted-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteTwistedCohomology (c : Compactification (Y ↘ Spec (.of D.k))) (n : ℕ) (hn : 1 ≤ n) (m : ℤ)
    (i : ℤ) :=
  (finiteOrdinaryCohomology D l E Y n hn (finiteTwistedCoefficient D l hl E Y n hn m) i,
    finiteCompactCohomology D l E Y c n hn (finiteTwistedCoefficient D l hl E Y n hn m) i)

/-- The ordinary and compactly supported constant-coefficient abbreviations,
using exactly the two cohomology constructions on the specified coefficient object.
Source: blueprint constant-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralConstantCohomology (c : Compactification (Y ↘ Spec (.of D.k))) (i : ℤ) :=
  (integralOrdinaryCohomology D l hl E Y (integralCohomologyCoefficient D l hl E Y) i,
    integralCompactCohomology D l hl E Y c (integralCohomologyCoefficient D l hl E Y) i)

/-- The ordinary and compactly supported signed-twist abbreviations,
using exactly the two cohomology constructions on the specified coefficient object.
Source: blueprint twisted-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralTwistedCohomology (c : Compactification (Y ↘ Spec (.of D.k))) (m : ℤ)
    (i : ℤ) :=
  (integralOrdinaryCohomology D l hl E Y (integralTwistedCoefficient D l hl E Y m) i,
    integralCompactCohomology D l hl E Y c (integralTwistedCoefficient D l hl E Y m) i)

/-- The ordinary and compactly supported constant-coefficient abbreviations,
using exactly the two cohomology constructions on the specified coefficient object.
Source: blueprint constant-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalConstantCohomology (c : Compactification (Y ↘ Spec (.of D.k))) (i : ℤ) :=
  (rationalOrdinaryCohomology D l hl E Y (rationalCohomologyCoefficient D l hl E Y) i,
    rationalCompactCohomology D l hl E Y c (rationalCohomologyCoefficient D l hl E Y) i)

/-- The ordinary and compactly supported signed-twist abbreviations,
using exactly the two cohomology constructions on the specified coefficient object.
Source: blueprint twisted-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalTwistedCohomology (c : Compactification (Y ↘ Spec (.of D.k))) (m : ℤ)
    (i : ℤ) :=
  (rationalOrdinaryCohomology D l hl E Y (rationalTwistedCoefficient D l hl E Y m) i,
    rationalCompactCohomology D l hl E Y c (rationalTwistedCoefficient D l hl E Y m) i)

/-- The ordinary and compactly supported constant-coefficient abbreviations,
using exactly the two cohomology constructions on the specified coefficient object.
Source: blueprint constant-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarConstantCohomology (c : Compactification (Y ↘ Spec (.of D.k)))
    (E₀ : Padic.FiniteCoefficientFields l Ω)
    (i : ℤ) :=
  (qbarOrdinaryCohomology D l hl Y Ω (qbarCohomologyCoefficient D l hl Y Ω E₀) i,
    qbarCompactCohomology D l hl Y Ω c (qbarCohomologyCoefficient D l hl Y Ω E₀) i)

/-- The ordinary and compactly supported signed-twist abbreviations,
using exactly the two cohomology constructions on the specified coefficient object.
Source: blueprint twisted-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarTwistedCohomology (c : Compactification (Y ↘ Spec (.of D.k)))
    (E₀ : Padic.FiniteCoefficientFields l Ω) (m : ℤ)
    (i : ℤ) :=
  (qbarOrdinaryCohomology D l hl Y Ω (qbarTwistedCoefficient D l hl Y Ω E₀ m) i,
    qbarCompactCohomology D l hl Y Ω c (qbarTwistedCoefficient D l hl Y Ω E₀ m) i)

section Weil

variable (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom]
  [LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))]
  [QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))]
  [IsSeparated ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))]

/-- For E-Weil complexes, RΓ and RΓ_c mean the constructions after For.
Source: blueprint final Weil-complex clause
(blueprint: def-weil-ordinary-compact-cohomology). -/
def weilSections (c : Compactification (D.geometricFiber Y₀).hom)
    (K : sfWeilComplex D l hl Y₀ E) :=
  (rationalOrdinarySections D l hl E (D.geometricFiber Y₀).left
      ((sfWeilForget D l hl Y₀ E).obj K),
    rationalCompactSections D l hl E (D.geometricFiber Y₀).left c
      ((sfWeilForget D l hl Y₀ E).obj K))

/-- For E-Weil complexes, both cohomology symbols apply the same construction after For.
Source: blueprint final Weil-complex clause
(blueprint: def-weil-ordinary-compact-cohomology). -/
def weilCohomology (c : Compactification (D.geometricFiber Y₀).hom)
    (K : sfWeilComplex D l hl Y₀ E) (i : ℤ) :=
  (rationalOrdinaryCohomology D l hl E (D.geometricFiber Y₀).left
      ((sfWeilForget D l hl Y₀ E).obj K) i,
    rationalCompactCohomology D l hl E (D.geometricFiber Y₀).left c
      ((sfWeilForget D l hl Y₀ E).obj K) i)

/-- For Qbar-Weil complexes, RΓ and RΓ_c are the common-stage constructions after For.
Source: blueprint final Weil-complex clause
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarWeilSections (c : Compactification (D.geometricFiber Y₀).hom)
    (K : sfCommonStageWeilComplex D l hl Y₀ Ω) :=
  (qbarOrdinarySections D l hl (D.geometricFiber Y₀).left Ω
      ((sfCommonStageWeilForget D l hl Y₀ Ω).obj K),
    qbarCompactSections D l hl (D.geometricFiber Y₀).left Ω c
      ((sfCommonStageWeilForget D l hl Y₀ Ω).obj K))

/-- Both cohomologies of a Qbar-Weil sheaf use its recorded common-stage For functor.
Source: blueprint final Weil-complex clause
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarWeilSheafCohomology (c : Compactification (D.geometricFiber Y₀).hom)
    (K : sfCommonStageWeilSheaf D l hl Y₀ Ω) (i : ℤ) :=
  (qbarOrdinaryCohomology D l hl (D.geometricFiber Y₀).left Ω
      ((sfCommonStageWeilForget D l hl Y₀ Ω).obj K.obj) i,
    qbarCompactCohomology D l hl (D.geometricFiber Y₀).left Ω c
      ((sfCommonStageWeilForget D l hl Y₀ Ω).obj K.obj) i)

/-- Both cohomologies of an arbitrary Qbar-Weil complex, after For.
Source: blueprint final Weil-complex clause
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarWeilCohomology (c : Compactification (D.geometricFiber Y₀).hom)
    (K : sfCommonStageWeilComplex D l hl Y₀ Ω) (i : ℤ) :=
  (qbarOrdinaryCohomology D l hl (D.geometricFiber Y₀).left Ω
      ((sfCommonStageWeilForget D l hl Y₀ Ω).obj K) i,
    qbarCompactCohomology D l hl (D.geometricFiber Y₀).left Ω c
      ((sfCommonStageWeilForget D l hl Y₀ Ω).obj K) i)

/-- Equip the rational constant with the recorded canonical Weil structure, and use For.
The first component retains the actual Weil sheaf, not merely its existence.
Source: blueprint canonical Weil structure and constant-cohomology clauses
(blueprint: def-weil-ordinary-compact-cohomology). -/
def constantWeilCohomology (c : Compactification (D.geometricFiber Y₀).hom) (i : ℤ) :=
  (constantWeilRationalSheaf l E D hl Y₀,
    weilCohomology D l hl E Y₀ c (constantWeilRationalSheaf l E D hl Y₀).obj i)

/-- Equip the Qbar constant with the recorded canonical common-stage Weil structure.
Source: blueprint canonical Weil structure and constant-cohomology clauses
(blueprint: def-weil-ordinary-compact-cohomology). -/
def qbarConstantWeilCohomology (c : Compactification (D.geometricFiber Y₀).hom) (i : ℤ) :=
  (constantWeilAlgebraicallyClosedSheaf l D hl Y₀ Ω,
    qbarWeilSheafCohomology D l hl Ω Y₀ c
      (constantWeilAlgebraicallyClosedSheaf l D hl Y₀ Ω) i)

end Weil

/-- The finite images in the exact constructible source category of Fib_s.
The recorded preservation theorem applies to the actual direct-image/compact-support
values. Its integral argument is the Roos presentation of the constant object and
imposes no hypothesis on the given finite complex.
Source: blueprint domain of Fib_s and finite-coefficient formulas
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteConstructibleImages (E₀ : Padic.FiniteCoefficientFields l Ω)
    (c : Compactification (Y ↘ Spec (.of D.k))) (n : ℕ) (hn : 1 ≤ n)
    (K : (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
      Y).FullSubcategory) :
    (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
      (Spec (.of D.k))).FullSubcategory ×
    (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
      (Spec (.of D.k))).FullSubcategory := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (Y ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  let I := integralCohomologyCoefficient D l hl (Coefficient.{u} l Ω E₀) Y
  let h := sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
    (Coefficient.{u} l Ω E₀) (Y ↘ Spec (.of D.k)) I.obj I.property
  letI := h.1.choose
  let L : SfIntegralDirectImage l (Coefficient.{u} l Ω E₀)
    (Y ↘ Spec (.of D.k)) I.obj := h.1.choose_spec.some
  let hK := directImages_constructible D l hl Ω E₀ n hn Y c K.property L
  letI := Padic.finite_coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n hn
  exact (⟨(proEtaleConstantDerivedDirectImage (Y ↘ Spec (.of D.k))
      (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)).obj K.obj, hK.1⟩,
    ⟨(sfIntrinsicCompactSupport c
      (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)).obj K.obj, hK.2.1⟩)

/-- The two finite sections complexes, now valued in D^b_fin(A), exactly as displayed.
Source: blueprint coefficient-complex formulas and finite point target
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteConstructibleSections (E₀ : Padic.FiniteCoefficientFields l Ω)
    (c : Compactification (Y ↘ Spec (.of D.k))) (n : ℕ) (hn : 1 ≤ n)
    (K : (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
      Y).FullSubcategory) :=
  ((pointFiniteFibre D l hl (Coefficient.{u} l Ω E₀) n hn).obj
      (finiteConstructibleImages D l hl Y Ω E₀ c n hn K).1,
    (pointFiniteFibre D l hl (Coefficient.{u} l Ω E₀) n hn).obj
      (finiteConstructibleImages D l hl Y Ω E₀ c n hn K).2)

/-- The two finite coefficient cohomologies, using the recorded finite homology functor.
Source: blueprint cohomology formulas
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteConstructibleCohomology (E₀ : Padic.FiniteCoefficientFields l Ω)
    (c : Compactification (Y ↘ Spec (.of D.k))) (n : ℕ) (hn : 1 ≤ n)
    (K : (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
      Y).FullSubcategory) (i : ℤ) :=
  ((DerivedCategory.coefficientFiniteCohomology _ i).obj
      (finiteConstructibleSections D l hl Y Ω E₀ c n hn K).1,
    (DerivedCategory.coefficientFiniteCohomology _ i).obj
      (finiteConstructibleSections D l hl Y Ω E₀ c n hn K).2)

/-- The displayed fibre equivalences reuse the recorded equivalence theorem.
Their functors remain exactly the specified finite, integral, rational and Qbar fibres.
Source: blueprint displayed Fib_s equivalences
(blueprint: def-weil-ordinary-compact-cohomology). -/
def cohomologyPointEquivalences (E₀ : Padic.FiniteCoefficientFields l Ω)
    (n : ℕ) (hn : 1 ≤ n) :
    ((intrinsicFiniteTorsionConstructible l E₀.val n hn (Spec (.of D.k))).FullSubcategory ≌
      (DerivedCategory.pointFiniteCohomology
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E₀.val n))).FullSubcategory) ×
    (sfIntegralConstructibleCategory l E₀.val (Spec (.of D.k)) ≌
      (DerivedCategory.pointFgComplete
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E₀.val))
        (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E₀.val)})).FullSubcategory) ×
    (sfRationalConstructibleCategory l E₀.val (Spec (.of D.k)) ≌
      (DerivedCategory.pointFiniteDimensional E₀.val).FullSubcategory) ×
    (generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) ≌
      DerivedCategory.PointFdQbar l Ω) := by
  let h := point_fibre_equivalence D l hl Ω E₀ n hn
  letI := h.1
  letI := h.2.1
  letI := h.2.2.1
  letI := h.2.2.2.1
  exact ((pointFiniteFibre D l hl E₀.val n hn).asEquivalence,
    (pointIntegralFibre D l hl E₀.val).asEquivalence,
    (pointRationalFibre D l hl E₀.val).asEquivalence,
    (pointQbarFibre D l hl Ω).asEquivalence)

/-- On finite-dimensional coefficient spaces these are the ordinary dimension, trace
and determinant, using Mathlib's definitions without introducing any alternative invariant.
Source: blueprint final linear-algebra clause
(blueprint: def-weil-ordinary-compact-cohomology). -/
def cohomologyLinearAlgebra (F : Type v) [Field F] (V : Type w) [AddCommGroup V]
    [Module F V] (_hV : FiniteDimensional F V) :=
  (Module.finrank F V, LinearMap.trace F V, (LinearMap.det : (V →ₗ[F] V) →* F))

/-- The concrete ordinary/compact cohomology operations for all four coefficient rings,
together with their constant and signed-twist specializations. E₀ is an actual finite
extension inside Ω; the canonical small coefficient model is used for the first three
levels. Every field of this tuple is the previously defined construction itself.
Source: blueprint all displayed cohomology definitions
(blueprint: def-weil-ordinary-compact-cohomology). -/
def ordinaryCompactCohomology (E₀ : Padic.FiniteCoefficientFields l Ω)
    (c : Compactification (Y ↘ Spec (.of D.k))) (n : ℕ) (hn : 1 ≤ n) :=
  (finiteConstructibleSections D l hl Y Ω E₀ c n hn,
    finiteConstructibleCohomology D l hl Y Ω E₀ c n hn,
    cohomologyPointEquivalences D l hl Ω E₀ n hn,
    finiteOrdinarySections D l (Coefficient.{u} l Ω E₀) Y n hn,
    finiteCompactSections D l (Coefficient.{u} l Ω E₀) Y c n hn,
    integralOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y,
    integralCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c,
    rationalOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y,
    rationalCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c,
    qbarOrdinarySections D l hl Y Ω,
    qbarCompactSections D l hl Y Ω c,
    finiteOrdinaryCohomology D l (Coefficient.{u} l Ω E₀) Y n hn,
    finiteCompactCohomology D l (Coefficient.{u} l Ω E₀) Y c n hn,
    integralOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y,
    integralCompactCohomology D l hl (Coefficient.{u} l Ω E₀) Y c,
    rationalOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y,
    rationalCompactCohomology D l hl (Coefficient.{u} l Ω E₀) Y c,
    qbarOrdinaryCohomology D l hl Y Ω,
    qbarCompactCohomology D l hl Y Ω c,
    finiteConstantCohomology D l (Coefficient.{u} l Ω E₀) Y c n hn,
    integralConstantCohomology D l hl (Coefficient.{u} l Ω E₀) Y c,
    rationalConstantCohomology D l hl (Coefficient.{u} l Ω E₀) Y c,
    qbarConstantCohomology D l hl Y Ω c E₀,
    finiteTwistedCohomology D l hl (Coefficient.{u} l Ω E₀) Y c n hn,
    integralTwistedCohomology D l hl (Coefficient.{u} l Ω E₀) Y c,
    rationalTwistedCohomology D l hl (Coefficient.{u} l Ω E₀) Y c,
    qbarTwistedCohomology D l hl Y Ω c E₀)

end WeilConjectures
