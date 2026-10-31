/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.DerivedPerfectPairing
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.CondensedSmoothTraceUnit
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.GlobalVerdierDuality
public import WeilConjectures.AlgebraicGeometry.TensorHomExchange
public import WeilConjectures.AlgebraicGeometry.CondensedWeilEquivarianceParent
public import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.CondensedFrobeniusComparisonCoherence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

import WeilConjectures.AlgebraicGeometry.FiniteGeometricPointCohomology

/-! # Smooth Poincare identification

Source: latest blueprint, sec-six-functors/sk-thm-sf-identification/_section.md,
main assertion and Complement (blueprint: sk-thm-sf-identification).
The scalar pairing is the recorded mixed-support cup/evaluation/trace composite.
The auxiliary expressions only name its canonical maps and clauses.
Definition interface (blueprint: def-sf-identification-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.SixFunctors

/-- The recorded Poincare composite extended to all finite-Tor constructible inputs.
Its cup, evaluation, shift and trace are precisely those of derivedPoincarePairing;
the latter declaration only accepts locally perfect inputs although its expression
needs no such proof. Source: displayed beta (blueprint: sk-thm-sf-identification). -/
def identificationPairing (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (Λ : ScalarSixRing.{u})
    (c : AlgebraicGeometry.ProEtale.PurityTransport.Coefficient ell)
    (e : c.bundled.{u} ell ≅ Λ)
    (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    (pairingCompactSections Λ.X D.k cf).obj K.obj ⊗
      ((pairingOrdinarySections Λ.X D.k X.hom).obj
        ((ihom K.obj).obj (𝟙_ _) ⊗ smoothTraceCoefficientLine ell Λ c e X.left d))
          ⟦2 * (d : ℤ)⟧ ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X))) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  pairingScalarCup Λ.X D.k cf K.obj
      ((ihom K.obj).obj (𝟙_ _) ⊗ smoothTraceCoefficientLine ell Λ c e X.left d)
      (2 * (d : ℤ)) ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      ((pairingCompactSections Λ.X D.k cf).map
        (pairingTwistedEvaluation Λ.X K.obj (smoothTraceCoefficientLine ell Λ c e X.left d))) ≫
    pairingScalarTrace ell D hEll Λ c e X d cf


/-- The degree-zero value of a scalar derived pairing on complementary-degree
classes. The native tensor shift comparison includes the total-complex signs.
Source: main assertion and Complement (blueprint: sk-thm-sf-identification). -/
def identificationDegreeValue {R : Type (u + 1)} [CommRing R]
    {P Q : DerivedCategory (ModuleCat.{u + 1} R)} (b : P ⊗ Q ⟶ 𝟙_ _)
    (i : ℤ) (x : 𝟙_ _ ⟶ P⟦i⟧) (y : 𝟙_ _ ⟶ Q⟦-i⟧) :
    𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)) ⟶ 𝟙_ _ :=
  (λ_ (𝟙_ _)).inv ≫ (x ⊗ₘ y) ≫
    (DerivedCategory.shiftTensorShiftIso (ModuleCat.{u + 1} R) P Q i (-i)).hom ≫
      (shiftFunctorZero' _ (i + -i) (add_neg_cancel i)).hom.app _ ≫ b

/-- Read an endomorphism of the regular derived unit as its scalar, using H^0
and the canonical single-complex unit comparison. The value at 1 fixes the
identification with R, including for the zero ring.
Source: scalar target of the Complement (blueprint: sk-thm-sf-identification). -/
def identificationScalarValue {R : Type (u + 1)} [CommRing R]
    (f : End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)))) : R :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app _ ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((DerivedCategory.singleFunctorObjUnitIso (ModuleCat R)).hom ≫ f ≫
        (DerivedCategory.singleFunctorObjUnitIso (ModuleCat R)).inv) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app _).hom
      (1 : R)

/-- Perfectness of the degreewise form of the specified derived pairing, using
Mathlib's perfect bilinear pairing predicate. Hom from the regular unit to a
shifted scalar complex is its cohomology module. The equality fixes the bilinear
map to be the degreewise value of the given derived pairing.
Source: Complement (blueprint: sk-thm-sf-identification). -/
def IdentificationDegreewise {R : Type (u + 1)} [CommRing R]
    {P Q : DerivedCategory (ModuleCat.{u + 1} R)} (b : P ⊗ Q ⟶ 𝟙_ _) : Prop :=
  ∀ i : ℤ,
    ∃ B : (𝟙_ _ ⟶ P⟦i⟧) →ₗ[R] (𝟙_ _ ⟶ Q⟦-i⟧) →ₗ[R] R,
      (∀ (x : 𝟙_ _ ⟶ P⟦i⟧) (y : 𝟙_ _ ⟶ Q⟦-i⟧),
        B x y = identificationScalarValue (identificationDegreeValue b i x y)) ∧
      B.IsPerfPair

variable (ell : ℕ) [Fact ell.Prime]
  (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
  (Λ : ScalarSixRing.{u}) (c : PurityTransport.Coefficient ell)
  (e : c.bundled.{u} ell ≅ Λ)
  (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
  [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom)
  (K : ConstantModelConstructibleFiniteTor Λ.X X.left)

/-- The evaluation-normalized global duality pairing before purity, using the
counit of the same exceptional adjoint. Its transpose is inverse tensor--Hom
exchange at the coefficient unit; no separate global isomorphism is chosen.
Source: displayed canonical isomorphism (blueprint: sk-thm-sf-identification). -/
def identificationVerdierPairing
    (ω : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ.X X.left)))
    (ε : (rightDerivedLowerShriekOfCompactification Λ.X cf).obj ω ⟶ 𝟙_ _) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    (pairingCompactSections Λ.X D.k cf).obj K.obj ⊗
      (pairingOrdinarySections Λ.X D.k X.hom).obj ((ihom K.obj).obj ω) ⟶ 𝟙_ _ :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (pairingExactScalarPointCup Λ.X D.k).derived.μ _ _ ≫
    (CohomologyTransport.sections Λ.X (Spec (.of D.k))).mapDerivedCategory.map
      (pairingSheafCup Λ.X cf K.obj ((ihom K.obj).obj ω) ≫
        (rightDerivedLowerShriekOfCompactification Λ.X cf).map ((ihom.ev K.obj).app ω) ≫
          ε) ≫ (pairingExactScalarPointCup_unitIso Λ.X D.k).inv

/-- All clauses of the smooth identification, with canonical maps fixed by
trace and evaluation equations. The witnesses for membership only certify that
these very ambient objects belong to Dctf. The last clause uses complementary
Hom-from-unit cohomology, so Q[-i] is H^(2d-i) of the unshifted second factor.
Source: main assertion and Complement (blueprint: sk-thm-sf-identification). -/
def IdentificationAssertion : Prop :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  cohomologicalDimension ell (Fact.out : ell.Prime) (Spec (.of D.k)) = 0 ∧
  Nonempty (ScalarExceptionalAdjoint Λ cf) ∧
  ∃ hs : (constantModelBoundedConstructible Λ.X (Spec (.of D.k)) ⊓
      DerivedCategory.finiteTorAmplitude _) (𝟙_ _),
  ∀ R : ScalarExceptionalAdjoint Λ cf,
  ∃ γ : (smoothTraceCoefficientLine ell Λ c e X.left d) ⟦2 * (d : ℤ)⟧ ≅
      (R.upper.obj ⟨𝟙_ _, hs⟩).obj,
  ∃ j : (((ihom K.obj).obj (𝟙_ _) ⊗
      smoothTraceCoefficientLine ell Λ c e X.left d) ⟦2 * (d : ℤ)⟧) ≅
      (ihom K.obj).obj (R.upper.obj ⟨𝟙_ _, hs⟩).obj,
    (rightDerivedLowerShriekOfCompactification Λ.X cf).map γ.hom ≫
        R.counit ⟨𝟙_ _, hs⟩ =
      smoothTraceUnitOfCoefficientIso ell Λ c e D hEll (pairingSmoothDatum D X d cf) ∧
    K.obj ◁ j.hom ≫ (ihom.ev K.obj).app (R.upper.obj ⟨𝟙_ _, hs⟩).obj =
      ((tensorLeft K.obj).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
        (shiftFunctor _ (2 * (d : ℤ))).map
          (pairingTwistedEvaluation Λ.X K.obj
            (smoothTraceCoefficientLine ell Λ c e X.left d)) ≫ γ.hom ∧
    (constantModelBoundedConstructible Λ.X X.left ⊓ DerivedCategory.finiteTorAmplitude _)
      ((ihom K.obj).obj (𝟙_ _)) ∧
    (constantModelBoundedConstructible Λ.X X.left ⊓ DerivedCategory.finiteTorAmplitude _)
      ((ihom K.obj).obj (R.upper.obj ⟨𝟙_ _, hs⟩).obj) ∧
    (constantModelBoundedConstructible Λ.X X.left ⊓ DerivedCategory.finiteTorAmplitude _)
      ((smoothTraceCoefficientLine ell Λ c e X.left d) ⟦2 * (d : ℤ)⟧) ∧
    (constantModelBoundedConstructible Λ.X X.left ⊓ DerivedCategory.finiteTorAmplitude _)
      ((((ihom K.obj).obj (𝟙_ _)) ⊗ smoothTraceCoefficientLine ell Λ c e X.left d)
        ⟦2 * (d : ℤ)⟧) ∧
    (IsPerfectOnCoefficientSite Λ.X X.left K.obj →
      IsPerfectOnCoefficientSite Λ.X X.left ((ihom K.obj).obj (𝟙_ _)) ∧
        ∃ ep : ExactPairing ((ihom K.obj).obj (𝟙_ _)) K.obj,
          ep.evaluation' = (ihom.ev K.obj).app (𝟙_ _)) ∧
    DerivedCategory.IsPerfectRingComplex ((pairingCompactSections Λ.X D.k cf).obj K.obj) ∧
    DerivedCategory.IsPerfectRingComplex
      (((pairingOrdinarySections Λ.X D.k X.hom).obj
        ((ihom K.obj).obj (𝟙_ _) ⊗ smoothTraceCoefficientLine ell Λ c e X.left d))
          ⟦2 * (d : ℤ)⟧) ∧
    MonoidalClosed.IsPerfectPairing (identificationPairing ell D hEll Λ c e X d cf K) ∧
    (∀ hK : IsPerfectOnCoefficientSite Λ.X X.left K.obj,
      identificationPairing ell D hEll Λ c e X d cf K =
        derivedPoincarePairing ell D hEll Λ c e X d cf K hK) ∧
    ∃ g : (pairingOrdinarySections Λ.X D.k X.hom).obj
        ((ihom K.obj).obj (R.upper.obj ⟨𝟙_ _, hs⟩).obj) ≅
      (ihom ((pairingCompactSections Λ.X D.k cf).obj K.obj)).obj (𝟙_ _),
      g.hom = MonoidalClosed.curry
        (identificationVerdierPairing D Λ X cf K _ (R.counit ⟨𝟙_ _, hs⟩)) ∧
      MonoidalClosed.curry (identificationPairing ell D hEll Λ c e X d cf K) =
        ((pairingOrdinarySections Λ.X D.k X.hom).commShiftIso
          (2 * (d : ℤ))).inv.app _ ≫
          (pairingOrdinarySections Λ.X D.k X.hom).map j.hom ≫ g.hom ∧
      (IsProper X.hom →
        ∃ χ : (pairingOrdinarySections Λ.X D.k X.hom).obj K.obj ≅
            (pairingCompactSections Λ.X D.k cf).obj K.obj,
          MonoidalClosed.IsPerfectPairing
            (χ.hom ▷ _ ≫ identificationPairing ell D hEll Λ c e X d cf K)) ∧
      (IsProper X.hom → IsPerfectOnCoefficientSite Λ.X X.left K.obj →
        (∃ (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ), 1 ≤ n ∧
          Nonempty (Mon.mk Λ.X ≅ Mon.mk
            (IntegralModelsEmbedded.discreteObj (Padic.coefficientExtensionRing ell E n)))) →
        IdentificationDegreewise (identificationPairing ell D hEll Λ c e X d cf K))

end WeilConjectures.SixFunctors
