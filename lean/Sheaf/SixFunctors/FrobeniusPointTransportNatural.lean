/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.InverseImagePullbackComparisonDerived
import Sheaf.Paper.IsomorphismComparisonScalarExtension
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization

/-!
# Naturality of Frobenius point transport

Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151
(blueprint: lem-weil-frobenius-point-transport-natural).

The two sigma maps are linear and natural on the finite and completed integral
complex models used by `frobeniusPointFiniteSigma` and
`frobeniusPointIntegralSigma`, and they descend to natural transformations
`Γ(s, -) → Γ(s, g_s⁻¹ -)` on the derived categories (`frobeniusPointFiniteSigmaDerived`,
`frobeniusPointIntegralSigmaDerived`).  The point-transport components are natural
on the finite and integral constructible categories.  Rational components are obtained
by the recorded scalar-localization construction, and algebraically closed
components are represented at a finite coefficient stage; the final clauses
state the corresponding naturality and scalar-extension compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
set_option linter.defProp false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures


/-- The canonical object equality identifying rational pullback with the integral model.
Source: blueprint rational pullback object formula in
`def-weil-frobenius-point-transport`; proof postponed to the uniqueness theorem
for `rationalDerivedPullback`.
-/
theorem frobeniusPointRationalPullbackEq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
      fun x => frobeniusPointPrimeInvertible D l hl x
    (rationalDerivedPullback l E (frobeniusPointIso D).hom).obj N =
      frobeniusPointRationalPullbackObj D l hl E N := by
  sorry

/-- The canonical common-stage object equality for qbar pullback.
Source: blueprint common-stage pullback paragraph; proof postponed to the
specified common-stage uniqueness property.
-/
theorem frobeniusPointQbarPullbackEq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
      fun x => frobeniusPointPrimeInvertible D l hl x
    (commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj A =
      frobeniusPointQbarPullbackObj D l hl Ω A := by
  sorry

/-- The canonical object equality for the chosen qbar fibre functor.
Source: blueprint algebraically closed coefficient fibre construction; proof
postponed to `pointQbarFibre_existsUnique`.
-/
theorem frobeniusPointQbarFibreObjEq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    (pointQbarFibre D l hl Ω).obj A = pointQbarFibreObj D l hl Ω A := by
  sorry

/-- The derived finite sigma component `Γ(s, N) → Γ(s, g_s⁻¹ N)` on the unbounded
derived category, for the exact module inverse image `inverseImageFiniteDerived`
(no pullback comparison `κ`): conjugate the chain-level `frobeniusPointFiniteSigma`
of the localization's representative by the recorded factorization isomorphisms.
Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151; clause 1 of
(blueprint: lem-weil-frobenius-point-transport-natural). -/
noncomputable def frobeniusPointFiniteSigmaDerived
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))) :
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj N ⟶
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
        ((inverseImageFiniteDerived l E (frobeniusPointIso D).hom n).obj N) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      (DerivedCategory.Q.objObjPreimageIso N).inv ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.hom.app
      (DerivedCategory.Q.objPreimage N) ≫
    DerivedCategory.Q.map
      (frobeniusPointFiniteSigma D l E n (DerivedCategory.Q.objPreimage N)) ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.inv.app
      (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
        (.up ℤ)).obj (DerivedCategory.Q.objPreimage N)) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      ((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapDerivedCategoryFactors.inv.app
          (DerivedCategory.Q.objPreimage N) ≫
        (inverseImageFiniteDerived l E (frobeniusPointIso D).hom n).map
          (DerivedCategory.Q.objObjPreimageIso N).hom)

/-- The derived completed-integral sigma component `Γ(s, N) → Γ(s, g_s⁻¹ N)` on the
whole derived category, for the exact module inverse image
`inverseImageIntegralDerived` (no pullback comparison `κ`): conjugate the chain-level
`frobeniusPointIntegralSigma` of the localization's representative by the recorded
factorization isomorphisms.
Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151; clause 1 of
(blueprint: lem-weil-frobenius-point-transport-natural). -/
noncomputable def frobeniusPointIntegralSigmaDerived
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    (pointFibreIntegralAmbient D l E).obj N ⟶
      (pointFibreIntegralAmbient D l E).obj
        ((inverseImageIntegralDerived l E (frobeniusPointIso D).hom).obj N) :=
  (pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.objObjPreimageIso N).inv ≫
    (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app
      (DerivedCategory.Q.objPreimage N) ≫
    DerivedCategory.Q.map
      (frobeniusPointIntegralSigma D l E (DerivedCategory.Q.objPreimage N)) ≫
    (pointIntegralSections l E D.k).mapDerivedCategoryFactors.inv.app
      (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
        (.up ℤ)).obj (DerivedCategory.Q.objPreimage N)) ≫
    (pointFibreIntegralAmbient D l E).map
      ((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapDerivedCategoryFactors.inv.app
          (DerivedCategory.Q.objPreimage N) ≫
        (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).map
          (DerivedCategory.Q.objObjPreimageIso N).hom)

/--
The point transport along Frobenius is linear and natural.
Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151
(blueprint: lem-weil-frobenius-point-transport-natural).

Proof steps (postponed at stage 2):
1. Identify the distinguished comma-object coprojection with restriction along
   geometric Frobenius by the inverse-image evaluation isomorphism.
2. Check additivity and both coefficient actions on finite and completed integral
   sections, including the comparison `c_Λ`.
3. Check chain-map naturality of restriction and pass it through the sections and
   inverse-image functors.
4. Apply exactness of sections and of the module inverse image to descend that
   equality through the derived localization (the derived sigma components).
5. Compose the naturality square for `κ` with the square for `σ` at finite level.
6. Use the normalized completed pullback comparison to obtain the integral square.
7. Localize the integral square and use `rationalDerivedPullback`, with its
   canonical object equalities, for the rational square.
8. Represent every qbar morphism over a common finite stage and use
   `commonStageDerivedPullback`; canonical eqToHom maps identify all four fibre
   objects in the displayed square.
9. For every coefficient extension E' ⊂ L, use the fibre-level
   `pointRationalSectionsScalarExtensionIso` and the normalized
   `rationalPullbackScalarComparison` to identify scalar-extended transport with
   the L-stage map;
   coherence under a further extension makes the result independent of the stage.
-/
theorem frobeniusPointTransport_natural
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    (∀ (n : ℕ)
      (K : CochainComplex
        (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
      (i : ℤ)
      (a : ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))
      (x : ModuleCat.carrier
        ((((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
            (.up ℤ)).obj K).X i)),
      (ConcreteCategory.hom
        ((frobeniusPointFiniteSigma D l E n K).f i)) (a • x) =
        a • (ConcreteCategory.hom
          ((frobeniusPointFiniteSigma D l E n K).f i)) x) ∧
    (∀ (n : ℕ)
      (K K' : CochainComplex
        (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
      (f : K ⟶ K'),
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
          (.up ℤ)).map f ≫
          frobeniusPointFiniteSigma D l E n K' =
        frobeniusPointFiniteSigma D l E n K ≫
          ((pointFiniteSections D.k
            (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
              (.up ℤ)).map
            (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
              (.up ℤ)).map f)) ∧
    (∀ (n : ℕ)
      (K K' : CochainComplex
        (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
      (f : K ⟶ K'),
      DerivedCategory.Q.map
        (((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
            (.up ℤ)).map f ≫
          frobeniusPointFiniteSigma D l E n K') =
        DerivedCategory.Q.map
          (frobeniusPointFiniteSigma D l E n K ≫
            ((pointFiniteSections D.k
              (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
                (.up ℤ)).map
              (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
                (.up ℤ)).map f))) ∧
    (∀ (n : ℕ)
      (N M : proEtaleDerivedCategory (Spec (.of D.k))
        (Padic.coefficientExtensionRing l E (n + 1)))
      (f : N ⟶ M),
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map f ≫
        frobeniusPointFiniteSigmaDerived D l E n M =
      frobeniusPointFiniteSigmaDerived D l E n N ≫
        (pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
          ((inverseImageFiniteDerived l E (frobeniusPointIso D).hom n).map f)) ∧
    (∀ (K : CochainComplex
      (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (i : ℤ)
      (a : ULift.{u + 1, u}
        (Padic.coefficientExtensionIntegers l E))
      (x : ModuleCat.carrier
        ((((pointIntegralSections l E D.k).mapHomologicalComplex
            (.up ℤ)).obj K).X i)),
      (ConcreteCategory.hom
        ((frobeniusPointIntegralSigma D l E K).f i)) (a • x) =
        a • (ConcreteCategory.hom
          ((frobeniusPointIntegralSigma D l E K).f i)) x) ∧
    (∀ (K K' : CochainComplex
      (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (f : K ⟶ K'),
      ((pointIntegralSections l E D.k).mapHomologicalComplex
          (.up ℤ)).map f ≫ frobeniusPointIntegralSigma D l E K' =
        frobeniusPointIntegralSigma D l E K ≫
          ((pointIntegralSections l E D.k).mapHomologicalComplex
              (.up ℤ)).map
            (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
              (.up ℤ)).map f)) ∧
    (∀ (K K' : CochainComplex
      (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (f : K ⟶ K'),
      DerivedCategory.Q.map
        (((pointIntegralSections l E D.k).mapHomologicalComplex
          (.up ℤ)).map f ≫ frobeniusPointIntegralSigma D l E K') =
        DerivedCategory.Q.map
          (frobeniusPointIntegralSigma D l E K ≫
            ((pointIntegralSections l E D.k).mapHomologicalComplex
              (.up ℤ)).map
            (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
              (.up ℤ)).map f))) ∧
    (∀ (N M : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
      (f : N ⟶ M),
      (pointFibreIntegralAmbient D l E).map f ≫
        frobeniusPointIntegralSigmaDerived D l E M =
      frobeniusPointIntegralSigmaDerived D l E N ≫
        (pointFibreIntegralAmbient D l E).map
          ((inverseImageIntegralDerived l E (frobeniusPointIso D).hom).map f)) ∧
    (∀ (n : ℕ)
      (N M : (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))
        (Spec (.of D.k))).FullSubcategory)
      (u : N ⟶ M),
      (pointFiniteFibre D l hl E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n))).map u ≫
          frobeniusPointTransportFiniteConstructible D l hl E n M =
        frobeniusPointTransportFiniteConstructible D l hl E n N ≫
          (pointFiniteFibre D l hl E (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n))).map
            ((frobeniusPointFinitePullback D l hl E n).map u)) ∧
    (∀ (N M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
      (u : N ⟶ M),
      (pointIntegralFibre D l hl E).map u ≫
          frobeniusPointTransportIntegralConstructible D l hl E M =
        frobeniusPointTransportIntegralConstructible D l hl E N ≫
          (pointIntegralFibre D l hl E).map
            ((frobeniusPointIntegralPullback D l hl E).map u)) ∧
    (∀ (N M : sfRationalConstructibleCategory l E (Spec (.of D.k)))
      (u : N ⟶ M),
      letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
        fun x => frobeniusPointPrimeInvertible D l hl x
      (pointRationalFibre D l hl E).map u ≫
          frobeniusPointTransportRational D l hl E M =
        frobeniusPointTransportRational D l hl E N ≫
          (pointRationalFibre D l hl E).map
            (eqToHom (frobeniusPointRationalPullbackEq D l hl E N).symm ≫
              (rationalDerivedPullback l E (frobeniusPointIso D).hom).map u ≫
              eqToHom (frobeniusPointRationalPullbackEq D l hl E M))) ∧
    (∀ (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
      [IsAlgClosure ℚ_[l] Ω]
      (A B : generalAlgebraicallyClosedConstructibleCategory l Ω
        (Spec (.of D.k)))
      (u : A ⟶ B),
      letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
        fun x => frobeniusPointPrimeInvertible D l hl x
      (eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω A).symm ≫
          (pointQbarFibre D l hl Ω).map u ≫
          eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω B)) ≫
          frobeniusPointTransportQbar D l hl Ω B =
        frobeniusPointTransportQbar D l hl Ω A ≫
          (eqToHom (congrArg (pointQbarFibreObj D l hl Ω)
              (frobeniusPointQbarPullbackEq D l hl Ω A).symm) ≫
            eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω
              ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj A)).symm ≫
            (pointQbarFibre D l hl Ω).map
              ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).map u) ≫
            eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω
              ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj B)) ≫
            eqToHom (congrArg (pointQbarFibreObj D l hl Ω)
              (frobeniusPointQbarPullbackEq D l hl Ω B)))) ∧
    (∀ (E' L : Type u) [Field E'] [Algebra ℚ_[l] E']
      [FiniteDimensional ℚ_[l] E'] [Field L] [Algebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] (ι : E' →ₐ[ℚ_[l]] L)
      (K : sfRationalConstructibleCategory l E' (Spec (.of D.k))),
      letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
        fun x => frobeniusPointPrimeInvertible D l hl x
      (pointRationalFibreScalarIso D l hl E' L ι).inv.app K ≫
          frobeniusPointTransportRational D l hl L
            ((sfRationalScalarExtension l E' (Spec (.of D.k)) 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) ≫
          (pointRationalFibre D l hl L).map
            (eqToHom (frobeniusPointRationalPullbackEq D l hl L
              ((sfRationalScalarExtension l E' (Spec (.of D.k)) 0
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K)).symm) ≫
          (pointRationalFibre D l hl L).map
            ((rationalPullbackScalarComparison l E' L ι
              (frobeniusPointIso D).hom).inv.app K) ≫
          (pointRationalFibreScalarIso D l hl E' L ι).hom.app
            ((rationalDerivedPullback l E' (frobeniusPointIso D).hom).obj K) =
        (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
          (frobeniusPointTransportRational D l hl E' K) ≫
          (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
            ((pointRationalFibre D l hl E').map
              (eqToHom (frobeniusPointRationalPullbackEq D l hl E' K).symm))) := by
  sorry

end WeilConjectures
