/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.CompactSupportCondensedRealization
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportUniformRestriction
public import WeilConjectures.SixFunctors.OpenTensorNormalization
public import WeilConjectures.SixFunctors.IntegralOpenReductionComparison
public import WeilConjectures.AlgebraicGeometry.CondensedERealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.AlgebraicGeometry.CondensedCompactSupportProjection
public import WeilConjectures.AlgebraicGeometry.CompactSupportRealizationFactorNormalization
public import WeilConjectures.AlgebraicGeometry.CompactSupportRealizationIdentity
public import WeilConjectures.SixFunctors.IntegralSystemOperations
public import WeilConjectures.SixFunctors.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.GeneratorReductionStatement
public import WeilConjectures.AlgebraicGeometry.CompletedCoefficientPresentationTransport
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.SemilinearCompactSupportCoefficientTransport
import all WeilConjectures.SixFunctors.OpenReconstructionEffectivity

/-! # Compact-support realization factorization over an arbitrary field

Source: Bhatt--Scholze, Definition 6.7.6, Lemma 6.7.7, Proposition 6.8.14(2),
Remark 6.8.15 (context only); the specified compact-support construction,
Steps 2--5, 6 and 13, and current blueprint sk-thm-purity-transport, Steps 2--3.
(blueprint: lem-pur-compact-support-realization-factorization).

The existing factor-normalization module supplies the actual proper counit and open
unit mates, without any restriction on the base field in those definitions. Here the
reconstruction comparison is placed directly in the parent's strict-tower coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Sheaf.monoidalCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures IntegralSystemRealization CompactSupportFactorNormalization
open scoped CategoryTheory.Obj

namespace WeilConjectures.CompactSupportRealizationFactorization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The proper counit mate followed by the inverse open-unit mate, transported by
identity on the underlying simultaneous systems to the parent's presentation.
Source: node proof Step 2, compact-support construction Step 2
(blueprint: lem-pur-compact-support-realization-factorization). -/
def rho (o : Operations l E) (m : RealizationModel l E o) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : Integral l E X) :=
  systemComparison l E o m c K ≫ (systemPresentation l E o b c).hom.app
    ((calculus l E X).reduction.obj K)

/-- The actual unit followed by total limit of rho and the inverse canonical
strict-tower presentation. Source: node proof Steps 3--4
(blueprint: lem-pur-compact-support-realization-factorization). -/
def q (o : Operations l E) (m : RealizationModel l E o) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : CompactSupportCondensedRealization.IntegralModel l E c (calculus l E))
    (K : CondensedERealization.Integral l E X) :=
  (calculus l E Y).adjunction.unit.app
      ((word l E c).obj ((purCoefficientModel l E X).functor.obj K.obj)) ≫
    (coefficientSequenceLimit l E Y).map
      (rho l E o m b c ((purCoefficientModel l E X).functor.obj K.obj)) ≫
    (CompactSupportCondensedRealization.limitPresentation l E c (calculus l E) M).inv.app K

/-- The three specified factors of a, with the section and lattice presentation
isomorphisms explicitly inserted. Source: node proof Step 6
(blueprint: lem-pur-compact-support-realization-factorization). -/
def realizedFactorization (o : Operations l E) (m : RealizationModel l E o)
    (b : CanonicalBridge l E o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (M : CompactSupportCondensedRealization.IntegralModel l E c (calculus l E))
    (AX : CondensedERealization.At l E X) (AZ : CondensedERealization.At l E c.Z)
    (AY : CondensedERealization.At l E Y) (K : CondensedERealization.Integral l E X) :=
  (latticeComparison l E Y AY).inv.app
      ((CompactSupportCondensedRealization.integralSupport l E c (calculus l E) M).obj K) ≫
    (realize l E Y AY).map (GeneratorReduction.inverseOrZero (q l E o m b c M K)) ≫
    (properRealization l E c.g AZ AY).app
      ((ringedOpen l E c.i).obj ((purCoefficientModel l E X).functor.obj K.obj)) ≫
    (CondensedRing.lowerStar
      (Profinite.continuousCoefficientRingObj E) c.g).rightDerivedFunctor.map
        (openRealization l E c.i AX AZ ((purCoefficientModel l E X).functor.obj K.obj)) ≫
    (CondensedRing.rightDerivedLowerShriekOfCompactification
      (Profinite.continuousCoefficientRingObj E) c).map
        ((latticeComparison l E X AX).hom.app K)

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- Transport only the parent's chosen reduction presentation, without changing any
of its comparison components. Source: node proof Step 3
(blueprint: lem-pur-compact-support-realization-factorization). -/
def atNormalized (C : CompactSupportCondensedRealization.ComparisonFamily l k)
    (h : (C.coefficient E).reduction = calculus l E)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f) :
    CompactSupportCondensedRealization.RealizationAt l E k
      (C.coefficient E).realization (calculus l E) X Y f c :=
  h ▸ (C.coefficient E).atCompactification X Y f c

/-- Every integral object, with no extra Tor or geometric-field hypothesis, has the
specified reconstruction and realization factorization. Equalities are in the whole
derived system or internal-module category. Source: node proof Steps 1--6 and 8
(blueprint: lem-pur-compact-support-realization-factorization). -/
def IsFactorized (C : CompactSupportCondensedRealization.ComparisonFamily l k) : Prop :=
  ∀ (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F],
    ∃ h : (C.coefficient F).reduction = calculus l F,
      (∃ o : Operations l F, Nonempty (RealizationModel l F o) ∧
        Nonempty (CanonicalBridge l F o)) ∧
      ∀ (o : Operations l F) (m : RealizationModel l F o) (b : CanonicalBridge l F o)
        (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
        [f.IsOver (Spec (.of k))] (c : Compactification f)
        (AZ : CondensedERealization.At l F c.Z) (K : CondensedERealization.Integral l F X.scheme),
        IsIso (q l F o m b c (atNormalized l F k C h X Y f c).integral K) ∧
        (calculus l F Y.scheme).reduction.map
            (q l F o m b c (atNormalized l F k C h X Y f c).integral K) ≫
          (CompactSupportCondensedRealization.alpha l F c (calculus l F)
            (atNormalized l F k C h X Y f c).integral).app K =
          rho l F o m b c ((purCoefficientModel l F X.scheme).functor.obj K.obj) ∧
        IsIso ((properRealization l F c.g AZ
          ((C.coefficient F).realization.atObject Y)).app
            ((ringedOpen l F c.i).obj ((purCoefficientModel l F X.scheme).functor.obj K.obj))) ∧
        IsIso ((openRealizationInverse l F c.i
          ((C.coefficient F).realization.atObject X) AZ).app
            ((purCoefficientModel l F X.scheme).functor.obj K.obj)) ∧
        (atNormalized l F k C h X Y f c).realization.hom.app (ScalarLocalization.mk K) =
          realizedFactorization l F o m b c (atNormalized l F k C h X Y f c).integral
            ((C.coefficient F).realization.atObject X) AZ
            ((C.coefficient F).realization.atObject Y) K

/-- Factorization of the specified compact-support reconstruction over any field of
positive characteristic distinct from l. Source: compact-support construction,
Steps 2--5, 6 and 13; blueprint sk-thm-purity-transport, Steps 2--3
(blueprint: lem-pur-compact-support-realization-factorization).
Proof:
1. Finite type over k makes X, Y and the proper compactification Z noetherian of
finite dimension; opens of Z are quasi-compact. The distinct prime is invertible.
Integral compact support preserves the recorded complete uniform categories.
2. Form rho on the derived ringed sequence site: its proper factor is the transpose
of scalar balancing followed by the counit; its open factor is the inverse open-unit
adjunct. Proper projection and normalized open tensor make both finite evaluations
invertible; joint conservativity makes rho invertible as a whole-system map.
3. The strict tower identifies P_R with the total limit of the system composite.
The specified alpha is the reduction/limit counit in these coordinates. Completeness
makes the actual unit invertible; hence q=L(rho)u is invertible.
4. Counit naturality gives e R L(rho)=rho e. Compose with R(u), and use the left
triangle identity to obtain alpha R(q)=rho before any evaluation.
5. For identity proper image the counit mate is identity under its unitors, leaving
the strict open reduction comparison and its inverse-unit reconstruction.
6. Construct the parent's specified a by applying scalar realization to inverse q,
then its counit-compatible proper comparison and its open-unit-normalized comparison.
This is exactly realizedFactorization, including the fixed lattice presentations.
7. The specified xi is the original proper/open coefficient paste. This construction
also uses the finite-extension-valued Omega ring and needs no colimit interchange.
8. Identity proper adjunctions make their proper factors identities. Naturality of
each unit, counit, scalar comparison and inverse gives all naturality equations. -/
theorem compactSupport_realization_factorization :
    ∃ C : CompactSupportCondensedRealization.ComparisonFamily l k, IsFactorized l k C := by
  sorry

end WeilConjectures.CompactSupportRealizationFactorization

namespace WeilConjectures.CompactSupportRealizationFactorization
open CompactSupportCondensedRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The condensed proper identity unitor is conjugate to the original inverse-image
identity, retaining its adjunction counit. Source: node proof Step 8
(blueprint: lem-pur-compact-support-realization-factorization). -/
def fieldPushId
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ] (W : Scheme.{u}) :
    (CondensedRing.lowerStar Λ (𝟙 W)).rightDerivedFunctor ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (𝟙 W))
    (CondensedRing.leftDerivedUpperStarId Λ W)).symm

/-- With identity proper factor, rho is exactly the normalized open reduction
comparison, in the simultaneous-system presentation. Source: node proof Step 5
(blueprint: lem-pur-compact-support-realization-factorization).
Proof: the proper scalar mate becomes identity under the canonical proper unitors.
The remaining map is inverse openReduction, whose definition is the open-unit
adjunct of the scalar balancing square. IntegralOpenReductionComparison constructs
r_j by the same strict K-flat augmentation and the same open-unit normalization;
therefore this is its system arrow, including all quotient transitions. -/
theorem identityProperReduction (o : Operations l E) (m : RealizationModel l E o)
    (b : CanonicalBridge l E o) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : CondensedERealization.Integral l E X) :
    IsIso ((m.openReduction l E j).app ((purCoefficientModel l E X).functor.obj K.obj)) ∧
    rho l E o m b (Compactification.ofIsOpenImmersion j)
        ((purCoefficientModel l E X).functor.obj K.obj) ≫
      (Functor.isoWhiskerLeft (ProEtale.SemilinearProperOpen.J
        (quotientRings l E) (quotientMaps l E) j)
        (ProEtale.SemilinearProperOpen.sId (quotientRings l E) (quotientMaps l E) Y)).hom.app
          ((calculus l E X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj)) =
      (calculus l E Y).reduction.map ((integralPushId l E Y).hom.app
          ((ringedOpen l E j).obj ((purCoefficientModel l E X).functor.obj K.obj))) ≫
        GeneratorReduction.inverseOrZero ((m.openReduction l E j).app
          ((purCoefficientModel l E X).functor.obj K.obj)) ≫
        (b.shriek l E j).hom.app
          ((calculus l E X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj)) := by
  sorry

/-- The proper factor of J becomes identity under the canonical direct-image unitors.
Source: node proof Step 8
(blueprint: lem-pur-compact-support-realization-factorization).
Proof: transpose both sides under the proper adjunction. The identity pullback
unitor and the section-normalized restriction square turn the two transposes into
the same scalar identity followed by the proper counit. Adjunction injectivity gives
the equation on the actual internal-module derived category. -/
theorem identityProperRealization (W : Scheme.{u}) (A : CondensedERealization.At l E W)
    (K : Integral l E W) :
    (properRealization l E (𝟙 W) A A).app K ≫
        (fieldPushId (Profinite.continuousCoefficientRingObj E) W).hom.app
          ((realize l E W A).obj K) =
      (realize l E W A).map ((integralPushId l E W).hom.app K) := by
  sorry

/-- Coefficient projection factorization, including the finite-extension-valued
algebraic-closure ring. Source: compact-support construction Steps 6 and 13;
node proof Step 7 (blueprint: lem-pur-compact-support-realization-factorization).
Proof: unfold the specified condensedProjection, which pastes derivedPushHom with
derivedOpenImmersionShriekIso. Their functor associators have identity components.
The former is the proper counit mate and the inverse of the latter is the open-unit
adjunct. This applies unchanged to omegaMap, whose sections have values in one
finite extension, rather than to an unrestricted continuous-function ring. -/
theorem coefficientFactorization
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (D : CondensedERealization.Data l E k)
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Integral l E X.scheme) :
    (condensedProjection (fieldMap l E F i) c).app
        (((D.atObject X).realization.functor.obj (ScalarLocalization.mk K)).obj) =
      (CondensedRing.derivedPushHom (fieldMap l E F i) c.g).app
        ((CondensedRing.openImmersionLowerShriek (Profinite.continuousCoefficientRingObj E)
          c.i).mapDerivedCategory.obj
            (((D.atObject X).realization.functor.obj (ScalarLocalization.mk K)).obj)) ≫
      (CondensedRing.lowerStar
        (Profinite.continuousCoefficientRingObj F) c.g).rightDerivedFunctor.map
          ((CondensedRing.derivedOpenImmersionShriekIso (fieldMap l E F i) c.i).hom.app
            (((D.atObject X).realization.functor.obj (ScalarLocalization.mk K)).obj)) ∧
    (condensedProjection (omegaMap l E a) c).app
        (((D.atObject X).realization.functor.obj (ScalarLocalization.mk K)).obj) =
      (CondensedRing.derivedPushHom (omegaMap l E a) c.g).app
        ((CondensedRing.openImmersionLowerShriek (Profinite.continuousCoefficientRingObj E)
          c.i).mapDerivedCategory.obj
            (((D.atObject X).realization.functor.obj (ScalarLocalization.mk K)).obj)) ≫
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) c.g).rightDerivedFunctor.map
        ((CondensedRing.derivedOpenImmersionShriekIso (omegaMap l E a) c.i).hom.app
          (((D.atObject X).realization.functor.obj (ScalarLocalization.mk K)).obj)) := by
  constructor
  · exact CompactSupportFactorNormalization.coefficient_factorization (fieldMap l E F i) c _
  · exact CompactSupportFactorNormalization.coefficient_factorization (omegaMap l E a) c _

/-- The proper coefficient mate for identity direct image is identity under its
canonical unitors, for finite extensions and for Omega. Source: node proof Step 8
(blueprint: lem-pur-compact-support-realization-factorization).
Proof: the proper scalar mate transposes scalar balancing followed by the counit.
The identity pullback unitors identify balancing with identity. The proper triangle
identity then identifies the transpose with the displayed scalar image of the
source proper unitor. The proof is the same for the finite-valued closure ring. -/
theorem identityProperCoefficient
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) (a : E →ₐ[ℚ_[l]] PadicAlgCl l) (W : Scheme.{u})
    (K : CondensedERealization.Constructible E W) :
    (CondensedRing.derivedPushHom (fieldMap l E F i) (𝟙 W)).app K.obj ≫
        (fieldPushId (Profinite.continuousCoefficientRingObj F) W).hom.app
          ((condensedScalar (fieldMap l E F i) W).obj K.obj) =
      (condensedScalar (fieldMap l E F i) W).map
        ((fieldPushId (Profinite.continuousCoefficientRingObj E) W).hom.app K.obj) ∧
    (CondensedRing.derivedPushHom (omegaMap l E a) (𝟙 W)).app K.obj ≫
        (fieldPushId (Profinite.padicAlgClRingObj l) W).hom.app
          ((condensedScalar (omegaMap l E a) W).obj K.obj) =
      (condensedScalar (omegaMap l E a) W).map
        ((fieldPushId (Profinite.continuousCoefficientRingObj E) W).hom.app K.obj) := by
  sorry

private def rhoTransformation (o : Operations l E) (m : RealizationModel l E o)
    (b : CanonicalBridge l E o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    word l E c ⋙ (calculus l E Y).reduction ⟶
      (calculus l E X).reduction ⋙ systemSupport l E c := by
  let (D : Integral l E X) : IsIso ((m.openReduction l E c.i).app D) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o m c.i D
  let : IsIso (m.openReduction l E c.i) := NatIso.isIso_of_isIso_app _
  let proper : ringedPush l E c.g ⋙ (calculus l E Y).reduction ⟶
      (calculus l E c.Z).reduction ⋙ Operations.push l E o c.g :=
    Functor.whiskerRight
      (Functor.whiskerRight (calculus l E c.Z).adjunction.unit (ringedPush l E c.g) ≫
        Functor.whiskerLeft (calculus l E c.Z).reduction (m.push l E c.g).inv)
      (calculus l E Y).reduction ≫
    Functor.whiskerLeft ((calculus l E c.Z).reduction ⋙ Operations.push l E o c.g)
      (calculus l E Y).adjunction.counit
  exact Functor.whiskerLeft (ringedOpen l E c.i) proper ≫
    Functor.whiskerRight (inv (m.openReduction l E c.i)) (Operations.push l E o c.g) ≫
    Functor.whiskerLeft (calculus l E X).reduction (systemPresentation l E o b c).hom

private theorem rhoTransformation_app (o : Operations l E) (m : RealizationModel l E o)
    (b : CanonicalBridge l E o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : Integral l E X) :
    (rhoTransformation l E o m b c).app K = rho l E o m b c K := by
  let (D : Integral l E X) : IsIso ((m.openReduction l E c.i).app D) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o m c.i D
  simp only [rhoTransformation, rho, systemComparison, properReduction,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatIso.isIso_inv_app, GeneratorReduction.inverseOrZero, dif_pos, Functor.comp_obj,
    Category.assoc]

private def qTransformation (o : Operations l E) (m : RealizationModel l E o)
    (b : CanonicalBridge l E o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : IntegralModel l E c (calculus l E)) :
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
        (purCoefficientModel l E X).functor ⋙ word l E c ⟶
      integralSupport l E c (calculus l E) M ⋙
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)) ⋙
          (purCoefficientModel l E Y).functor :=
  Functor.whiskerLeft
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
        (purCoefficientModel l E X).functor ⋙ word l E c)
      (calculus l E Y).adjunction.unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft
        (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
          (purCoefficientModel l E X).functor) (rhoTransformation l E o m b c))
      (coefficientSequenceLimit l E Y) ≫
    (limitPresentation l E c (calculus l E) M).inv

/-- Naturality of the specified integral reconstruction, in the actual parent
coordinates. Source: node proof Step 8
(blueprint: lem-pur-compact-support-realization-factorization).
Proof: proper and open mates are natural, and the bridge is a natural isomorphism.
Functoriality of total limit and naturality of its actual unit give naturality of
L(rho)u; the final strict-tower presentation is natural as well. -/
theorem q_naturality (o : Operations l E) (m : RealizationModel l E o)
    (b : CanonicalBridge l E o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : IntegralModel l E c (calculus l E))
    (K K' : CondensedERealization.Integral l E X) (v : K ⟶ K') :
    (word l E c).map ((purCoefficientModel l E X).functor.map v.hom) ≫ q l E o m b c M K' =
      q l E o m b c M K ≫ (purCoefficientModel l E Y).functor.map
        (((integralSupport l E c (calculus l E) M).map v).hom) := by
  simpa only [qTransformation, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, rhoTransformation_app, Functor.comp_map,
    ObjectProperty.ι_map, Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc, q]
    using (qTransformation l E o m b c M).naturality v

end WeilConjectures.CompactSupportRealizationFactorization
