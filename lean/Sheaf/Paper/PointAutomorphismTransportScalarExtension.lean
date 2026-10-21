/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module
import Mathlib.Algebra.CharP.CharAndCard
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.IsomorphismComparisonScalarExtension
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.IsomorphismScalarTensorKFlatModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.CoefficientComplexRationalization

/-! # Point-automorphism transport and completed coefficient extension

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension).

All definitions below are applications, scalar unliftings, or composites of recorded canonical
maps. The integral coefficients remain the completed coefficient sheaf. The theorem declarations
state the integral, rational, identity and tower clauses and the required prime-invertibility
input; all their proofs are postponed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The coefficient prime is a unit in every stalk of the geometric point. This supplies
an existing comparison input from the finite-field hypotheses, rather than assuming it.

Source: the finite-field conventions, blueprint order 411, and the coefficient convention
l different from p (blueprint: lem-weil-point-automorphism-transport-scalar-extension).

Proof: the cardinality of k_0 and primality of p identify its characteristic with p
(charP_of_card_eq_prime_pow). A distinct prime l is nonzero in k_0 and hence is a unit
(CharP.cast_ne_zero_of_ne_of_prime). Map this unit through the inclusion k_0 into k,
then through the inverse of Gamma(Spec k)=k and the germ at each x. Ring homomorphisms
preserve units and natural-number casts, giving the stated unit in every stalk. -/
theorem pointTransportPrimeUnits (_hl : l ≠ D.p) :
    ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x) := by
  sorry

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]

/-- The recorded restriction/coprojection map, with the canonical coefficient unlift. The chosen
module transformation is fixed by equality on every section in
point_automorphism_restriction_natural; no arbitrary transformation is selected.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointAutomorphismRestrictionModules :
    pointCompletedSections D.k l E ⟶
      inverseImageIntegralModules l E g ⋙ pointCompletedSections D.k l E :=
  Functor.whiskerRight
    (point_automorphism_restriction_natural l E D hl g none).2.2.choose
    (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E) ≃+* _).symm.toRingHom)

/-- The same restriction transformation localized termwise on all complexes, followed by the
canonical exact-functor composition comparison. This has exactly the endpoints Gamma and G
followed by Gamma. Localization uniquely determines it from the module transformation; no
constructibility hypothesis is imposed.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointAutomorphismRestrictionDerived :
    pointCompletedDerivedSections D.k l E ⟶
      inverseImageIntegralDerived l E g ⋙ pointCompletedDerivedSections D.k l E :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    ((pointCompletedSections D.k l E).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((Functor.mapHomologicalComplex
      (inverseImageIntegralModules l E g ⋙ pointCompletedSections D.k l E) (.up ℤ)) ⋙
        DerivedCategory.Q)
    (pointCompletedDerivedSections D.k l E)
    (inverseImageIntegralModules l E g ⋙ pointCompletedSections D.k l E).mapDerivedCategory
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (pointAutomorphismRestrictionModules D l hl E g) (.up ℤ))
      DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
      (pointCompletedSections D.k l E)).hom


/-- The specified integral kappa at the geometric point, with its prime-invertibility inputs
supplied by the finite-field datum. This is a direct application of
inverseImagePullbackComparisonDerived, retaining its chosen K-flat quotient-cone construction.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportKappa (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :=
  inverseImagePullbackComparisonDerived l E g (pointTransportPrimeUnits D l hl)
    (pointTransportPrimeUnits D l hl) K

/-- The point transport t is restriction sigma followed by sections of the specified kappa. It is
defined on each object; no naturality of this composite is asserted.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransport (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :=
  (pointAutomorphismRestrictionDerived D l hl E g).app K ≫
    (pointCompletedDerivedSections D.k l E).map (pointTransportKappa D l hl E g K)

set_option linter.defProp false in
/-- The recorded isomorphism-pullback admissibility assertion for G_E K, specialized to the
geometric point. This is an existing proof projection, not a new constructibility assumption.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportInverseConstructible
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (isomorphismComparisonInputs_constructible l E g (pointTransportPrimeUnits D l hl)
    (pointTransportPrimeUnits D l hl) K hK).1

set_option linter.defProp false in
/-- The recorded isomorphism-pullback admissibility assertion for P_E K, specialized to the
geometric point. Its completeness component is used in the specified scalar-pullback comparison.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportPullbackConstructible
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (isomorphismComparisonInputs_constructible l E g (pointTransportPrimeUnits D l hl)
    (pointTransportPrimeUnits D l hl) K hK).2

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The existing sections isomorphism phi, with the intrinsic constructibility predicate converted
by pointIntegralConstructible_iff. Its definition is exactly the inverse of Gamma(chi) after
theta.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportPhi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  pointSectionsScalarExtensionIso l E L ι D hl K
    ((pointIntegralConstructible_iff l E D hl K).mpr hK)

/-- The specified beta packaged as an isomorphism: chi at G_E K inverse, then the existing derived
tensor comparison b, then G_L applied to chi at K. Its hom is definitionally
isomorphismComparisonScalarBeta. The scalarCompletion comparison is identified with the recorded
universal chi by isomorphismScalarModel_existsUnique.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportBetaIso
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (scalarCompletionIso l E L ι (Spec (.of D.k)) _
    (pointTransportInverseConstructible D l hl E g K hK).1).symm ≪≫
    (isomorphismScalarTensorDerived l E L ι g).app K ≪≫
    (inverseImageIntegralDerived l L g).mapIso
      (scalarCompletionIso l E L ι (Spec (.of D.k)) K hK.1)

/-- The specified completed pullback/scalar isomorphism alpha. It is precisely
scalarPullbackCompleted; its hom is definitionally isomorphismComparisonScalarAlpha. The
admissibility input comes from the recorded isomorphism-derived-pullback assertion.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportAlphaIso
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  scalarPullbackCompleted l E L ι g K hK.1
    (pointTransportPullbackConstructible D l hl E g K hK).1

/-- The comparison psi = phi at G_E K after Gamma(beta inverse), using only the named canonical
maps.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportPsi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (pointCompletedDerivedSections D.k l L).map (pointTransportBetaIso D l hl E g L ι K hK).inv ≫
    (pointTransportPhi D l hl E L ι _
      (pointTransportInverseConstructible D l hl E g K hK)).hom

/-- The pullback sections comparison psi prime = phi at P_E K after Gamma(alpha inverse), using the
specified scalar-operation comparison.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportPullbackPsi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (pointCompletedDerivedSections D.k l L).map (pointTransportAlphaIso D l hl E g L ι K hK).inv ≫
    (pointTransportPhi D l hl E L ι _
      (pointTransportPullbackConstructible D l hl E g K hK)).hom


/-- The existing rational sections comparison: integral phi tensored with L and then the canonical
balanced localization map. No idempotent completion is introduced.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportRationalPhi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  pointRationalSectionsScalarExtensionIso l E L ι D hl K
    ((pointIntegralConstructible_iff l E D hl K).mpr hK)

/-- Rationalize psi and apply the canonical module tensor/rationalization associator at Gamma(G_E
K).

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportRationalPsi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (pointModuleDerivedRationalization l L).map (pointTransportPsi D l hl E g L ι K hK) ≫
    (pointDerivedTensorRationalization l E L ι).hom.app
      ((pointCompletedDerivedSections D.k l E).obj ((inverseImageIntegralDerived l E g).obj K))

/-- Rationalize psi prime and apply the canonical module tensor/rationalization associator at
Gamma(P_E K). This is the pullback comparison for raw rationalization.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportRationalPullbackPsi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (pointModuleDerivedRationalization l L).map (pointTransportPullbackPsi D l hl E g L ι K hK) ≫
    (pointDerivedTensorRationalization l E L ι).hom.app
      ((pointCompletedDerivedSections D.k l E).obj ((integralDerivedPullback l E g).obj K))

/-- Restriction and specified pullback transport commute with completed scalar extension; tensoring
the second equation gives the raw rationalized compatibility.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension).

Proof:
1. The isomorphism-derived-pullback theorem makes G_E K and P_E K constructible and complete.
The finite-free completed scalar comparison and the point-sections scalar comparison therefore
apply to K and both these objects. Put eta_H = Gamma(chi_H) theta_H = phi_H inverse.
2. Before completing, choose a flat-term K-flat resolution P of K. At U=(s,id), V=(s,g),
restriction sigma sends x to x restricted to V. The sections-tensor map sends x tensor a to its
sheafified pure tensor. The local formula for b sends the transported tensor to precisely that
same restricted tensor. Constant coefficients obey sigma(a)=c inverse(a), which is exactly the
transported coefficient action. Pure tensors generate, so the two maps agree in every degree,
commute with differentials, and descend through exact sections and ordinary finite-free tensor.
The K-flat tensor-model lemma identifies the resulting map with b_K.
3. Apply derived naturality of sigma at coefficient L to chi_K, including its possibly
nonconstructible source. Substitute beta = G(chi) b chi_G inverse. This gives Gamma(beta) eta_G
(sigma_E tensor 1) = sigma_L eta_K. Cancel the two invertible comparisons to obtain the first
integral equation.
4. The specified-comparison theorem gives alpha T(kappa_E) = kappa_L beta. Apply sections,
invert alpha and beta, and use naturality of phi at the derived morphism kappa_E between the two
admissible objects. The first equation then gives the second integral equation. No naturality of
t is used.
5. For identity and towers, the ordinary b unit and associator identities hold on local iterated
tensors: both composites send ((y tensor a) tensor b) to g inverse of (x tensor a_0 b_0).
Balancing, sheafification and localization give the ordinary identities.
6. Conjugate these identities by chi to obtain beta coherence; move chi past b by naturality and
cancel adjacent chi inverse/chi. The sections associator identity for phi then yields the psi
unit and tower identities. Repeat with the specified alpha tower identity and naturality of phi
at alpha to obtain the psi prime identities. The completed associator is exactly the
chi-conjugated ordinary associator.
7. Apply tensor with L to the second integral equation. The recorded coefficient-complex
rationalization comparison identifies the two tensor orders by the balanced multiplication map,
including fractions. Exactness gives the displayed rational equation. Its unit and mixed
integral/field tower identities transport the coherence equations to raw rationalization, which
retains integral objects and tensors morphisms with the fraction field. -/
theorem point_automorphism_transport_scalar_extension
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    ((pointAutomorphismRestrictionDerived D l hl L g).app
        ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K) ≫
        pointTransportPsi D l hl E g L ι K hK =
      (pointTransportPhi D l hl E L ι K hK).hom ≫
        (pointIntegralModuleDerivedTensor l E L ι).map
          ((pointAutomorphismRestrictionDerived D l hl E g).app K)) ∧
    (pointTransport D l hl L g
        ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K) ≫
        pointTransportPullbackPsi D l hl E g L ι K hK =
      (pointTransportPhi D l hl E L ι K hK).hom ≫
        (pointIntegralModuleDerivedTensor l E L ι).map (pointTransport D l hl E g K)) ∧
    ((pointModuleDerivedRationalization l L).map
        (pointTransport D l hl L g
          ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K)) ≫
        pointTransportRationalPullbackPsi D l hl E g L ι K hK =
      (pointTransportRationalPhi D l hl E L ι K hK).hom ≫
        (pointCoefficientFieldDerivedTensor l E L ι).map
          ((pointModuleDerivedRationalization l E).map (pointTransport D l hl E g K))) := by
  sorry

set_option linter.defProp false in
/-- Constructibility of T K, supplied by the existing intrinsic scalar-extension preservation
theorem. This allows the second extension in every coefficient tower.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportScalarConstructible
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  sfIntegralScalarExtension_constructible D.p l hl E L ι (Spec (.of D.k)) K hK

/-- The canonical completed identity-extension isomorphism already specified by the sections
comparison: invert chi and use ordinary tensor multiplication.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportScalarUnit
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  pointIntegralScalarUnit l E D hl K ((pointIntegralConstructible_iff l E D hl K).mpr hK)

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

/-- The canonical completed coefficient-tower associator already specified by the sections
comparison: conjugate the ordinary derived tensor associator by the prescribed completion
comparisons.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportScalarAssoc
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  pointIntegralScalarAssoc l E L ι M j D hl K
    ((pointIntegralConstructible_iff l E D hl K).mpr hK)

/-- Both transport comparisons respect the canonical identity coefficient extension, integrally and
after raw rationalization.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension).

Proof:
1. The ordinary tensor multiplication identifies the identity extension with the identity
functor. The ordinary b unit formula is multiplication on pure tensors.
2. Conjugate by the specified completion comparison chi. The identity comparison becomes
pointTransportScalarUnit, exactly the unit from the point-sections scalar-comparison lemma. For
alpha use the scalar-operation identity clause with that same completed unit.
3. Insert the unit identity for phi into psi = phi_G Gamma(beta inverse), respectively psi prime
= phi_P Gamma(alpha inverse), and cancel the completion comparisons. This gives the two integral
equalities below, with Gamma(G(unit)) and Gamma(P(unit)) as their canonical right sides.
4. Apply fraction-field tensor and the balanced localization unit identity of the
coefficient-complex rationalization comparison. Multiplication of coefficient factors, including
denominators, yields the two rational equalities. No naturality of t is used. -/
theorem point_automorphism_transport_scalar_unit
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    (pointTransportPsi D l hl E g E (AlgHom.id ℚ_[l] E) K hK ≫
        (pointIntegralModuleDerivedUnit l E).hom.app
          ((pointCompletedDerivedSections D.k l E).obj
            ((inverseImageIntegralDerived l E g).obj K)) =
      (pointCompletedDerivedSections D.k l E).map
        ((inverseImageIntegralDerived l E g).map (pointTransportScalarUnit D l hl E K hK).hom)) ∧
    (pointTransportPullbackPsi D l hl E g E (AlgHom.id ℚ_[l] E) K hK ≫
        (pointIntegralModuleDerivedUnit l E).hom.app
          ((pointCompletedDerivedSections D.k l E).obj
            ((integralDerivedPullback l E g).obj K)) =
      (pointCompletedDerivedSections D.k l E).map
        ((integralDerivedPullback l E g).map (pointTransportScalarUnit D l hl E K hK).hom)) ∧
    (pointTransportRationalPsi D l hl E g E (AlgHom.id ℚ_[l] E) K hK ≫
        (pointCoefficientFieldDerivedUnit l E).hom.app
          ((pointModuleDerivedRationalization l E).obj
            ((pointCompletedDerivedSections D.k l E).obj
              ((inverseImageIntegralDerived l E g).obj K))) =
      (pointModuleDerivedRationalization l E).map
        ((pointCompletedDerivedSections D.k l E).map
          ((inverseImageIntegralDerived l E g).map
            (pointTransportScalarUnit D l hl E K hK).hom))) ∧
    (pointTransportRationalPullbackPsi D l hl E g E (AlgHom.id ℚ_[l] E) K hK ≫
        (pointCoefficientFieldDerivedUnit l E).hom.app
          ((pointModuleDerivedRationalization l E).obj
            ((pointCompletedDerivedSections D.k l E).obj
              ((integralDerivedPullback l E g).obj K))) =
      (pointModuleDerivedRationalization l E).map
        ((pointCompletedDerivedSections D.k l E).map
          ((integralDerivedPullback l E g).map
            (pointTransportScalarUnit D l hl E K hK).hom))) := by
  sorry

/-- Both transport comparisons respect successive finite coefficient extensions under the canonical
integral and rational associators.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension).

Proof:
1. On a flat-term K-flat model, both ordinary inverse-image tensor tower composites agree on
every local iterated pure tensor. This is the pure-tensor formula for b and the ordinary derived
tensor associator; it descends by the tensor-model and exact localization lemmas.
2. Substitute beta = G(chi) b chi_G inverse. Naturality of b moves the middle chi comparison
past b, and the adjacent inverse comparisons cancel. The result is beta_ME A_G = G_M(A) beta_ML
T_ML(beta_LE), with precisely the chi-conjugated completed associator A in
pointIntegralScalarAssoc.
3. Insert psi = phi_G Gamma(beta inverse). The associator identity for phi and naturality of
phi_ML at beta_LE cancel T_ML(beta_LE). This gives the first integral identity below.
4. The scalar-operation comparison gives the same tower identity for alpha. Insert psi prime =
phi_P Gamma(alpha inverse), and use naturality of phi_ML at alpha_LE and the same sections
associator identity. This gives the second integral identity, without assuming naturality of t.
5. Tensor these equalities with M and use the mixed integral/field tower identity of the
balanced rationalization comparison. Both routes multiply the coefficient factors in the same
order, including fractions. This gives the two rational tower equations with the existing
coefficient-field derived associator. -/
theorem point_automorphism_transport_scalar_tower
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    ((pointCompletedDerivedSections D.k l M).map
        ((inverseImageIntegralDerived l M g).map
          (pointTransportScalarAssoc D l hl E L ι M j K hK).hom) ≫
        pointTransportPsi D l hl E g M (j.comp ι) K hK =
      pointTransportPsi D l hl L g M j _
          (pointTransportScalarConstructible D l hl E L ι K hK) ≫
        (pointIntegralModuleDerivedTensor l L M j).map
          (pointTransportPsi D l hl E g L ι K hK) ≫
        (pointIntegralModuleDerivedAssoc l E L ι M j).hom.app
          ((pointCompletedDerivedSections D.k l E).obj
            ((inverseImageIntegralDerived l E g).obj K))) ∧
    ((pointCompletedDerivedSections D.k l M).map
        ((integralDerivedPullback l M g).map
          (pointTransportScalarAssoc D l hl E L ι M j K hK).hom) ≫
        pointTransportPullbackPsi D l hl E g M (j.comp ι) K hK =
      pointTransportPullbackPsi D l hl L g M j _
          (pointTransportScalarConstructible D l hl E L ι K hK) ≫
        (pointIntegralModuleDerivedTensor l L M j).map
          (pointTransportPullbackPsi D l hl E g L ι K hK) ≫
        (pointIntegralModuleDerivedAssoc l E L ι M j).hom.app
          ((pointCompletedDerivedSections D.k l E).obj
            ((integralDerivedPullback l E g).obj K))) ∧
    ((pointModuleDerivedRationalization l M).map
        ((pointCompletedDerivedSections D.k l M).map
          ((inverseImageIntegralDerived l M g).map
            (pointTransportScalarAssoc D l hl E L ι M j K hK).hom)) ≫
        pointTransportRationalPsi D l hl E g M (j.comp ι) K hK =
      pointTransportRationalPsi D l hl L g M j _
          (pointTransportScalarConstructible D l hl E L ι K hK) ≫
        (pointCoefficientFieldDerivedTensor l L M j).map
          (pointTransportRationalPsi D l hl E g L ι K hK) ≫
        (pointCoefficientFieldDerivedAssoc l E L ι M j).hom.app
          ((pointModuleDerivedRationalization l E).obj
            ((pointCompletedDerivedSections D.k l E).obj
              ((inverseImageIntegralDerived l E g).obj K)))) ∧
    ((pointModuleDerivedRationalization l M).map
        ((pointCompletedDerivedSections D.k l M).map
          ((integralDerivedPullback l M g).map
            (pointTransportScalarAssoc D l hl E L ι M j K hK).hom)) ≫
        pointTransportRationalPullbackPsi D l hl E g M (j.comp ι) K hK =
      pointTransportRationalPullbackPsi D l hl L g M j _
          (pointTransportScalarConstructible D l hl E L ι K hK) ≫
        (pointCoefficientFieldDerivedTensor l L M j).map
          (pointTransportRationalPullbackPsi D l hl E g L ι K hK) ≫
        (pointCoefficientFieldDerivedAssoc l E L ι M j).hom.app
          ((pointModuleDerivedRationalization l E).obj
            ((pointCompletedDerivedSections D.k l E).obj
              ((integralDerivedPullback l E g).obj K)))) := by
  sorry

end WeilConjectures
