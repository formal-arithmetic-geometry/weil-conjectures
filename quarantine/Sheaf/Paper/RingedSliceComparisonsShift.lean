/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.RingedDerivedSliceLocalization
public import Sheaf.Paper.DerivedAdjunctionShift
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Paper.RingedSliceDerivedComparisons
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Shift.Adjunction
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Integer shifts of canonical ringed-slice comparisons

Source: Stacks Project, sites-cohomology.tex, Tags 08FI and 07A4, and the
agent-written signed-shift calculation from these constructions
(blueprint: lem-weil-pbc-ringed-slice-comparisons-shift).

The helper predicates only spell out the representative normalization and the four
squares in this statement. Tensor, restriction, and the derived adjunctions are the
existing constructions. No comparison is selected from an arbitrary existence claim.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace SheafOfModules

/-- The inherited resolution shift of the existing exact derived slice restriction.
Source: Stacks Tags 08FI and 07A4; signed representative calculation
(blueprint: lem-weil-pbc-ringed-slice-comparisons-shift). -/
instance ringedSliceRestrictionCommShift
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings A))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((localCoefficientRings A).over U))] :
    (ringedSliceRestriction.{u, w} A U).CommShift ℤ :=
  letI := (ringedOverFunctor_exactGeneral.{u, u, u, u} (localCoefficientRings A) U).1
  letI := (ringedOverFunctor_exactGeneral.{u, u, u, u} (localCoefficientRings A) U).2.1
  letI := (ringedOverFunctor_exactGeneral.{u, u, u, u} (localCoefficientRings A) U).2.2
  inferInstanceAs ((overFunctor.{u} (localCoefficientRings A) U).mapDerivedCategory.CommShift ℤ)

section Tensor

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Sheaf J CommRingCat.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings A))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, w} J A))
  (T : CoefficientTensorModels.{u, u, u, w} J A S)
  [(Functor.curry.obj S.tensor).CommShift₂Int]

/-- The specified tensor shifts are the unsigned first and signed second total shifts.
The formulas on sheafified pure-tensor generators determine the chain isomorphisms;
the displayed localization squares fix the derived shifts, including their signs.
Source: Stacks Tags 08FI and 07A4; signed representative calculation
(blueprint: lem-weil-pbc-ringed-slice-comparisons-shift). -/
def RingedSliceTensorShiftNormalized : Prop :=
  (∀ (P Q : CochainComplex (SheafOfModules.{u} (localCoefficientRings A)) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q) (n : ℤ),
    ∃ hpn : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) (P⟦n⟧),
    ∃ γ : (coefficientTotalTensor.{u, u, u} J A).obj (P⟦n⟧, Q) ≅
        ((coefficientTotalTensor.{u, u, u} J A).obj (P, Q))⟦n⟧,
      (∀ (p q k : ℤ) (h : p + q = k) (h' : (p + n) + q = k + n) (V : Cᵒᵖ)
        (x : (P.X (p + n)).val.obj V)
        (y : (Q.X q).val.obj V),
        (γ.hom.f k).val.app V
          (coefficientTensorGenerator.{u, u, u} J A (P⟦n⟧) Q p q k h V x y) =
          coefficientTensorGenerator.{u, u, u} J A P Q (p + n) q (k + n) h' V x y) ∧
      (T.iso J A S (P⟦n⟧) Q hpn hq).hom ≫
        S.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso n).hom.app P) (𝟙 _)) ≫
        (((Functor.curry.obj S.tensor).flip.obj (DerivedCategory.Q.obj Q)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map γ.hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((coefficientTotalTensor.{u, u, u} J A).obj (P, Q)) ≫
        (T.iso J A S P Q hp hq).hom⟦n⟧') ∧
  (∀ (P Q : CochainComplex (SheafOfModules.{u} (localCoefficientRings A)) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q) (n : ℤ),
    ∃ hqn : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) (Q⟦n⟧),
    ∃ γ : (coefficientTotalTensor.{u, u, u} J A).obj (P, Q⟦n⟧) ≅
        ((coefficientTotalTensor.{u, u, u} J A).obj (P, Q))⟦n⟧,
      (∀ (p q k : ℤ) (h : p + q = k) (h' : p + (q + n) = k + n) (V : Cᵒᵖ)
        (x : (P.X p).val.obj V)
        (y : (Q.X (q + n)).val.obj V),
        (γ.hom.f k).val.app V
          (coefficientTensorGenerator.{u, u, u} J A P (Q⟦n⟧) p q k h V x y) =
          (p * n).negOnePow •
            coefficientTensorGenerator.{u, u, u} J A P Q p (q + n) (k + n) h' V x y) ∧
      (T.iso J A S P (Q⟦n⟧) hp hqn).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 _) ((DerivedCategory.Q.commShiftIso n).hom.app Q)) ≫
        (((Functor.curry.obj S.tensor).obj (DerivedCategory.Q.obj P)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map γ.hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((coefficientTotalTensor.{u, u, u} J A).obj (P, Q)) ≫
        (T.iso J A S P Q hp hq).hom⟦n⟧')

end Tensor

/-- Both tensor shift squares for the canonical slice comparison, with the other
input fixed. Quantification over normalized models makes the assertion independent
of the presentation of derived tensor. This predicate is applied to both R and S.
Source: Stacks Tags 08FI and 07A4; signed representative calculation
(blueprint: lem-weil-pbc-ringed-slice-comparisons-shift). -/
def RingedSliceTensorShiftCompatibility
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings A))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((localCoefficientRings A).over U))] : Prop :=
  ∀ (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, w} J A))
    (T : CoefficientTensorModels.{u, u, u, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u, u, u, w} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, u, u, w} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons
      (derivedInternalHomOfUniverses.{u, u, u, w} J A)
      (derivedInternalHomOfUniverses.{u, u, u, w} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{u, u, u, w, w} J A U) S SU
      (RingedSliceFlatRestriction.{u, u, u} J A U))
    (_hd : RingedSliceTensorModel.{u, u, u, w, w} J A U S T SU TU d)
    [_s : (Functor.curry.obj S.tensor).CommShift₂Int]
    [_sU : (Functor.curry.obj SU.tensor).CommShift₂Int],
    RingedSliceTensorShiftNormalized J A S T →
    RingedSliceTensorShiftNormalized (J.over U) (A.over U) SU TU →
    ∀ (M N : ringedSiteDerived.{u, w} A) (n : ℤ),
      ((d.rho (M⟦n⟧) N).hom ≫
        SU.tensor.map (Prod.mkHom
          (((ringedSliceRestriction.{u, w} A U).commShiftIso n).hom.app M) (𝟙 _)) ≫
        (((Functor.curry.obj SU.tensor).flip.obj
          ((ringedSliceRestriction.{u, w} A U).obj N)).commShiftIso n).hom.app
            ((ringedSliceRestriction.{u, w} A U).obj M) =
      (ringedSliceRestriction.{u, w} A U).map
        ((((Functor.curry.obj S.tensor).flip.obj N).commShiftIso n).hom.app M) ≫
        ((ringedSliceRestriction.{u, w} A U).commShiftIso n).hom.app
          (S.tensor.obj (M, N)) ≫ (d.rho M N).hom⟦n⟧') ∧
      ((d.rho M (N⟦n⟧)).hom ≫
        SU.tensor.map (Prod.mkHom (𝟙 _)
          (((ringedSliceRestriction.{u, w} A U).commShiftIso n).hom.app N)) ≫
        (((Functor.curry.obj SU.tensor).obj
          ((ringedSliceRestriction.{u, w} A U).obj M)).commShiftIso n).hom.app
            ((ringedSliceRestriction.{u, w} A U).obj N) =
      (ringedSliceRestriction.{u, w} A U).map
        ((((Functor.curry.obj S.tensor).obj M).commShiftIso n).hom.app N) ≫
        ((ringedSliceRestriction.{u, w} A U).commShiftIso n).hom.app
          (S.tensor.obj (M, N)) ≫ (d.rho M N).hom⟦n⟧')

/-- The adjunct of the specified coefficient isomorphism, used by the recorded module API.
Source: Stacks Tag 04J0 (blueprint: lem-weil-pbc-ringed-slice-comparisons-shift). -/
def ringedSliceShiftStructuralMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : D ⥤ C) [u.IsContinuous K J]
    {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
    (c : (u.sheafPullback CommRingCat.{u} K J).obj R ≅ S) :
    R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S :=
  (u.sheafAdjunctionContinuous CommRingCat.{u} K J).homEquiv R S c.hom

/-- The canonical direct-image, inverse-image, and both tensor slice comparisons
commute with every integer shift, with the specified total-tensor signs.
Source: Stacks Tags 08FI and 07A4, representative constructions; the signed-shift
calculation is agent-written (blueprint: lem-weil-pbc-ringed-slice-comparisons-shift).

Proof:
1. Restriction is termwise identity at T -> V, so its shift comparison has identity
components. The differential on K[n] is (-1)^n d. Mathlib's total-tensor shifts
(lem-weil-pbc-total-tensor-integer-shifts) have coefficient 1 in the first input
and (-1)^(np) in the second. Reindexing preserves flat terms and K-flatness:
tensoring a shifted representative with an acyclic complex is a shift of an
acyclic tensor, by these signed isomorphisms (def-pc-kflat-complex).
2. Resolve E by a K-injective I (prop-pur-kinjective-resolutions-exist).
Its restriction is K-injective (lem-pur-kinjective-restrict-localized).
The normalization below is precisely lem-weil-pbc-ringed-slice-derived-comparisons:
beta on QI is induced by the ordinary identity on I(uT). For E[n] use I[n],
valid by lem-weil-pbc-kinjective-shift. Both shift-square paths are identity on
I^(a+n)(uT), with differential (-1)^n d. Localization and naturality extend
the equality to every unbounded E. The specified resolution shifts are fixed
by their compatibility with eta and epsilon (lem-weil-pbc-derived-adjunction-shift).
3. The unit square in RingedSliceAdjunctionSquare identifies the adjunct of
lambda_P with beta_(LP) after restriction of the global unit. Apply the unit
shift equations of lem-weil-pbc-derived-adjunction-shift globally and locally,
Step 2, and naturality of beta at L(P[n]) -> LP[n]. The resulting equality
says the two shifted adjuncts are equal.
4. The adjunction bijection is injective, hence the two lambda shift paths agree
(lem-weil-pbc-adjunction-shift-compatibility-unique). This uses the specified
mate, including its orientation, rather than selecting a new comparison.
5. For either site resolve both tensor inputs by flat-term K-flat P,Q
(lem-pc-kflat-resolution). Restriction preserves this class. The canonical
tensor normalization is RingedSliceTensorModel, from
lem-weil-pbc-ringed-slice-evaluation-transpose: on each (p,q) summand it sends
x tensor y to x tensor y. Use shifted representatives from Step 1.
6. In the first-input square both paths send the summand to the same restricted
pure tensor with coefficient 1; in the second both have coefficient (-1)^(np).
Restriction and the tensor map commute with this scalar. These are chain maps
for the differential in def-pc-tensor-complex-sheaves. Equality passes through Q;
the uniqueness clause of lem-weil-pbc-site-derived-tensor-descent extends it
to arbitrary derived inputs. Do this for R at V and S at u(V), giving all four
squares. No boundedness or nonzero coefficient hypothesis is used. -/
theorem ringedSliceComparisonsShift
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : D ⥤ C) [u.IsContinuous K J]
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)]
    {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
    (c : (u.sheafPullback CommRingCat.{u} K J).obj R ≅ S) (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings S))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((localCoefficientRings R).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((localCoefficientRings S).over (u.obj V)))]
    (e : RingedSliceDerivedImage.{u, w} u (ringedSliceShiftStructuralMap u c))
    (l : RingedSliceDerivedImage.{u, w} (Over.post (X := V) u)
      (localizedRingedSiteMap u (ringedSliceShiftStructuralMap u c) V))
    (d : RingedSliceAdjunctionSquare e.adjunction l.adjunction
      (ringedSliceRestriction.{u, w} R V) (ringedSliceRestriction.{u, w} S (u.obj V)))
    (_normalized : ∀ I : CochainComplex (SheafOfModules.{u} (localCoefficientRings S)) ℤ,
      (ringedSliceRestriction.{u, w} R V).map (e.eta.app I) ≫
        d.beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
        l.right.map ((ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app I) =
      (ringedSliceRestrictionFactors.{u, w} R V).hom.app
        (((ringedSliceModulePushforward u (ringedSliceShiftStructuralMap u c)).mapHomologicalComplex
          (.up ℤ)).obj I) ≫
        DerivedCategory.Q.{w}.map
          (ringedSlicePushforwardComplexIso u (ringedSliceShiftStructuralMap u c) V I).hom ≫
        l.eta.app ((ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I))
    [e.left.CommShift ℤ] [e.right.CommShift ℤ]
    [l.left.CommShift ℤ] [l.right.CommShift ℤ]
    [NatTrans.CommShift e.epsilon ℤ] [NatTrans.CommShift e.eta ℤ]
    [NatTrans.CommShift l.epsilon ℤ] [NatTrans.CommShift l.eta ℤ] :
    NatTrans.CommShift d.beta.hom ℤ ∧ NatTrans.CommShift d.lambda.hom ℤ ∧
      RingedSliceTensorShiftCompatibility.{u, w} K R V ∧
      RingedSliceTensorShiftCompatibility.{u, w} J S (u.obj V) := by
  sorry

end SheafOfModules
