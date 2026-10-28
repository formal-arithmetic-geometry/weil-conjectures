/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.DerivedAutomorphismHomEvaluationBase
public import Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationABase

import all Sheaf.Paper.IsomorphismReductionTower
import Sheaf.Paper.PodReindexingHomCoefficientDescent
import Sheaf.Paper.PodIntegralHomComparisonIsIso
import Sheaf.Paper.PodIntegralHomComparisonNaturality
import Sheaf.Paper.PodIntegralHomComparisonEvaluation
import Sheaf.Paper.PodIntegralHomComparisonTranspose
import all Sheaf.AlgebraicGeometry.ProEtale.FiniteComparisonIsomorphism
import all Sheaf.Paper.FiniteCoefficientHomChange
import all Sheaf.Paper.CompletedPullbackTowerCore
import Sheaf.Paper.IntegralComparisonSequenceSystems

/-! # Internal Hom and evaluation under coefficient-site isomorphisms

Source: Stacks Project, Modules on Sites, Tag 0GMX; the derived and completed
normalization is the enhancement in the node's sixteen proof steps, supplying
main-20261015 prop-pod-dual-tate-data-compatibility Steps 1, 2, 4 and 5.
(blueprint: lem-pod-derived-automorphism-hom-evaluation).

Finite inputs are unbounded. Integral inputs have exactly the recorded
Hom-constructibility condition. Completed inverse image is constructed from
all coefficient projections; its comparison with tower pullback uses the
actual completion unit and a resolution-normalized total-limit comparison.
System maps and their identities are stated before evaluation or realization.
Rational maps are localized; algebraically closed maps use every common stage.

## Main definitions

* `podFiniteHomComparison`: transpose of pullback of finite evaluation.
* `podPartialHomComparison`: the same construction on permitted Hom pairs.
* `podCompletedRingMap`: completed coefficient transport from all projections.
* `podCompletedToTower`: the completion-unit comparison with tower pullback.

## Main statements

* `derivedAutomorphismHomEvaluation`: the four evaluation-defined natural isomorphisms.
* The `*_laws`, `*_shift`, `*_comp` declarations give all coherent identities.
* `podHomReductionSquare`: the actual system-level reduction square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard
attribute [-instance] isoReductionAbSheafify isoReductionAbBijective isoReductionSiteSmall


section IntegralTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Integral invertibility, naturality, evaluation and every transpose, using
completed tensor and exactly the stated Hom-constructible domain.
Source: node proof steps 8--11.
Proof: the four fields are `podIntegralHomComparison_isIso`,
`podIntegralHomComparison_naturality`, `podIntegralHomComparison_evaluation` and
`podIntegralHomComparison_transpose`.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralHomComparison_laws :
    PodPartialHomCompatibility (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) := by
  refine { isIso := ?_, naturality := ?_, evaluation := ?_, transpose := ?_ }
  · exact podIntegralHomComparison_isIso l E g
  · exact podIntegralHomComparison_naturality l E g
  · exact podIntegralHomComparison_evaluation l E g
  · exact podIntegralHomComparison_transpose l E g
end IntegralTransport

section RationalClosed
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- The rational transpose is the unique additive localization of the integral
transpose. The equation fixes inverse transposition on every pure tensor in the
actual localized Hom groups, including its scalar.
Source: node proof step 14.
Proof: integral transposition is O_E-linear, so tensor it with E. Its inverse
localizes too. The unchanged integral objects and the prescribed rational
operation formulas identify the endpoints. Pure tensors generate each Hom
module, so the normalization determines both maps uniquely; balancing and
naturality descend from their integral versions.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalClosed_existsUnique :
    ∃! S : PodPartialClosed (rationalDerivedTensor l E W)
        (constructibleRationalHomPairs l E W) (rationalDerivedInternalHom l E W),
      ∀ (L : sfRationalConstructibleCategory l E W)
        (P : (constructibleRationalHomPairs l E W).FullSubcategory)
        (f : L.obj ⟶ (constructibleIntegralHom l E W).obj
          (integralPairOfRationalHomPair l E W P))
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
        (q : L ⟶ (rationalDerivedInternalHom l E W).obj P),
        HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) →
        HEq ((S.transpose L P).symm q)
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            ((podIntegralClosed l E W).transpose L.obj
              (integralPairOfRationalHomPair l E W P)).symm f) := by
  sorry

/-- The uniquely localized completed closed data.
Source: node proof step 14 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podRationalClosed := (podRationalClosed_existsUnique l E W).exists.choose
end RationalClosed

section RationalTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Rational pullback preserves the same integral Hom-pair condition.
Source: node proof step 14.
Proof: the rational operations keep integral objects. Their object formulas
identify this condition with podIntegralPairs_pullback.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalPairs_pullback
    (P : (constructibleRationalHomPairs l E Y).FullSubcategory) :
    constructibleRationalHomPairs l E X
      (((rationalDerivedPullback l E g).op.prod (rationalDerivedPullback l E g)).obj P.obj) := by
  exact PodCoefficientDescent.rational_pair_permitted l E g P

/-- The rational comparison uses precisely localized tensor and evaluation.
Source: node proof step 14 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podRationalHomComparison :=
  podPartialHomComparison (podRationalClosed l E Y) (podRationalClosed l E X)
    (rationalDerivedPullback l E g) (podRationalPairs_pullback l E g)
      (canonicalRationalPullbackTensor l E g)

/-- Rational maps are the localized integral maps, and naturality holds for
arbitrary localized Hom arrows, including sums of pure tensors.
Source: node proof step 14.
Proof: localize the integral comparison and its inverse. On pure tensors the
closed normalization gives the displayed map; additivity and balancing extend
this to all arrows. Expand each naturality and evaluation equation bilinearly
and apply the integral equation to each summand. Transposition is linear too.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalHomComparison_laws :
    PodPartialHomCompatibility (podRationalClosed l E Y) (podRationalClosed l E X)
      (rationalDerivedPullback l E g) (podRationalPairs_pullback l E g)
        (canonicalRationalPullbackTensor l E g) ∧
    ∀ P : (constructibleRationalHomPairs l E Y).FullSubcategory,
      HEq (podRationalHomComparison l E g P)
        ((sfRationalConstructibleLocalization l E X).map
          (podIntegralHomComparison l E g (integralPairOfRationalHomPair l E Y P))) := by
  sorry
end RationalTransport


section CommonClosed
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

set_option backward.isDefEq.respectTransparency true in
/-- Exact common-stage normalization of inverse transposition, at every finite
stage containing the entries. The implications only reconcile the recorded
operation objects with their literal pair representatives, whose equality is
part of the owning operation definitions; they impose no condition on arrows.
Source: node proof steps 15--16
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def PodCommonTransposeNormalization
    (S : PodPartialClosed (commonStageDerivedTensor l Ω W)
      (commonStageHomPairs l Ω W) (commonStageDerivedInternalHom l Ω W)) : Prop :=
  ∀ (L : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (hL : L.stage ≤ F) (hP : (commonStageHomObject l Ω W P).stage ≤ F)
    (hT : (commonStageTensorObject l Ω W L P.obj.1.unop).stage ≤ F)
    (hN : P.obj.2.stage ≤ F)
    (φ : L.toStage hL ⟶ (commonStageHomObject l Ω W P).toStage hP)
    (q : L ⟶ (commonStageDerivedInternalHom l Ω W).obj P),
    HEq q (ofHom L (commonStageHomObject l Ω W P) F hL hP φ) →
    HEq ((S.transpose L P).symm q)
      (ofHom (commonStageTensorObject l Ω W L P.obj.1.unop) P.obj.2 F hT hN
        ((commonStageTensorComparison l Ω W L P.obj.1.unop F hT).hom ≫
          ((podRationalClosed l (Coefficient.{u} l Ω F) W).transpose (L.toStage hL)
            (commonStageHomPairAtStage l Ω W P F hP)).symm
              (φ ≫ (commonStageHomComparison l Ω W P F hP).hom)))

/-- Common-stage closed maps are determined by rational transposition at every
larger finite field, and are natural on the actual Hom-colimit category.
Source: node proof steps 15--16.
Proof: put the parameter, pair and arrow over a common finite field. Apply the
rational inverse transpose, conjugating by the recorded tensor and Hom stage
comparisons. Finite free coefficient extension preserves the evaluation formula,
without requiring the first input to be perfect: Hom commutes with the finite
direct sum of its coefficient copies. Transposition therefore commutes with
further scalar extension. This proves independence of enlargement and eventual
equality. The rational inverse maps prove bijectivity; addition and naturality
can be checked at one common stage. Every arrow has such a representative, so
the normalization determines the closed data uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonClosed_existsUnique :
    ∃! S : PodPartialClosed (commonStageDerivedTensor l Ω W)
      (commonStageHomPairs l Ω W) (commonStageDerivedInternalHom l Ω W),
      PodCommonTransposeNormalization l Ω W S := by
  sorry

/-- The closed data normalized on all common finite-field representatives.
Source: node proof step 16 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCommonClosed := (podCommonClosed_existsUnique l Ω W).exists.choose
end CommonClosed

section CommonTransport
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Isomorphism pullback preserves the permitted common-stage Hom pairs.
Source: node proof steps 15--16.
Proof: at the finite compositum use podRationalPairs_pullback, then the
prescribed pullback/scalar comparison to identify both entries. Hom of the
resulting pair is isomorphic to the pulled back Hom, so is constructible.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonPairs_pullback
    (P : (commonStageHomPairs l Ω Y).FullSubcategory) :
    commonStageHomPairs l Ω X
      (((commonStageDerivedPullback l Ω g).op.prod
        (commonStageDerivedPullback l Ω g)).obj P.obj) := by
  have h := PodCoefficientDescent.common_pair_permitted l Ω g P
  have hobj := (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1
  change commonStageHomPairs l Ω X
    (op ((commonStageDerivedPullback l Ω g).obj P.obj.1.unop),
      (commonStageDerivedPullback l Ω g).obj P.obj.2)
  change commonStageHomPairs l Ω X
    (op ((commonStageDerivedPullback_existsUnique l Ω g).exists.choose.obj P.obj.1.unop),
      (commonStageDerivedPullback_existsUnique l Ω g).exists.choose.obj P.obj.2)
  rw [hobj P.obj.1.unop, hobj P.obj.2]
  exact h

/-- The common-stage comparison is the transpose of the prescribed common-stage
tensor/evaluation composite on the actual pair category.
Source: node proof step 16 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCommonHomComparison :=
  podPartialHomComparison (podCommonClosed l Ω Y) (podCommonClosed l Ω X)
    (commonStageDerivedPullback l Ω g) (podCommonPairs_pullback l Ω g)
      (canonicalCommonStagePullbackTensor l Ω g)

/-- Invertibility and all displayed identities on the algebraically closed
coefficient category, naturally for arbitrary common-stage morphisms.
Source: node proof steps 15--16.
Proof: put every arrow in a proposed equation over one common finite field.
The normalized transpose and tensor comparison identify the comparison there
with the rational evaluation-defined comparison. Its inverse, naturality,
evaluation and transposition equations hold by podRationalHomComparison_laws.
Finite free scalar compatibility makes their classes independent of the
chosen stage and arrow representative, including eventual equality.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonHomComparison_laws :
    PodPartialHomCompatibility (podCommonClosed l Ω Y) (podCommonClosed l Ω X)
      (commonStageDerivedPullback l Ω g) (podCommonPairs_pullback l Ω g)
        (canonicalCommonStagePullbackTensor l Ω g) := by
  sorry
end CommonTransport

section Systems
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- The comparison is an actual map on the unbounded derived category of strict
systems, defined before finite evaluation or total-limit realization.
Source: node proof steps 12--13, Stacks 0941 and 0GMX
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podSystemHomComparison :=
  coefficientBaseChangeHom (pullbackTensorCalculus l E Y).systemClosed
    (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
      (pullbackTensorSystemComparison l E g)

/-- System reindexing preserves internal Hom and the actual system evaluation,
transposes and internal composition, without inferring equality from evaluations.
Source: node proof step 12.
Proof: identify the ordinary sequence inverse image with the integral-comparison
pullback by their common ring map. Its derived composition and identity
isomorphisms exhibit inverse reindexing as a quasi-inverse. For every test
object in the image, the two closed adjunctions, full faithfulness and the
tensor comparison identify postcomposition with the Hom comparison as a
bijection. Essential surjectivity extends this to all test objects, so Yoneda
proves invertibility. Naturality and transposition are the general closed
adjunction calculations. The recorded tensor associativity and unit identities
construct a strong monoidal structure with exactly the prescribed tensorator;
the general evaluation/composition calculation then gives all remaining laws.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podSystemHomComparison_laws :
    (∀ M N, IsIso (podSystemHomComparison l E g M N)) ∧
    CoefficientEvaluationCompatible (pullbackTensorCalculus l E Y).systemClosed
      (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
        (pullbackTensorSystemComparison l E g) := by
  let SA := (pullbackTensorCalculus l E Y).systemClosed
  let SB := (pullbackTensorCalculus l E X).systemClosed
  let F := pullbackTensorSequenceDerived l E g
  let μ := pullbackTensorSystemComparison l E g
  change (∀ M N, IsIso (coefficientBaseChangeHom SA SB F μ M N)) ∧
    CoefficientEvaluationCompatible SA SB F μ
  have hF : F ≅ integralComparisonDerivedSequencePullback l E g := by
    have heq : pullbackTensorSequenceInverse l E g =
        integralComparisonSequencePullback l E g := by
      unfold pullbackTensorSequenceInverse integralComparisonSequencePullback
      congr 1
      unfold pullbackTensorSequenceDirect integralComparisonSequenceDirectImage
      rw [pullbackTensorSequenceRing_eq]
    exact Functor.mapDerivedCategoryNatIso (eqToIso heq)
  have hH : (integralComparisonDerivedSequencePullback l E g).IsEquivalence := by
    let H := integralComparisonDerivedSequencePullback l E g
    let G := integralComparisonDerivedSequencePullback l E (inv g)
    let a : H ⋙ G ≅ 𝟭 _ :=
      (integralComparisonSystemComposition l E (inv g) g).symm ≪≫
        eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
          (IsIso.inv_hom_id g)) ≪≫ integralComparisonSystemUnit l E Y
    let b : G ⋙ H ≅ 𝟭 _ :=
      (integralComparisonSystemComposition l E g (inv g)).symm ≪≫
        eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
          (IsIso.hom_inv_id g)) ≪≫ integralComparisonSystemUnit l E X
    exact (CategoryTheory.Equivalence.mk H G a.symm b).isEquivalence_functor
  have : F.IsEquivalence := Functor.isEquivalence_of_iso hF.symm
  refine ⟨?_, ?_⟩
  · intro M N
    have hL (L : coefficientSequenceDerived l E Y) : Function.Bijective
        (fun x : F.obj L ⟶ F.obj ((coefficientSequenceInternalHom l E Y).obj (op M, N)) ↦
          x ≫ coefficientBaseChangeHom SA SB F μ M N) := by
      let e := (SA.transpose L M N).symm.trans
        ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
          ((Iso.homCongr (μ.app (L, M)) (Iso.refl (F.obj N))).trans
            (SB.transpose _ _ _)))
      have he (x : L ⟶ (coefficientSequenceInternalHom l E Y).obj (op M, N)) :
          e x = F.map x ≫ coefficientBaseChangeHom SA SB F μ M N := by
        dsimp only [e, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk,
          Functor.FullyFaithful.homEquiv, Iso.refl_hom]
        rw [Category.comp_id]
        change SB.transpose _ _ _ (μ.inv.app (L, M) ≫
          F.map ((SA.transpose L M N).symm x)) = _
        simpa only [Equiv.apply_symm_apply] using
          (finiteChange_transpose SA SB F μ L M N ((SA.transpose L M N).symm x)).symm
      have hbij : Function.Bijective
          (fun x : L ⟶ (coefficientSequenceInternalHom l E Y).obj (op M, N) ↦
            F.map x ≫ coefficientBaseChangeHom SA SB F μ M N) := by
        simpa only [← he] using e.bijective
      constructor
      · intro x y hxy
        obtain ⟨x₀, rfl⟩ := F.map_surjective x
        obtain ⟨y₀, rfl⟩ := F.map_surjective y
        exact congrArg F.map (hbij.1 hxy)
      · intro y
        obtain ⟨x, hx⟩ := hbij.2 y
        exact ⟨F.map x, hx⟩
    apply isIso_of_yoneda_map_bijective
    intro T
    let e := F.objObjPreimageIso T
    constructor
    · intro x y hxy
      apply (cancel_epi e.hom).mp
      apply (hL (F.objPreimage T)).1
      simpa only [Category.assoc] using congrArg (fun z ↦ e.hom ≫ z) hxy
    · intro y
      obtain ⟨x, hx⟩ := (hL (F.objPreimage T)).2 (e.hom ≫ y)
      refine ⟨e.inv ≫ x, ?_⟩
      change (e.inv ≫ x) ≫ coefficientBaseChangeHom SA SB F μ M N = y
      change x ≫ coefficientBaseChangeHom SA SB F μ M N = e.hom ≫ y at hx
      rw [Category.assoc, hx, Iso.inv_hom_id_assoc]
  let := SA.monoidal
  let := SB.monoidal
  have hright {A B : coefficientSequenceDerived l E X} (f : A ⟶ B)
      (P : coefficientSequenceDerived l E X) :
      SB.tensor.map (Prod.mkHom f (𝟙 P)) = SB.monoidal.whiskerRight f P :=
    @MonoidalCategory.tensorHom_id _ _ SB.monoidal A B f P
  have hleft (P : coefficientSequenceDerived l E X)
      {A B : coefficientSequenceDerived l E X} (f : A ⟶ B) :
      SB.tensor.map (Prod.mkHom (𝟙 P) f) = SB.monoidal.whiskerLeft P f :=
    @MonoidalCategory.id_tensorHom _ _ SB.monoidal P A B f
  obtain ⟨ε, hε⟩ := pullbackTensorSystemComparison_unit l E g
  let s : F.CoreMonoidal := Functor.CoreMonoidal.mk' ε.symm
    (fun M N ↦ (μ.app (M, N)).symm)
    (by
      intro M N f P
      have hn := μ.hom.naturality (Prod.mkHom f (𝟙 P))
      dsimp only [Functor.comp_map, Functor.prod_map] at hn
      rw [(pullbackTensorSequenceDerived l E g).map_id] at hn
      rw [hright] at hn
      simpa only [F, SA, SB, μ, CoefficientClosedStructure.tensor,
        Iso.symm_inv, Iso.app_hom,
        MonoidalCategory.tensor_map,
        @MonoidalCategory.tensorHom_id _ _ SA.monoidal,
        @MonoidalCategory.tensorHom_id _ _ SB.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SA.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SB.monoidal] using hn.symm)
    (by
      intro M N P f
      have hn := μ.hom.naturality (Prod.mkHom (𝟙 P) f)
      dsimp only [Functor.comp_map, Functor.prod_map] at hn
      rw [(pullbackTensorSequenceDerived l E g).map_id] at hn
      rw [hleft] at hn
      simpa only [F, SA, SB, μ, CoefficientClosedStructure.tensor,
        Iso.symm_inv, Iso.app_hom,
        MonoidalCategory.tensor_map,
        @MonoidalCategory.tensorHom_id _ _ SA.monoidal,
        @MonoidalCategory.tensorHom_id _ _ SB.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SA.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SB.monoidal] using hn.symm)
    (by
      intro M N P
      simpa only [Iso.symm_inv, Iso.app_hom, CoefficientClosedStructure.tensor,
        Functor.comp_obj, Functor.prod_obj,
        MonoidalCategory.tensor_obj, MonoidalCategory.tensor_map,
        @MonoidalCategory.tensorHom_id _ _ SA.monoidal,
        @MonoidalCategory.tensorHom_id _ _ SB.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SA.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SB.monoidal] using
        (pullbackTensorSystemComparison_associativity l E g M N P).symm)
    (by
      intro M
      have h := (hε M).1
      rw [hright] at h
      apply (cancel_epi (F.map (SA.monoidal.leftUnitor M).hom)).1
      apply (cancel_mono (SB.monoidal.leftUnitor (F.obj M)).hom).1
      simpa only [F, SA, SB, μ, Category.assoc,
        ← (pullbackTensorSequenceDerived l E g).map_comp_assoc, Iso.hom_inv_id,
        (pullbackTensorSequenceDerived l E g).map_id,
        Iso.symm_inv, Iso.app_hom,
        Category.id_comp, Iso.inv_hom_id, Category.comp_id,
        CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
        @MonoidalCategory.tensorHom_id _ _ SA.monoidal,
        @MonoidalCategory.tensorHom_id _ _ SB.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SA.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SB.monoidal] using h.symm)
    (by
      intro M
      have h := (hε M).2
      rw [hleft] at h
      apply (cancel_epi (F.map (SA.monoidal.rightUnitor M).hom)).1
      apply (cancel_mono (SB.monoidal.rightUnitor (F.obj M)).hom).1
      simpa only [F, SA, SB, μ, Category.assoc,
        ← (pullbackTensorSequenceDerived l E g).map_comp_assoc, Iso.hom_inv_id,
        (pullbackTensorSequenceDerived l E g).map_id,
        Iso.symm_inv, Iso.app_hom,
        Category.id_comp, Iso.inv_hom_id, Category.comp_id,
        CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
        @MonoidalCategory.tensorHom_id _ _ SA.monoidal,
        @MonoidalCategory.tensorHom_id _ _ SB.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SA.monoidal,
        @MonoidalCategory.id_tensorHom _ _ SB.monoidal] using h.symm)
  exact finiteChange_compatible SA SB F μ ⟨s, fun _ _ ↦ rfl⟩
end Systems


section CompletedReindexing
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- Pullback of the nth completed-ring projection, followed by the uniquely
constant-section-normalized finite coefficient map.
Source: node proof step 1 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedRingProjection (n : ℕᵒᵖ) :
    (isoSectionwiseInverseImage g RingCat.{u+1}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      (integralCoefficientSheafSystem l E X).obj n :=
  (isoSectionwiseInverseImage g RingCat.{u+1}).map
      (limit.π (integralCoefficientSheafSystem l E Y) n) ≫
    isoSectionwiseConstantMap.{u, u} g
      (CommRingCat.of (ULift.{u+1} (finiteCoefficientRing l E (n.unop + 1))))

/-- The projection maps respect every coefficient quotient arrow.
Source: node proof step 1, Stacks 0H7J.
Proof: the limit projections respect every quotient. Constant-section maps
commute with quotient homomorphisms by the sheafification universal property.
Compose these two naturality equations.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedRingProjection_naturality {m n : ℕᵒᵖ} (f : m ⟶ n) :
    podCompletedRingProjection l E g m ≫ (integralCoefficientSheafSystem l E X).map f =
      podCompletedRingProjection l E g n := by
  have hπ := (isoReductionCompletedMap_existsUnique l E g).exists.choose_spec
  dsimp only [podCompletedRingProjection]
  rw [← hπ m.unop, ← hπ n.unop]
  simp only [Category.assoc, limit.w]

/-- The actual completed coefficient transport, constructed by the limit lift
of all finite projections. Source: node proof step 1, Stacks 0038
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedRingMap :
    (isoSectionwiseInverseImage g RingCat.{u+1}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      completedIntegralCoefficientSheafUnrestricted l E X :=
  limit.lift (integralCoefficientSheafSystem l E X)
    { pt := _
      π := { app := podCompletedRingProjection l E g
             naturality := fun _ _ f ↦
               (Category.id_comp _).trans (podCompletedRingProjection_naturality l E g f).symm } }

/-- Completed-ring transport is invertible with precisely the prescribed
projections. Source: node proof step 1, Stacks 0038.
Proof: the site equivalence preserves the inverse limit. Each finite coefficient
comparison is invertible. The induced map of limit cones is therefore invertible.
Its composites with the projections are the defining limit-lift equations.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedRingMap_isIso : IsIso (podCompletedRingMap l E g) := by
  have he : podCompletedRingMap l E g = (isoReductionCompletedMap l E g).hom := by
    apply limit.hom_ext
    intro n
    rw [podCompletedRingMap, limit.lift_π]
    exact ((isoReductionCompletedMap_existsUnique l E g).exists.choose_spec n.unop).symm
  rw [he]
  infer_instance

/-- Use the proved invertibility of the actual limit-lift map.
Source: Stacks 0038 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedRingMapIsIso : IsIso (podCompletedRingMap l E g) :=
  podCompletedRingMap_isIso l E g

attribute [local irreducible] podCompletedRingMap

/-- Exact inverse image on modules over the completed ring sheaf, sectionwise
with the transported coefficient action. Source: node proof step 1
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedModuleInverseImage : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  isoSectionwiseModuleInverseImage.{u, u} g (podCompletedRingMap l E g)

/-- Additivity inherited from the published exact sectionwise inverse image.
Source: Stacks 03DA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedModuleAdditive : (podCompletedModuleInverseImage l E g).Additive :=
  isoSectionwiseModuleInverseImage_additive.{u, u} g (podCompletedRingMap l E g)

/-- Left exactness inherited from the published inverse image.
Source: Stacks 03DA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedModuleLimits : PreservesFiniteLimits (podCompletedModuleInverseImage l E g) :=
  isoSectionwiseModuleInverseImage_limits.{u, u} g (podCompletedRingMap l E g)

/-- Right exactness inherited from the published inverse image.
Source: Stacks 03DA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedModuleColimits :
    PreservesFiniteColimits (podCompletedModuleInverseImage l E g) :=
  isoSectionwiseModuleInverseImage_colimits.{u, u} g (podCompletedRingMap l E g)

/-- The unbounded derived exact inverse-image equivalence, with the standard
termwise localization and its standard shift comparison.
Source: node proof steps 1--2 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedDerivedInverseImage := (podCompletedModuleInverseImage l E g).mapDerivedCategory

/-- The standard exact-derived shift structure on the sectionwise functor.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedDerivedCommShift :
    (podCompletedDerivedInverseImage l E g).CommShift ℤ :=
  letI := podCompletedModuleAdditive l E g
  letI := podCompletedModuleLimits l E g
  letI := podCompletedModuleColimits l E g
  inferInstanceAs ((podCompletedModuleInverseImage l E g).mapDerivedCategory.CommShift ℤ)

/-- Sectionwise completed inverse image is an equivalence.
Source: node proof steps 1--2.
Proof: reindex with the inverse scheme isomorphism and inverse coefficient map.
Both composites are identity on every coefficient projection, hence on the
completed ring and its actions. The identity-on-sections maps give the natural
unit and counit. Deriving preserves their inverse identities.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedInverseImage_equivalence :
    (podCompletedModuleInverseImage l E g).IsEquivalence ∧
      (podCompletedDerivedInverseImage l E g).IsEquivalence := by
  have h : (podCompletedModuleInverseImage l E g).IsEquivalence :=
    isoReduction_equivalence.{u, u} g (podCompletedRingMap l E g)
  let := h
  refine ⟨h, ?_⟩
  exact Functor.isEquivalence_mapDerivedCategory.{u + 2, u + 2, u + 1, u + 1,
    u + 2, u + 2} (podCompletedModuleInverseImage l E g)

/-- Restriction and reindexing agree by the inverse-image unit on every local
section. This specifies the ordinary comparison before passing to derived maps.
Source: node proof steps 1 and 8.
Proof: after scalar restriction the underlying sheaf of a finite module is
unchanged. The canonical isomorphism from intrinsic inverse image to sectionwise
reindexing sends its adjunction-unit section to restriction along the counit
of postcomposition/base-change. The completed ring map commutes with the finite
projection, so the same section map is linear for the completed action.
The unit determines the comparison uniquely: the finite inverse image is an
equivalence, so its adjunction unit is invertible. Cancel its section maps to
compare transformations on base-changed objects. Base change is itself an
equivalence of sites, so faithful precomposition extends this equality to every
object. The left-adjoint uniqueness comparison supplies the normalized map,
and the scalar-restriction square supplies its completed scalar action.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podFiniteRestrictionOrdinary_existsUnique (n : ℕ) :
    ∃! e : sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g ⋙
        scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E Y n ⋙ podCompletedModuleInverseImage l E g,
      ∀ (M : normalizedDVRModules l E Y n) (V : Y.ProEt)
        (x : M.val.obj (op V)),
        HEq (((e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V)))
          ((((sfIntrinsicConstantModuleAdjunction g
            (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op V)) x))
          ((M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
            (inferInstance : WeaklyEtale g) trivial).counit.app V).op) x) := by
  have he : podCompletedRingMap l E g = (isoReductionCompletedMap l E g).hom := by
    apply limit.hom_ext
    intro k
    rw [podCompletedRingMap, limit.lift_π]
    exact ((isoReductionCompletedMap_existsUnique l E g).exists.choose_spec k.unop).symm
  have hF : podCompletedModuleInverseImage l E g = isoReductionIntegralInverse l E g := by
    exact congrArg (fun c ↦ isoSectionwiseModuleInverseImage.{u, u} g c.hom)
      (show asIso (podCompletedRingMap l E g) = isoReductionCompletedMap l E g from
        Iso.ext he)
  rw [hF]
  let a := sfIntrinsicConstantModuleAdjunction g (finiteCoefficientRing l E (n + 1))
  let b := AlgebraicGeometry.ProEtale.finiteSectionwiseAdjunction.{u, u} l E g n
  let c := a.leftAdjointUniq b
  obtain ⟨s, hs⟩ := isoReduction_restrictionSquare.{u, u} l E g n
  have hsInv (M : normalizedDVRModules l E Y n) (U : X.ProEtᵒᵖ)
      (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
      (s.inv.app M).val.app U x = x := by
    have hi := moduleIso_hom_inv_apply (s.app M) U x
    change (s.inv.app M).val.app U ((s.hom.app M).val.app U x) = x at hi
    rw [hs] at hi
    exact hi
  let e := Functor.isoWhiskerRight c (scalarReductionRestriction l E X n) ≪≫ s.symm
  have hn (M : normalizedDVRModules l E Y n) (V : Y.ProEt)
      (x : M.val.obj (op V)) :
      ((e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V)))
          (((a.unit.app M).val.app (op V)) x) =
        (M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
          (inferInstance : WeaklyEtale g) trivial).counit.app V).op) x := by
    change (s.inv.app M).val.app _
      ((c.hom.app M).val.app _ ((a.unit.app M).val.app (op V) x)) = _
    rw [hsInv]
    exact congrArg (fun z ↦ z.val.app (op V) x)
      (Adjunction.unit_leftAdjointUniq_hom_app a b M)
  refine ⟨e, fun M V x ↦ heq_of_eq (hn M V x), ?_⟩
  intro e' he'
  have hpost : (MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale g)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence g).1
  let siteAdj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  have : (proEtaleBaseChange g).IsEquivalence :=
    siteAdj.isEquivalence_right_of_isEquivalence_left
  have hb : Functor.IsEquivalence
      (AlgebraicGeometry.ProEtale.inverseImageFiniteModules.{u, u} l E g n) :=
    isoReduction_equivalence.{u, u} g _
  have : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g).IsEquivalence :=
    Functor.isEquivalence_of_iso c.symm
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  have : IsIso (a.unit.app M).val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map (a.unit.app M)))
  have hlevel (V : Y.ProEt) :
      ((PresheafOfModules.toPresheaf _).map (e'.hom.app M).val).app
          (op ((proEtaleBaseChange g).obj V)) =
        ((PresheafOfModules.toPresheaf _).map (e.hom.app M).val).app
          (op ((proEtaleBaseChange g).obj V)) := by
    apply (cancel_epi
      (((PresheafOfModules.toPresheaf _).map (a.unit.app M).val).app (op V))).1
    ext x
    exact (eq_of_heq (he' M V x)).trans (hn M V x).symm
  apply ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (proEtaleBaseChange g).op).map_injective
  apply NatTrans.ext
  funext V
  exact hlevel V.unop

/-- The uniquely section-normalized ordinary coefficient restriction comparison.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteRestrictionOrdinary (n : ℕ) :=
  (podFiniteRestrictionOrdinary_existsUnique l E g n).exists.choose

/-- Derived finite restriction/reindexing comparison induced from that same
ordinary section map. Source: node proof step 8
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteRestriction (n : ℕ) :
    finiteDerivedPullback l E n g ⋙ coefficientFiniteDerivedRestriction l E X n ≅
      coefficientFiniteDerivedRestriction l E Y n ⋙ podCompletedDerivedInverseImage l E g :=
  letI := podCompletedModuleAdditive l E g
  letI := podCompletedModuleLimits l E g
  letI := podCompletedModuleColimits l E g
  (Functor.mapDerivedCategoryCompIso
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g)
    (scalarReductionRestriction l E X n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (podFiniteRestrictionOrdinary l E g n) ≪≫
      Functor.mapDerivedCategoryCompIso (scalarReductionRestriction l E Y n)
        (podCompletedModuleInverseImage l E g)


/-- The actual ordinary limit projection, with the restriction/evaluation identity.
Source: Stacks 0941 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podOrdinaryProjection (W : Scheme.{u}) (n : ℕ) :
    pullbackTensorOrdinaryLimit l E W ⟶
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  Functor.whiskerLeft (coefficientSequenceRestriction l E W) (lim.π (op n)) ≫
    eqToHom (coefficientSequenceRestriction_evaluation l E W n)

/-- The unit-normalized ordinary system/finite pullback comparison.
Source: node proof step 12 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podSystemEvaluationOrdinary (n : ℕ) :
    pullbackTensorSequenceInverse l E g ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g :=
  (pullbackTensorSequenceInverseEvaluation l E g n).symm ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
      (pullbackTensorLevelIntrinsic l E g n)

/-- Ordinary limits commute with the exact equivalence, uniquely on all projections.
Source: node proof step 8, Stacks 0038.
Proof: the two functors take the ordinary limit of the same reindexed diagram.
The finite restriction comparisons identify their cones. The limit universal
property supplies the comparison and its inverse, and jointly monic ordinary
projections prove naturality and uniqueness.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podOrdinaryLimitReindexing_existsUnique :
    ∃! e : pullbackTensorSequenceInverse l E g ⋙ pullbackTensorOrdinaryLimit l E X ≅
        pullbackTensorOrdinaryLimit l E Y ⋙ podCompletedModuleInverseImage l E g,
      ∀ (N : coefficientSequenceModules l E Y) (n : ℕ),
        e.hom.app N ≫ (podCompletedModuleInverseImage l E g).map
          ((podOrdinaryProjection l E Y n).app N) =
        (podOrdinaryProjection l E X n).app ((pullbackTensorSequenceInverse l E g).obj N) ≫
        (scalarReductionRestriction l E X n).map
          ((podSystemEvaluationOrdinary l E g n).hom.app N) ≫
        (podFiniteRestrictionOrdinary l E g n).hom.app
          ((coefficientSequenceEvaluation l E Y n).obj N) := by
  sorry

/-- The ordinary projection-normalized limit comparison.
Source: Stacks 0038 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podOrdinaryLimitReindexing :=
  (podOrdinaryLimitReindexing_existsUnique l E g).exists.choose

/-- Resolution normalization for total derived-limit reindexing, imposed before
any finite evaluation. This is the right-derived universal-property square.
Source: node proof steps 8 and 13
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def PodLimitResolutionNormalization
    (e : pullbackTensorSequenceDerived l E g ⋙ coefficientSequenceLimit l E X ≅
      coefficientSequenceLimit l E Y ⋙ podCompletedDerivedInverseImage l E g) : Prop :=
  ∀ C : CochainComplex (coefficientSequenceModules l E Y) ℤ,
    pullbackTensorLimitUnit l E X
        (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj C) ≫
      (coefficientSequenceLimit l E X).map
        ((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.inv.app C) ≫
      e.hom.app (DerivedCategory.Q.obj C) =
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (podOrdinaryLimitReindexing l E g) (.up ℤ)).hom.app C) ≫
      (podCompletedModuleInverseImage l E g).mapDerivedCategoryFactors.inv.app
        (((pullbackTensorOrdinaryLimit l E Y).mapHomologicalComplex (.up ℤ)).obj C) ≫
      (podCompletedDerivedInverseImage l E g).map (pullbackTensorLimitUnit l E Y C)

/-- Exact reindexing commutes with functorial total derived limit, fixed on
resolutions and commuting with every actual finite reduction projection.
Source: node proof steps 8 and 13.
Proof: exact inverse reindexing transports null homotopies, hence K-injective
resolutions in the ordinary system category. Derive the single ordinary limit
comparison using those resolutions. The total derived-functor universal property
fixes the transformation by the displayed unit square, hence uniquely. The
ordinary projection equations give its derived projection equations. Inverse
reindexing gives its inverse. No equality of maps is inferred from finite
projections in a derived category.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podLimitReindexing_existsUnique :
    ∃! e : pullbackTensorSequenceDerived l E g ⋙ coefficientSequenceLimit l E X ≅
        coefficientSequenceLimit l E Y ⋙ podCompletedDerivedInverseImage l E g,
      PodLimitResolutionNormalization l E g e ∧
      ∀ (N : coefficientSequenceDerived l E Y) (n : ℕ),
        e.hom.app N ≫ (podCompletedDerivedInverseImage l E g).map
          ((coefficientSequenceProjection l E Y n).app N) =
        (coefficientSequenceProjection l E X n).app
          ((pullbackTensorSequenceDerived l E g).obj N) ≫
        (coefficientFiniteDerivedRestriction l E X n).map
          ((pullbackTensorDerivedEvaluation l E g n).hom.app N) ≫
        (podFiniteRestriction l E g n).hom.app
          ((coefficientSequenceDerivedEvaluation l E Y n).obj N) := by
  sorry

/-- The total derived-limit comparison fixed by resolutions and projections.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podLimitReindexing := (podLimitReindexing_existsUnique l E g).exists.choose
end CompletedReindexing


end WeilConjectures
