/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingIntegralData
import WeilConjectures.SmoothPurity.Derived.DerivedCompleteFiniteReductionDetection
import WeilConjectures.SixFunctors.Integral.IntegralReductionShiftedHomFiniteQcqs
import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingIntegralNormalization
import WeilConjectures.SmoothPurity.PurUnitTrace.AdicUnitTraceTargetNormalization

/-! # Finite detection of completed-line counit pairings

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-cor-sp-all-coefficients/cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md.
(blueprint: lem-pur-adic-smooth-dualizing-integral-detection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicSmoothDualizing

private theorem lineProjection_zero (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (n : ℕ) : lineProjection P T n 0 =
      constantCoefficientProjection P.coefficients.l P.extension T n := by
  let M := (scalarReductionRestriction P.coefficients.l P.extension T n).obj
    (SheafOfModules.unit (integralCoefficientSheaf P.coefficients.l P.extension T n))
  apply (SheafOfModules.unitHomEquiv M).injective
  have he := (SheafOfModules.unitHomEquiv M).apply_symm_apply
    (PresheafOfModules.sectionsMk
      (fun W ↦ (1 : (integralCoefficientSheaf P.coefficients.l P.extension T n).obj.obj W))
      (fun {_ _} f ↦ map_one
        ((integralCoefficientSheaf P.coefficients.l P.extension T n).obj.map f).hom))
  apply Eq.trans _ he.symm
  ext W
  have h := (existsUnique_lineProjection P T n 0).exists.choose_spec W 1 Fin.elim0
  have hp := map_one ((completedIntegralCommRingProjectionUnrestricted
    P.coefficients.l P.extension T n).hom.app W).hom
  simp only [generator] at h
  have hh := congrArg (fun a :
      (integralCoefficientSheaf P.coefficients.l P.extension T n).obj.obj W ↦
    @SMul.smul _
      ((finiteCoefficientTwist P.coefficients.l P.extension T n (0 : ℤ)).val.obj W)
      (((finiteCoefficientTwist P.coefficients.l P.extension T n (0 : ℤ)).val.obj W
        ).isModule.toSMul) a
      (finiteTateProPowerGenerator P.coefficients.l P.extension n T W 1 0 Fin.elim0)) hp
  have h1 : @SMul.smul _
      ((finiteCoefficientTwist P.coefficients.l P.extension T n (0 : ℤ)).val.obj W)
      (((finiteCoefficientTwist P.coefficients.l P.extension T n (0 : ℤ)).val.obj W
        ).isModule.toSMul)
      (1 : (integralCoefficientSheaf P.coefficients.l P.extension T n).obj.obj W)
      (finiteTateProPowerGenerator P.coefficients.l P.extension n T W 1 0 Fin.elim0) =
        (1 : (integralCoefficientSheaf P.coefficients.l P.extension T n).obj.obj W) := by
    simp only [finiteTateProPowerGenerator, map_one]
    exact @one_smul _ _ _
      ((finiteCoefficientTwist P.coefficients.l P.extension T n (0 : ℤ)).val.obj W
        ).isModule.toDistribMulAction.toMulAction _
  exact h.trans (hh.trans h1)

private theorem transpose_leftAdjointUniq
    {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    {K : C} {M : D} (t : K ⟶ G.obj M) :
    (a.homEquiv K M).symm t =
      (a.leftAdjointUniq b).hom.app K ≫ (b.homEquiv K M).symm t := by
  apply (a.homEquiv K M).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
  exact ((b.homEquiv K M).apply_symm_apply t).symm

private theorem twistReduction_zero_isIso (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (n : ℕ) :
    IsIso (twistReduction P T aT n 0) := by
  let φ := PurCompactSupport.projection P.coefficients.l P.extension
    (n + 1) (Nat.succ_pos n) T
  let c := ((pbcDerivedScalarAdjunction φ).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor _ 0).map (lineProjection P T n 0) ≫
      ((pbcRestrict φ).mapDerivedCategorySingleFunctor 0).inv.app _)
  have hc : c = (PurCompactSupport.finiteReductionIso P.coefficients.l P.extension T n).hom.app
      (integralConstantCoefficientObject P.coefficients.l P.extension T) ≫
        constantCoefficientReductionMap P.coefficients.l P.extension T n := by
    dsimp only [c]
    rw [lineProjection_zero]
    exact transpose_leftAdjointUniq (pbcDerivedScalarAdjunction φ)
      (derivedScalarExtensionRestrictionAdjunction P.coefficients.l P.extension T n).choose _
  have hred : IsIso (constantCoefficientReductionMap P.coefficients.l P.extension T n) :=
    ((integralConstantCoefficient_constructible P.coefficients.l P.extension T P.field
      P.coefficients.different).2.2.2 n).1
  have hC : IsIso c := by
    rw [hc]
    exact ((PurCompactSupport.finiteReductionIso P.coefficients.l P.extension T n).app
      (integralConstantCoefficientObject P.coefficients.l P.extension T) ≪≫
        @asIso _ _ _ _
          (constantCoefficientReductionMap P.coefficients.l P.extension T n) hred).isIso_hom
  unfold twistReduction
  change IsIso (_ ≫ (shiftFunctor _ (2 * (0 : ℤ))).map c ≫ _)
  exact (((pbcDerivedExtend φ).commShiftIso (2 * (0 : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (0 : ℤ))).mapIso (@asIso _ _ _ _ c hC) ≪≫
      (finitePowerComparison P T aT n 0).symm).isIso_hom

variable (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := X ↘ Spec (.of P.field.k)))

/-- Finite counit pairings detect arrows into the integral exceptional coefficient unit.
Neither arrow is assumed invertible or normalized; smoothness is not required.

Source: smooth-dualizing corollary uniqueness, constructible mapping-limit argument
and finite-group Mittag-Leffler detection
(blueprint: lem-pur-adic-smooth-dualizing-integral-detection).

Proof: the power-zero root projection is the regular coefficient projection, by its
specified value on the unit section and the unit-Hom equivalence. Transposition
through the two normalized scalar adjunctions identifies its derived map with the
known invertible constantCoefficientReductionMap. The shift and finite power
comparisons are isomorphisms, so twistReduction in degree zero cancels.
Naturality of finiteReductionIso converts the resulting equality into equality
of scalar reductions of the two ambient traces. The target is the derived-complete
coefficient unit; the source is constructible, since S.left identifies it with
compact support inside the constructible finite-Tor category. The finite shifted
Hom theorem on the finite-type base point kills the Milnor obstruction. Therefore
derivedComplete_finiteReduction_ext identifies the traces. Cancel inverse S.left,
use full faithfulness of the constructible inclusion, and apply injectivity of the
exceptional adjunction's Hom equivalence to identify the original arrows. This
uses the actual finite shifted-Hom hypothesis, rather than unconditional joint
faithfulness of derived finite reductions. It includes d=0 and empty schemes. -/
theorem integralTrace_reductions_hom_ext (d : ℕ)
    (g h : integralTwist P X (X ↘ Spec (.of P.field.k)) d ⟶
      (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0))
    (heq : ∀ n : ℕ,
      (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n) (Spec (.of P.field.k)))).map (integralTrace P X S d g) ≫
          twistReduction P (Spec (.of P.field.k)) (𝟙 _) n 0 =
      (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n) (Spec (.of P.field.k)))).map (integralTrace P X S d h) ≫
          twistReduction P (Spec (.of P.field.k)) (𝟙 _) n 0) : g = h := by
  let K := integralTwist P X (X ↘ Spec (.of P.field.k)) d
  let Q := integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0
  let M := (operation P X S (.integral (fieldStage P))).F.obj K
  let A := (PurCompactSupport.image
    (PurCompactSupport.completed P.coefficients.l P.extension) (compactification P X)).obj K.obj
  have hA : sfIntegralConstructible P.coefficients.l P.extension
      (Spec (.of P.field.k)) A :=
    (sfIntegralConstructible_isClosedUnderIsomorphisms P.coefficients.l P.extension
      (Spec (.of P.field.k))).of_iso
        ((S.ring.left (compactification P X) (.integral (fieldStage P))).app K) M.property.1
  have hfin (n : ℕ) : Finite (A⟦(1 : ℤ)⟧ ⟶
      (sfDerivedReductionRestricted P.coefficients.l P.extension
        (Spec (.of P.field.k)) n).obj Q.obj) :=
    integralReduction_shiftedHom_finite_qcqs P.field P.coefficients.l
      P.coefficients.different P.extension (sixFunctorPoint P.field)
      ⟨A, hA⟩ ⟨Q.obj, Q.property.1⟩ n
  have ht : integralTrace P X S d g = integralTrace P X S d h := by
    apply derivedComplete_finiteReduction_ext P.coefficients.l P.extension
      (Spec (.of P.field.k)) Q.property.1.1 hfin
    intro n
    have : IsIso (twistReduction P (Spec (.of P.field.k)) (𝟙 _) n 0) :=
      twistReduction_zero_isIso P _ _ n
    have hp := (cancel_mono (twistReduction P (Spec (.of P.field.k)) (𝟙 _) n 0)).mp
      (heq n)
    let I := PurCompactSupport.finiteReductionIso P.coefficients.l P.extension
      (Spec (.of P.field.k)) n
    apply (cancel_epi (I.hom.app A)).mp
    exact (I.hom.naturality (integralTrace P X S d g)).symm.trans
      ((congrArg (fun v ↦ v ≫ I.hom.app Q.obj) hp).trans
        (I.hom.naturality (integralTrace P X S d h)))
  apply ((operation P X S (.integral (fieldStage P))).adjunction.homEquiv _ _).symm.injective
  apply (finiteTorConstructibleIntegral P.coefficients.l P.extension
    (Spec (.of P.field.k))).ι.map_injective
  exact (cancel_epi ((S.ring.left (compactification P X)
    (.integral (fieldStage P))).inv.app K)).mp ht

end WeilConjectures.AdicSmoothDualizing

-- Compatibility API retained while the public corollary uses condensed coefficients.
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w₁ w₂
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures
namespace AdicSmoothDualizing

open AlgebraicGeometry.Scheme

attribute [local irreducible] PurCompactSupport.image
  sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar

variable (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]

variable (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
  P.field P.coefficients.different (f := X ↘ Spec (.of P.field.k)))

/-- The integral clause of the corollary, including its canonical normalization.
The unit is the completed regular coefficient module (power zero), and its reduction
at every positive level is the free rank-one finite coefficient unit.

Source: current blueprint cor-pur-adic-and-rational-smooth-dualizing-complexes,
proof Step 1 and normalized-integration paragraph
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: apply thm-pur-adic-reconstruction to the completed coefficient unit.
Each finite reduction is the free coefficient module with Tor interval [0,0].
The finite purity maps are isomorphisms and their scalar-naturality makes them a
map of normalized systems. Reconstruction gives an isomorphism from the completed
twisted pullback of the unit to its exceptional pullback. Pullback of the completed
unit is the completed unit on X. Invert the reconstructed isomorphism to obtain e.
The reconstructed counit reduces to the finite normalized smooth trace: its factors
are finite purity followed by the exceptional counit. The root projections,
coefficient multiplication and even-shift comparisons are precisely twistReduction.
Thus its normalization is the displayed IsNormalizedIntegralIntegration predicate.
For uniqueness transpose under the exceptional adjunction and reduce to the same
finite purity morphism at every level. Use the already constructed isomorphism to
identify the dualizing object with the shifted line. Degree-zero full faithfulness
then identifies a difference with an ordinary endomorphism of that completed line.
The root projections and completed coefficient projections are jointly injective, so
an endomorphism vanishing at every finite quotient is zero. Thus the isomorphisms agree.
No uniqueness assertion about arbitrary triangulated homotopy-limit maps is used. -/
theorem existsUnique_integralIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    ∃! e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
        integralTwist P X (X ↘ Spec (.of P.field.k)) d,
      IsNormalizedIntegralIntegration P X d (integralCounitAmbient P X S d e) := by
  let K := integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0
  obtain ⟨unit⟩ := CompletedUnitPullback.completedUnitPullbackTower P
    (X ↘ Spec (.of P.field.k))
  let core := unit.core
  obtain ⟨normal, hn⟩ := PurUnitTrace.unit_trace_target_normalization
    P.field P.coefficients P.extension (X ↘ Spec (.of P.field.k)) d S.ring
  obtain ⟨a, ha, _, _, hred, _⟩ := purAdicReconstruction
    P.field P.coefficients P.extension (X ↘ Spec (.of P.field.k)) d K.obj K.property
  let aIso := @asIso _ _ _ _ a ha
  obtain ⟨e, he⟩ := hn K
  let j := integralUnitSourceComparison P X d core
  let g : integralTwist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P X S (.integral (fieldStage P))).G.obj K :=
    ObjectProperty.isoMk _ (j.symm ≪≫ aIso ≪≫ e)
  have hg : PurUnitTrace.HasPrescribedReductions P.field P.coefficients P.extension
      (X ↘ Spec (.of P.field.k)) d S.ring normal K (j.hom ≫ g.hom.hom) := by
    intro n
    have hh := (hred n).2.2
    have hn := he n
    have hj : j.hom ≫ g.hom.hom = a ≫ e.hom := by
      dsimp only [g, aIso, ObjectProperty.isoMk, Iso.trans_hom, Iso.symm_hom,
        asIso_hom, ObjectProperty.homMk_hom]
      exact j.hom_inv_id_assoc _
    have hf := congrArg
      ((scalarReductionDerivedExtension P.coefficients.l P.extension X n).map) hj
    have hc := congrArg (fun v ↦ v ≫
      PurUnitTrace.targetReduction P.field P.coefficients P.extension
        (X ↘ Spec (.of P.field.k)) S.ring normal K n) hf
    apply (heq_of_eq hc).trans
    have hcomp := (scalarReductionDerivedExtension
      P.coefficients.l P.extension X n).map_comp a e.hom
    apply (heq_of_eq (congrArg (fun v ↦ v ≫
      PurUnitTrace.targetReduction P.field P.coefficients P.extension
        (X ↘ Spec (.of P.field.k)) S.ring normal K n) hcomp)).trans
    apply (heq_of_eq (Category.assoc _ _ _)).trans
    exact (heq_of_eq (congrArg (fun v ↦
      (scalarReductionDerivedExtension P.coefficients.l P.extension X n).map a ≫ v)
      (eq_of_heq hn))).trans (heq_of_eq hh)
  have hnorm := integralIdentification_normalized_of_prescribed P X S d normal core g hg
  refine ⟨g.symm, hnorm, ?_⟩
  intro e' he'
  apply Iso.ext_inv
  apply integralTrace_reductions_hom_ext P X S d
  intro n
  have h := (he' n).symm.trans (hnorm n)
  have ht (q : (operation P X S (.integral (fieldStage P))).G.obj K ≅
      integralTwist P X (X ↘ Spec (.of P.field.k)) d) :
      integralTrace P X S d q.inv = integralCounitAmbient P X S d q := by
    rw [integralTrace, integralCounitAmbient, integralCounit, Adjunction.homEquiv_counit]
  rw [← ht e', ← ht g.symm] at h
  exact h

/-- The canonical integral identification is selected only after its normalized
integration property has determined it uniquely.
Source: corollary, omega_X = O_E,X(d)[2d]
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integralIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S (.integral (fieldStage P))).G.obj
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
        integralTwist P X (X ↘ Spec (.of P.field.k)) d :=
  (existsUnique_integralIdentification P X S d).exists.choose

attribute [local irreducible] integralIdentification

/-- The rational coefficient unit and its shifted twist, using the literal
rationalization of the same completed integral representatives.
Source: corollary proof Step 2, rationalization
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rationalTwist (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
    (fieldStage P) T).obj (integralTwist P T aT d)

attribute [local irreducible] rationalIdentification

set_option maxHeartbeats 1600000 in
-- The elaboration of this declaration ran out of the default 200000 heartbeats in the red global
-- build of 2026-10-25 against the newer dependencies; the statement is unchanged.
/-- The selected field's index in the recorded common-stage category.
Source: corollary proof Step 2, descent of a finite coefficient stage
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def fieldIndex : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar :=
  ⟨P.extension, P.finiteExtension⟩

/-- The prescribed small-model transport, retaining its actual algebra equivalence.
Source: corollary proof Step 2, common-stage size convention
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def modelEmbedding : P.extension →ₐ[Padic P.coefficients.l]
    AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (fieldIndex P) :=
  (Shrink.algEquiv (Padic P.coefficients.l) P.extension).symm.toAlgHom

/-- Scalar transport to that small coefficient model uses the existing rational tensor
functor, with no equality imposed on coefficient and site universes.
Source: corollary proof Step 2, common-stage descent
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev modelScalar (T : Scheme.{u}) :=
  ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l P.coefficients.Qbar
    (fieldStage P)
    (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
      (fieldIndex P)) (modelEmbedding P) T

/-- The actual common-stage inclusion of the selected coefficient field.
Source: corollary proof Step 2, Qbar coefficients
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev commonInclusion (T : Scheme.{u}) :=
  ConstructibleExceptionalCoefficients.commonInclusion P.coefficients.l P.coefficients.Qbar
    T (fieldIndex P)

attribute [local irreducible] closedIdentification

end AdicSmoothDualizing
end WeilConjectures
