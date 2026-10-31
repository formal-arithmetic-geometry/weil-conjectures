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

private theorem transport_counit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
    (F : C ⥤ D) (G : D ⥤ C) (F' : C' ⥤ D') (G' : D' ⥤ C')
    (TX : C ⥤ C') (TY : D ⥤ D')
    (q : F ⋙ TY ≅ TX ⋙ F') (b : G ⋙ TX ≅ TY ⋙ G')
    (L : D) (eps : F.obj (G.obj L) ⟶ L)
    (eps' : F'.obj (G'.obj (TY.obj L)) ⟶ TY.obj L)
    (hc : q.hom.app (G.obj L) ≫ F'.map (b.hom.app L) ≫ eps' = TY.map eps)
    {M : C} (e : G.obj L ≅ M) :
    eps' = F'.map ((b.symm.app L ≪≫ TX.mapIso e).hom) ≫
      q.inv.app M ≫ TY.map (F.map e.inv ≫ eps) := by
  apply (cancel_epi (q.hom.app (G.obj L) ≫ F'.map (b.hom.app L))).mp
  rw [Category.assoc, hc]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← F'.map_comp_assoc]
  simp only [b.hom_inv_id_app]
  dsimp only [Functor.comp_obj] at *
  rw [F'.map_id, Category.id_comp]
  have hnat : F'.map (TX.map e.hom) ≫ q.inv.app M =
      q.inv.app (G.obj L) ≫ TY.map (F.map e.hom) := by
    simpa only [Functor.comp_map] using q.inv.naturality e.hom
  rw [reassoc_of% hnat]
  simp only [← TY.map_comp, Iso.hom_inv_id_app_assoc]
  rw [← F.map_comp_assoc, e.hom_inv_id, F.map_id, Category.id_comp]

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

/-- The rational identification is exactly the transported inverse integral purity map.
Source: corollary proof Step 2, coefficient comparison for exceptional pullback
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rationalIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S (.rational (fieldStage P))).G.obj
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      rationalTwist P X (X ↘ Spec (.of P.field.k)) d :=
  ((S.fields.rationalizationComparison (compactification P X) (fieldStage P)).b.symm.app
    (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) ≪≫
  (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
    (fieldStage P) X).mapIso (integralIdentification P X S d)

attribute [local irreducible] rationalIdentification

set_option maxHeartbeats 1600000 in
-- The elaboration of this declaration ran out of the default 200000 heartbeats in the red global
-- build of 2026-10-25 against the newer dependencies; the statement is unchanged.
/-- Rational integration is the specified scalar transport of normalized integral
integration, through the compact-support coefficient comparison.
Source: corollary proof Steps 2--3
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def rationalIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S (.rational (fieldStage P))).F.obj
        (rationalTwist P X (X ↘ Spec (.of P.field.k)) d) ⟶
      rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0 :=
  (S.fields.rationalizationComparison (compactification P X) (fieldStage P)).q.inv.app
      (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (fieldStage P) (Spec (.of P.field.k))).map
        (integralCounit P X S d (integralIdentification P X S d))

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

/-- The closed coefficient unit and its twist represented over the selected finite
stage. The representative uses the actual size transport and common-stage inclusion.
Source: corollary proof Step 2, Qbar_X(d)[2d]
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def closedTwist (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  (commonInclusion P T).obj ((modelScalar P T).obj (rationalTwist P T aT d))

/-- Transport the rational identification first through the specified small-model
coefficient change and then through the common-stage exceptional comparison.
Source: corollary proof Step 2, transported Qbar purity
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def closedIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S .closed).G.obj (closedTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      closedTwist P X (X ↘ Spec (.of P.field.k)) d :=
  ((S.common.commonComparison (compactification P X) (fieldIndex P)).b.symm.app
      ((modelScalar P (Spec (.of P.field.k))).obj
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0))) ≪≫
    (commonInclusion P X).mapIso
      (((S.fields.rationalComparison (compactification P X) (fieldStage P)
          (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
            (fieldIndex P)) (modelEmbedding P)).b.symm.app
              (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) ≪≫
        (modelScalar P X).mapIso (rationalIdentification P X S d))

attribute [local irreducible] closedIdentification

/-- Qbar integration is common-stage descent of the same rationalized integral map.
The compact-support comparisons are the published normalized q maps.
Source: corollary proof Step 3, transported normalized integration
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def closedIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S .closed).F.obj
        (closedTwist P X (X ↘ Spec (.of P.field.k)) d) ⟶
      closedTwist P (Spec (.of P.field.k)) (𝟙 _) 0 :=
  (S.common.commonComparison (compactification P X) (fieldIndex P)).q.inv.app
      ((modelScalar P X).obj (rationalTwist P X (X ↘ Spec (.of P.field.k)) d)) ≫
    (commonInclusion P (Spec (.of P.field.k))).map
      ((S.fields.rationalComparison (compactification P X) (fieldStage P)
          (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
            (fieldIndex P)) (modelEmbedding P)).q.inv.app
              (rationalTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
        (modelScalar P (Spec (.of P.field.k))).map (rationalIntegration P X S d))

/-- The rational and algebraically closed counit clauses of the smooth dualizing
corollary. Together with existsUnique_integralIdentification these cover exactly
O_E, E and Qbar_l; none of the three integration maps has an arbitrary scalar factor.
The functors on Spec k are the sheaf coordinates of the recorded ordinary compact
cohomology, so applying the recorded coefficient-point fibre gives RΓ_c -> Lambda.

Source: current blueprint cor-pur-adic-and-rational-smooth-dualizing-complexes
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: Step 1 is existsUnique_integralIdentification: reconstruct finite normalized
purity at the completed unit, identify its pullback with the completed unit on X,
and invert. Step 2 applies rationalization to that inverse, with the exceptional
coefficient comparison b. Size-transport the same rational representative and descend
it to the common-stage category to get the Qbar identification. These are exactly
rationalIdentification and closedIdentification, so they invert transported purity.
Step 3 applies the counit equation of each recorded coefficient comparison. It says
that q inverse followed by the scalar-extended old trace is the new counit after
compact-support image of the transported identification. First use rationalization,
then the small-model field change, then common-stage inclusion. Finite normalization
is inherited from the coordinate Kummer orientation in finiteIntegration; on affine
space its ordered product of normalized A1 classes integrates to one. No global
fundamental class or assertion that integration is invertible is made for arbitrary X.
Finally the coefficient-point fibre identifies the unit with the scalar coefficient
complex and the compact-support value with the recorded RΓ_c. -/
theorem adic_and_rational_smooth_dualizing_complexes (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    IsNormalizedIntegralIntegration P X d
      (integralCounitAmbient P X S d (integralIdentification P X S d)) ∧
    ((operation P X S (.rational (fieldStage P))).adjunction.counit.app
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0) =
      (operation P X S (.rational (fieldStage P))).F.map
          (rationalIdentification P X S d).hom ≫ rationalIntegration P X S d) ∧
    ((operation P X S .closed).adjunction.counit.app
        (closedTwist P (Spec (.of P.field.k)) (𝟙 _) 0) =
      (operation P X S .closed).F.map
          (closedIdentification P X S d).hom ≫ closedIntegration P X S d) := by
  let R := S.fields.rationalizationComparison (compactification P X) (fieldStage P)
  let := R.shiftX
  let := R.shiftY
  have hr : (operation P X S (.rational (fieldStage P))).adjunction.counit.app
      (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0) =
      (operation P X S (.rational (fieldStage P))).F.map
        (rationalIdentification P X S d).hom ≫ rationalIntegration P X S d := by
    unfold rationalIdentification rationalIntegration integralCounit
    exact transport_counit _ _ _ _ _ _ R.q R.b _ _ _
      (R.comparison.counit _) (integralIdentification P X S d)
  refine ⟨?_, hr, ?_⟩
  · unfold integralIdentification
    exact (existsUnique_integralIdentification P X S d).exists.choose_spec
  · let E := ConstructibleExceptionalCoefficients.commonField P.coefficients.l
      P.coefficients.Qbar (fieldIndex P)
    let M := S.fields.rationalComparison (compactification P X) (fieldStage P)
      E (modelEmbedding P)
    let C := S.common.commonComparison (compactification P X) (fieldIndex P)
    let := M.shiftX
    let := M.shiftY
    let := C.shiftX
    let := C.shiftY
    let A := operation P X S (.rational E)
    let eM := (M.b.symm.app (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) ≪≫
      (modelScalar P X).mapIso (rationalIdentification P X S d)
    let tM := M.q.inv.app (rationalTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
      (modelScalar P (Spec (.of P.field.k))).map (rationalIntegration P X S d)
    have hri : (operation P X S (.rational (fieldStage P))).F.map
        (rationalIdentification P X S d).inv ≫
        (operation P X S (.rational (fieldStage P))).adjunction.counit.app
          (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0) =
        rationalIntegration P X S d := by
      rw [hr, ← Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    have hm : A.adjunction.counit.app
        ((modelScalar P (Spec (.of P.field.k))).obj
          (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) = A.F.map eM.hom ≫ tM := by
      dsimp only [eM, tM]
      rw [← hri]
      exact transport_counit _ _ _ _ _ _ M.q M.b _ _ _
        (M.comparison.counit _) (rationalIdentification P X S d)
    have hmi : A.F.map eM.inv ≫ A.adjunction.counit.app
        ((modelScalar P (Spec (.of P.field.k))).obj
          (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) = tM := by
      rw [hm, ← Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    unfold closedIdentification closedIntegration
    change _ = (operation P X S .closed).F.map
      ((C.b.symm.app ((modelScalar P (Spec (.of P.field.k))).obj
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) ≪≫
        (commonInclusion P X).mapIso eM).hom) ≫
      C.q.inv.app ((modelScalar P X).obj
        (rationalTwist P X (X ↘ Spec (.of P.field.k)) d)) ≫
      (commonInclusion P (Spec (.of P.field.k))).map tM
    rw [← hmi]
    exact transport_counit _ _ _ _ _ _ C.q C.b _ _ _ (C.comparison.counit _) eM

end AdicSmoothDualizing
end WeilConjectures
