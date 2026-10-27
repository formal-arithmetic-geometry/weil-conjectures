/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.TowerTracePurityComparisonData
import Sheaf.Paper.TowerTraceNormalizedPresentations
import Sheaf.Paper.TowerTraceOrientationUniqueness
import Sheaf.Paper.TowerTraceScalarCounit
import Sheaf.Paper.TowerTraceCanonicalIntegral

/-! # Assembly of tower and trace purity

Source: tower gamma (1)--(2), field extension (2)--(3), and purity transport.
(blueprint: lem-pur-tower-trace-purity-comparison). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.TowerTracePurityComparison

-- Insert a factorization without simplifying the morphisms on either side.
private theorem insert_composite {C : Type*} [Category C] {W X Y Z T : C}
    (s : W ⟶ X) (a : X ⟶ Y) (b : Y ⟶ Z) (t : Z ⟶ T) (v : X ⟶ Z)
    (h : v = a ≫ b) : s ≫ v ≫ t = s ≫ a ≫ b ≫ t := by
  rw [h, Category.assoc]

variable (P : PurityFiniteSetting.{u})

variable {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))]
  (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]

attribute [local irreducible] sfRationalScalarExtension rationalDerivedPullback
  rationalDerivedTensor ScalarLocalization.category
  tower orientation counitTrace extendedTrace commonImage
  RationalSmoothPurityCanonical.integralMap RationalSmoothPurityCanonical.rationalIso
  RationalSmoothPurityCanonical.rationalSourceComparison
  RationalSmoothPurityCanonical.sourceScalar RationalSmoothPurityCanonical.rationalSource

attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category

set_option maxHeartbeats 300000 in
-- Comparing the dependent integral and rational coefficient presentations requires
-- more than the default heartbeat allowance for the source and scalar-square conversions.
/-- Tower purity equals reconstructed-trace purity, for every permitted base-field
orientation, every finite coefficient field, and every common finite-Tor input.
The existential data supply normalized presentations of the specified constructions;
the source and exceptional target are not replaced by arbitrary morphisms.
Source: latest blueprint, tower-gamma proof (1)--(2), field-extension-towers proof
(2)--(3), and rational-and-Qbar purity transport Steps 1--2
(blueprint: lem-pur-tower-trace-purity-comparison).

Proof:
1. Apply lem-pur-tower-purity-realized-transpose at every finite coefficient field,
using the fixed compactification and the canonical source realization. Its unit
map and any g0 with the displayed finite reductions agree by
lem-pur-integral-orientation-reduction-injectivity. Thus g0 = a^T_0 and their
counit traces are equal. This uses rank-one orientation injectivity only.
2. Apply det-sp-field-extension-towers (2). Its purity and counit comparisons carry
the base unit orientation and counit to those at E. Naturality of the compact-support
comparison gives exactly t_E = epsilon_E P_E(a^T_E), with the displayed inverse
coefficient and twist comparisons. The ordinary/strict scalar comparison identifies
the ell-power and uniformizer-power systems cofinally.
3. The adjunct identity of lem-pur-tower-purity-realized-transpose identifies the
counit adjunct of gamma^T with inverse projection followed by tensoring with this
unit trace. This is the defining adjunct of tracePurity. Injectivity of the specified
adjunction Hom equivalence gives tracePurity = gamma^T integrally for every K.
4. The integral representatives of lem-pur-adic-purity-scalar-naturality in their
trace-transpose presentation are precisely tracePurity. Apply scalar localization
of def-weil-pbc-rational-category and the canonical comparisons of
thm-pur-rational-and-qbar-purity and det-sp-field-extension-towers (3). These preserve
the equality, as do further coefficient extension and the common-stage inclusions
of def-weil-pbc-qbar-category. The rational assertion names rationalIso itself and
uses rationalSourceComparison, the localized normalized tensor source, the specified
rationalizationComparison.b and representative_eq. For an inclusion E into F,
rationalIso_scalar supplies exactly the displayed sourceScalar and exceptional
rationalComparison.b; modelScalar and commonInclusion carry that equality to the
common category. Thus the previously specified family, including its finite-field
and common-stage comparisons, is identified with the actual tower map. -/
theorem tower_trace_purity_comparison : Comparison P j p d := by
  classical
  let : CompactSpace X := FieldExtensionTowers.compactSpace P X
  let : QuasiSeparatedSpace Y := FieldExtensionTowers.quasiSeparatedSpace P Y
  let : QuasiCompact (j ≫ p) := inferInstance
  let : IsSeparated (j ≫ p) := inferInstance
  let : LocallyOfFiniteType (j ≫ p) := inferInstance
  let : ∀ x : X, Invertible (P.coefficients.l : X.residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients X x).invertible
  let : ∀ y : Y, Invertible (P.coefficients.l : Y.residueField y) :=
    fun y ↦ (purAdicResidueUnit P.field P.coefficients Y y).invertible
  intro S
  obtain ⟨M, R, A, hA, hAdj⟩ := normalized_presentations P j p d S.ring
  have ht (E : FieldShriekSystem.Index P)
      (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :
      adicTranspose P.field P.coefficients E.val (j ≫ p) S.ring
          (SpTowerGamma.factorization j p) ⟨_, (A E).tensorTor K⟩ K
          (adicTraceMap P.coefficients.l E.val (A E).models (A E).openComparison
            (SpTowerGamma.factorization j p)
            (PurUnitTrace.tateUnit P.field P.coefficients E.val d X) K.obj
            ((A E).completionIso K) ((A E).projectionIso K)
            (counitTrace P j p d S.ring M E (R.model E) (A E)
              (orientation P j p d S.ring M E (R.model E) (A E)) ≫ (A E).unitIso.hom)) =
        (A E).tensorSource.inv.app K ≫ tower P j p d S.ring M E (R.model E) (A E) K := by
    have he := congrArg
      ((S.ring.operation (SpTowerGamma.factorization j p)
        (.integral { carrier := E.val })).adjunction.homEquiv ⟨_, (A E).tensorTor K⟩ K)
      (hAdj E K)
    simp only [Equiv.apply_symm_apply] at he
    exact congrArg (fun v ↦ v.hom) he.symm
  have hIntegral (E : FieldShriekSystem.Index P)
      (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :
      tracePurity P j p d S.ring M E (R.model E) (A E)
          (counitTrace P j p d S.ring M E (R.model E) (A E)
            (orientation P j p d S.ring M E (R.model E) (A E))) K =
        tower P j p d S.ring M E (R.model E) (A E) K := by
    dsimp only [tracePurity]
    rw [ht E K, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hRational (E : FieldShriekSystem.Index P)
      (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :
      (RationalSmoothPurityCanonical.rationalIso (atField P E) (j ≫ p)
        (SpTowerGamma.factorization j p) S d (rationalInput P E K)).hom =
          rationalTowerComponent P j p d S M E (R.model E) (A E) K := by
    let := (hA E).2
    have hi := (canonical_integral_transpose P j p d S M E (R.model E) (A E)
      (hA E).1 K).trans (ht E K)
    have hmap :
        (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldStage (atField P E)) X).map
            (RationalSmoothPurityCanonical.integralMap (atField P E) (j ≫ p)
              (SpTowerGamma.factorization j p) S d
              (RationalSmoothPurityCanonical.representative (atField P E)
                (rationalInput P E K))) =
          normalizedRationalSource P j p d S M E (R.model E) (A E) K ≫
            rationalTower P j p d S.ring M E (R.model E) (A E) K := by
      unfold normalizedRationalSource rationalTower
      change (sfRationalConstructibleLocalization P.coefficients.l E.val X).map
        (ObjectProperty.homMk
          (RationalSmoothPurityCanonical.integralMap (atField P E) (j ≫ p)
            (SpTowerGamma.factorization j p) S d K).hom :
          (PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l E.val X).obj
            (RationalSmoothPurityCanonical.integralSource (atField P E) (j ≫ p) d K) ⟶
            targetObject P j p S.ring E K) = _
      rw [← Functor.map_comp]
      apply congrArg (sfRationalConstructibleLocalization P.coefficients.l E.val X).map
      apply ObjectProperty.hom_ext
      exact hi
    unfold RationalSmoothPurityCanonical.rationalIso rationalTowerComponent
    simp only [Iso.trans_hom, Functor.mapIso_hom,
      RationalSmoothPurityCanonical.integralIso, asIso_hom]
    exact insert_composite
      (RationalSmoothPurityCanonical.rationalSourceComparison (atField P E) (j ≫ p) d
        (rationalInput P E K)).hom
      (normalizedRationalSource P j p d S M E (R.model E) (A E) K)
      (rationalTower P j p d S.ring M E (R.model E) (A E) K)
      ((S.fields.rationalizationComparison (SpTowerGamma.factorization j p)
        (AdicSmoothDualizing.fieldStage (atField P E))).b.hom.app
          (RationalSmoothPurityCanonical.representative (atField P E) (rationalInput P E K)) ≫
        (S.ring.operation (SpTowerGamma.factorization j p)
          (.rational (AdicSmoothDualizing.fieldStage (atField P E)))).G.map
            (eqToHom (RationalSmoothPurityCanonical.representative_eq (atField P E)
              (rationalInput P E K)))) _ hmap
  refine ⟨M, R, A, hA, ?_⟩
  intro g0 hg0
  have hg := prescribed_orientations_unique P j p d S.ring M (base P)
    (R.model (base P)) (A (base P)) g0.hom
    (orientation P j p d S.ring M (base P) (R.model (base P)) (A (base P)))
    hg0 (hA (base P)).1
  have hTrace (E : FieldShriekSystem.Index P) :
      extendedTrace P j p d S.ring M E (R.model E) (A E)
          (counitTrace P j p d S.ring M (base P) (R.model (base P)) (A (base P)) g0.hom) =
        counitTrace P j p d S.ring M E (R.model E) (A E)
          (orientation P j p d S.ring M E (R.model E) (A E)) := by
    rw [hg]
    exact scalar_counit P j p d S.ring M R A (fun F ↦ (hA F).1) E
  refine ⟨hg, hTrace, ?_⟩
  intro E K
  refine ⟨?_, hRational E K, ?_⟩
  · rw [hTrace E]
    exact hIntegral E K
  · intro F h
    have hs := RationalSmoothPurityCanonical.rationalIso_scalar (atField P E) (j ≫ p)
      (SpTowerGamma.factorization j p) S F (IntermediateField.inclusion h) d
      (rationalInput P E K)
    have hm := congrArg
      (ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
        P.coefficients.Qbar (AdicSmoothDualizing.fieldStage (atField P E))
        (AdicSmoothDualizing.fieldStage (atField P F)) (IntermediateField.inclusion h) X).map
      (hRational E K)
    have heq := congrArg
      (fun v ↦ v ≫
        (S.fields.rationalComparison (SpTowerGamma.factorization j p)
          (AdicSmoothDualizing.fieldStage (atField P E))
          (AdicSmoothDualizing.fieldStage (atField P F))
          (IntermediateField.inclusion h)).b.hom.app (rationalInput P E K)) hm
    exact congrArg ((commonImage P F X).map) (hs.symm.trans heq)

end WeilConjectures.TowerTracePurityComparison
