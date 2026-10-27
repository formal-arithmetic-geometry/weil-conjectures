module

public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.CompactSupportIntrinsicTensorComparison
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Paper.CompactSupportInputTowerCompatibility
import Sheaf.Paper.CompactSupportCoefficientTransition
import Sheaf.Paper.CompactSupportQuotientCocycle
import Sheaf.Paper.CompactSupportReductionAdjoint
import all Sheaf.Paper.CompactSupportFiniteAction
import all Sheaf.Paper.CoefficientSequenceRoosModel
import all Sheaf.Paper.CompactSupportReductionTower

/-! # Normalized realization of the specified compact-support quotient tower

Source: blueprint main-20261015, lem-coef-integral-compact-support, proof paragraph 2;
Stacks Tags 06YS, 0D6D, 07A6 and 05RT
(blueprint: lem-coef-compact-support-normalized-realization).

Natural index n always denotes the positive coefficient exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The sequence-system quotient is the direct quotient homomorphism on constant sheaves.
Source: Stacks Tag 03EK; blueprint input quotient maps
(blueprint: lem-coef-compact-support-normalized-realization).
Proof: induct on m-n. At equal levels both maps are identities; at consecutive levels
they are the coefficient transition. Quotient factors compose on every residue class,
and constant sheafification and forgetting commutativity preserve their compositions. -/
theorem coefCompactSupportQuotient_eq (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRQuotient l E W h =
      (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (compactSupportLevelSheafQuotient l E W m n h) := by
  exact compactSupportQuotient_eq l E W h

/-- Canonical identity transport from the sequence quotient to the direct quotient.
Source: blueprint quotient maps; Stacks Tag 03DA
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportRestrictionIso (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E W h ≅
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory :=
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
    (compactSupportLevelQuotient l E m n h)
  letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
    (compactSupportLevelQuotient l E m n h)
  Functor.mapDerivedCategoryNatIso
    (F := normalizedDVRModuleRes l E W h)
    (G := proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h))
    (eqToIso (congrArg (fun q ↦ SheafOfModules.restrictScalars.{u + 1} q)
      (coefCompactSupportQuotient_eq l E W h)))

/-- The iterated-reduction balancing map, defined as the normalized adjunct of rho.
Source: Stacks Tags 0D6D and 07A6
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportBeta (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource l E W)) :=
  ((pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E W m n h)).homEquiv
    _ _).symm (compactSupportReductionMap l E W m n h K)

/-- The actual input quotient transition in the sequence quotient coordinates.
Source: blueprint input reductions; Stacks Tag 03EK
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportInputTau (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) {m n : ℕ} (h : n ≤ m) :
    (scalarReductionDerivedExtension l E W m).obj K ⟶
      (normalizedDVRRes l E W h).obj ((scalarReductionDerivedExtension l E W n).obj K) :=
  compactSupportReductionMap l E W m n h K ≫
    (coefCompactSupportRestrictionIso l E W h).inv.app
      ((scalarReductionDerivedExtension l E W n).obj K)

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard constantSheaf Padic.coefficientExtensionIdeal
  coefficientSequenceEvaluation coefficientSequenceTransition
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence Functor.objPreimage Functor.objObjPreimageIso

/-- The quotient maps are independent of representatives, have identity units, and
satisfy every quotient cocycle. Their restriction is the recorded K-flat quotient tower:
its representative comparisons compute adjacent maps by id tensor q and hence all maps
by composition. This retains the actual maps, not only isomorphic objects.
Source: Stacks Tags 03EK, 06YY, 0D6D and 07A6; blueprint input reductions
(blueprint: lem-coef-compact-support-normalized-realization).
Proof: compute on one flat-term K-flat representative. Every quotient acts by
s tensor x ↦ q(s) tensor x. Identity quotients act identically; successive quotients
compose to the direct quotient. The normalized scalar-adjunction unit sends x to
1 tensor x, so its adjunct is this same map. The universal K-flat comparisons descend
these identities independently of the resolution. The recorded integral reduction
tower has exactly these adjacent maps, so finite composition gives the final equation
(lem-pur-derived-change-of-rings, lem-sfb-successive-derived-quotient-normalization,
lem-pur-sheaf-ring-derived-coefficient-adjunction). -/
theorem coefCompactSupportInput_properties (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (∀ n : ℕ, coefCompactSupportInputTau l E W K (Nat.le_refl n) ≫
      (normalizedDVRResUnit l E W n).hom.app
        ((scalarReductionDerivedExtension l E W n).obj K) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      coefCompactSupportInputTau l E W K (le_trans hmn hrm) ≫
          (normalizedDVRResComp l E W hrm hmn).inv.app
            ((scalarReductionDerivedExtension l E W n).obj K) =
        coefCompactSupportInputTau l E W K hrm ≫
          (normalizedDVRRes l E W hrm).map (coefCompactSupportInputTau l E W K hmn)) ∧
    (∀ (m n : ℕ) (h : n ≤ m),
      (scalarReductionDerivedRestriction l E W m).map
          (compactSupportReductionMap l E W m n h K) ≫
        (compactSupportRestrictionComp l E W m n h).hom.app
          ((scalarReductionDerivedExtension l E W n).obj K) =
        (sfIntegralReductionTower l E W K).map (homOfLE h).op) := by
  classical
  obtain ⟨S, _hS⟩ := coefficientDerivedSystemEvaluationCalculus.{u, u} l E W
  let N := S.reduction.obj K
  let e (n : ℕ) : (coefficientSequenceDerivedEvaluation l E W n).obj N ≅
      (scalarReductionDerivedExtension l E W n).obj K := (S.reductionEvaluation n).app K
  have he {m n : ℕ} (h : n ≤ m) :
      (coefficientSequenceDerivedTransition l E W h).app N ≫
          (normalizedDVRRes l E W h).map (e n).hom =
        (e m).hom ≫ coefCompactSupportInputTau l E W K h := by
    apply (cancel_mono ((coefCompactSupportRestrictionIso l E W h).hom.app
      ((scalarReductionDerivedExtension l E W n).obj K))).mp
    rw [Category.assoc, (coefCompactSupportRestrictionIso l E W h).hom.naturality,
      ← Category.assoc]
    have ht := NatTrans.congr_app (derivedTransition_direct l E W h) N
    change (coefficientSequenceDerivedTransition l E W h).app N ≫
      (coefCompactSupportRestrictionIso l E W h).hom.app
        ((coefficientSequenceDerivedEvaluation l E W n).obj N) = _ at ht
    rw [ht]
    simp only [coefCompactSupportInputTau, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact compactSupportReductionTransition l E W S.toCoefficientDerivedSystemReduction h K
  refine ⟨?_, ?_, compactSupportInput_completed_tower l E W K⟩
  · intro n
    apply (cancel_epi (e n).hom).mp
    rw [← Category.assoc, ← he]
    rw [Category.assoc, (normalizedDVRResUnit l E W n).hom.naturality]
    rw [← Category.assoc, derivedTransition_id]
    simp only [Functor.id_map, Category.id_comp, Category.comp_id]
  · intro r m n hrm hmn
    apply (cancel_epi (e r).hom).mp
    rw [← Category.assoc, ← he, Category.assoc,
      (normalizedDVRResComp l E W hrm hmn).inv.naturality]
    rw [← Category.assoc, derivedTransition_comp]
    dsimp only [Functor.comp_map]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [he hmn]
    simp only [Functor.map_comp]
    rw [← Category.assoc, he hrm]
    simp only [Category.assoc]

/-- The finite-level output transition, before restriction to completed coefficients.
Source: blueprint proof paragraph 2, specified coefficient maps
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportTau {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) {m n : ℕ} (h : n ≤ m) :=
  (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
      (compactSupportReductionMap l E X m n h K) ≫
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
      ((scalarReductionDerivedExtension l E X n).obj K)

/-- The output object at a positive coefficient level, in the recorded tower category.
Source: blueprint proof paragraph 2
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportLevel {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    normalizedDVRDerived l E Y n :=
  (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
    ((scalarReductionDerivedExtension l E X n).obj K)

/-- The specified output transition in the sequence quotient coordinates.
Source: blueprint proof paragraph 2
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportNormalizedTau {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource l E X))
    {m n : ℕ} (h : n ≤ m) :
    coefCompactSupportLevel l E c K m ⟶
      (normalizedDVRRes l E Y h).obj (coefCompactSupportLevel l E c K n) :=
  coefCompactSupportTau l E c K h ≫
    (coefCompactSupportRestrictionIso l E Y h).inv.app (coefCompactSupportLevel l E c K n)

/-- Finite-level derived tensor/restriction adjoint of the specified output transition.
Source: Stacks Tag 07A6; blueprint proof paragraph 2
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportAdjoint {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) {m n : ℕ} (h : n ≤ m) :=
  ((pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E Y m n h)).homEquiv
    _ _).symm (coefCompactSupportTau l E c K h)

/-- Adjacent restricted output transitions are exactly the defining integral-limit maps.
Source: blueprint proof paragraph 2, final sentence
(blueprint: lem-coef-compact-support-normalized-realization).
Proof: expand both definitions. The direct quotient at consecutive levels is the
specified coefficient transition, and both reduction maps are adjuncts of the same
unit. Their restriction associators preserve every underlying section, so coincide.
The same fixed compactification and proper/open restriction comparison appear in both. -/
theorem coefCompactSupportTau_adjacent {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (scalarReductionDerivedRestriction l E Y (n + 1)).map
        (coefCompactSupportTau l E c K (Nat.le_succ n)) ≫
      (compactSupportRestrictionComp l E Y (n + 1) n (Nat.le_succ n)).hom.app
        (coefCompactSupportLevel l E c K n) = sfCompactSupportTransition l E c K n := by
  rfl

/-- The first arrow in the specified tensor comparison factorization.
Source: blueprint proof paragraph 2; Stacks Tags 07A6 and 0GL6
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportTensor {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) {m n : ℕ} (h : n ≤ m) :=
  AlgebraicGeometry.ProEtale.intrinsicCompactSupportCoefficientComparison
    (compactSupportLevelQuotient l E m n h) c
    ((scalarReductionDerivedExtension l E X m).obj K)

attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

/-- Composition of scalar restrictions along a completed projection and a quotient.
Source: Stacks Tag 03DA; blueprint coherent realization
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportCompletedModuleComp
    (W : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E W h ⋙ completedIntegralRestrictScalars l E W D hl m ≅
      completedIntegralRestrictScalars l E W D hl n :=
  normalizedDVRRestrictionCompIso
      (completedIntegralCoefficientProjection l E W D hl m) (normalizedDVRQuotient l E W h) ≪≫
    eqToIso (congrArg (fun q ↦ SheafOfModules.restrictScalars.{u + 1} q)
      (limit.w (integralCoefficientSheafSystem l E W) (homOfLE h).op))

/-- All conclusions of the normalized realization, with its actual chain-level lift.
The normalized tower's finite objects are identified with precisely Rp_* j_! K_n.
The chain complexes retain their B_n action. The complex of strict completed-coefficient
sequences is itself a representative of the coherent tower, and its evaluation maps
identify both the complexes and every transition, not merely their cohomology.
Source: blueprint lem-coef-integral-compact-support, proof paragraph 2; Stacks Tag 05RT
(blueprint: lem-coef-compact-support-normalized-realization). -/
structure CoefCompactSupportRealization
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) where
  normalized : NormalizedDVRTower l E Y D hl
  levels : ∀ n : ℕ, normalized.M n ≅ coefCompactSupportLevel l E c K n
  complexes : ∀ n : ℕ, CochainComplex (normalizedDVRModules l E Y n) ℤ
  identifications : ∀ n : ℕ,
    DerivedCategory.Q.obj (complexes n) ≅ coefCompactSupportLevel l E c K n
  chainMaps : ∀ {m n : ℕ} (h : n ≤ m), complexes m ⟶
    ((normalizedDVRModuleRes l E Y h).mapHomologicalComplex (.up ℤ)).obj (complexes n)
  strict : CochainComplex (ℕᵒᵖ ⥤ completedIntegralModuleSheaves l E Y D hl) ℤ
  strictIso : DerivedCategory.Q.obj strict ≅ normalized.tower
  strictEvaluations : ∀ n : ℕ,
    (((evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E Y D hl)).obj (op n)).mapHomologicalComplex
        (.up ℤ)).obj strict ≅
      ((completedIntegralRestrictScalars l E Y D hl n).mapHomologicalComplex
        (.up ℤ)).obj (complexes n)

/-- The exact normalization, chain composition, and evaluation compatibility equations
for a compact-support realization. Separating these proof fields from its data avoids
expanding the large derived-localization categories in a dependent structure recursor.
Source: blueprint proof paragraph 2; Stacks Tags 05RT and 07A6
(blueprint: lem-coef-compact-support-normalized-realization). -/
def CoefCompactSupportRealizationSpec
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X))
    (R : CoefCompactSupportRealization l E D hl c K) : Prop :=
  (∀ {m n : ℕ} (h : n ≤ m),
      R.normalized.tau h ≫ (normalizedDVRRes l E Y h).map (R.levels n).hom =
        (R.levels m).hom ≫ coefCompactSupportNormalizedTau l E c K h) ∧
  (∀ {m n : ℕ} (h : n ≤ m),
      DerivedCategory.Q.map (R.chainMaps h) ≫
          (normalizedDVRModuleRes l E Y h).mapDerivedCategoryFactors.inv.app (R.complexes n) ≫
          (normalizedDVRRes l E Y h).map (R.identifications n).hom =
        (R.identifications m).hom ≫ coefCompactSupportNormalizedTau l E c K h) ∧
  (∀ {m n : ℕ} (h : n ≤ m),
      ((NatTrans.mapHomologicalComplex
          ((evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E Y D hl)).map (homOfLE h).op)
          (.up ℤ)).app R.strict) ≫ (R.strictEvaluations n).hom =
        (R.strictEvaluations m).hom ≫
          ((completedIntegralRestrictScalars l E Y D hl m).mapHomologicalComplex (.up ℤ)).map
            (R.chainMaps h) ≫
          (Functor.mapHomologicalComplexCompIso
            (coefCompactSupportCompletedModuleComp l E Y D hl h) (.up ℤ)).hom.app (R.complexes n))


attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

set_option maxHeartbeats 600000 in
-- Compare exact derived functors without unfolding their localization constructions.
/-- The actual compact-support quotient tower is normalized and has a coherent
realization retaining its finite coefficient chain complexes and prescribed transitions.
Source: blueprint main-20261015, lem-coef-integral-compact-support, proof paragraph 2;
Stacks Tags 06YS, 0D6D, 07A6 and 05RT
(blueprint: lem-coef-compact-support-normalized-realization).

Proof:
1. Use the quotient-cocycle theorem to identify the canonical reduction adjoints and
prove that beta is invertible. Integral constructibility gives bounded constructibility
of every finite reduction.
2. Apply the finite reduction-adjoint theorem to beta. The quotient-unit identity and
injectivity of the scalar adjunction identify the actual compact-support adjoint with
the specified tensor comparison followed by F_n(beta); both arrows are invertible.
3. Form the native derived coefficient system by reducing K on the ringed sequence
site and applying the fixed compactification there. Evaluation and transition
comparisons identify its finite objects and maps with the specified compact-support
objects and quotient maps. The native finite-action theorem gives normalization.
4. Choose one complex representing this derived coefficient system. Exact evaluation
produces all the finite coefficient complexes and chain maps. The localization
factorization identifies their maps with the specified transitions. Exact restriction
to the completed coefficient sheaf produces the strict complex of towers, and the
ordinary restriction comparison proves its transition equation in each degree.
At adjacent levels the formula is precisely sfCompactSupportTransition, the transition
in def-weil-integral-rational-qbar-compact-support. -/
theorem compactSupport_normalized_realization
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X))
    (_hK : sfIntegralConstructible l E X K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hTor : ∀ n : ℕ, HasProEtaleTorAmplitude X
      (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E X n).obj K) a b) :
    (∃ R : CoefCompactSupportRealization l E D hl c K,
      CoefCompactSupportRealizationSpec l E D hl c K R) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        IsIso (coefCompactSupportBeta l E X h K) ∧
        IsIso (coefCompactSupportTensor l E c K h) ∧
        IsIso ((sfIntrinsicCompactSupport c
          (Padic.coefficientExtensionRing l E (n + 1))).map
          (coefCompactSupportBeta l E X h K)) ∧
        coefCompactSupportAdjoint l E c K h =
          coefCompactSupportTensor l E c K h ≫
            (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
              (coefCompactSupportBeta l E X h K)) := by
  classical
  have hlk : IsUnit (l : D.k) := by
    let : Fintype D.k₀ := Fintype.ofFinite _
    have : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
    have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    exact isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime _ (Fact.out : l.Prime) hl.symm)
  have hquot := compactSupport_quotient_cocycle l E D.k hlk c K
  have hfinite (n : ℕ) := (_hK.2.choose_spec.choose_spec.2 n).1
  have hadj (m n : ℕ) (h : n ≤ m) :
      IsIso (coefCompactSupportBeta l E X h K) ∧
      IsIso (coefCompactSupportTensor l E c K h) ∧
      IsIso ((sfIntrinsicCompactSupport c
        (Padic.coefficientExtensionRing l E (n + 1))).map
        (coefCompactSupportBeta l E X h K)) ∧
      coefCompactSupportAdjoint l E c K h =
        coefCompactSupportTensor l E c K h ≫
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
            (coefCompactSupportBeta l E X h K) := by
    have hb : IsIso (coefCompactSupportBeta l E X h K) := (hquot.1 m n h).1
    have H := coefCompactSupportReductionAdjoint l E D.k hlk m n h f c
      ((scalarReductionDerivedExtension l E X m).obj K)
      ((scalarReductionDerivedExtension l E X n).obj K)
      (hfinite m) (hfinite n) (asIso (coefCompactSupportBeta l E X h K))
    refine ⟨hb, H.2.1, H.2.2, ?_⟩
    apply ((pbcDerivedScalarAdjunction
      (compactSupportLevelSheafQuotient l E Y m n h)).homEquiv _ _).injective
    dsimp only [coefCompactSupportAdjoint]
    rw [Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_unit]
    exact (congrArg (fun ρ ↦
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map ρ ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((scalarReductionDerivedExtension l E X n).obj K))
      (hquot.1 m n h).2).trans H.1.symm
  refine ⟨?_, hadj⟩
  obtain ⟨S, _hS⟩ := coefficientDerivedSystemEvaluationCalculus.{u, u} l E X
  let N : coefficientSequenceDerived.{u, u} l E Y :=
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g).obj (S.reduction.obj K)
  let e (n : ℕ) : (coefficientSequenceDerivedEvaluation l E Y n).obj N ≅
      coefCompactSupportLevel l E c K n :=
    (compactSupportSystemEvaluation l E c n).app (S.reduction.obj K) ≪≫
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).mapIso
        ((S.reductionEvaluation n).app K)
  have he {m n : ℕ} (h : n ≤ m) :
      (coefficientSequenceDerivedTransition l E Y h).app N ≫
        (normalizedDVRRes l E Y h).map (e n).hom =
      (e m).hom ≫ coefCompactSupportNormalizedTau l E c K h := by
    have hg := compactSupportNativeSystemTransition l E c h (S.reduction.obj K)
    have hd := compactSupportReductionTransition l E X S.toCoefficientDerivedSystemReduction h K
    have H := compactSupportFiniteSquare
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)))
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
      (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E X m n h))
      (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E Y m n h))
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom
      _ _ _ _ _ _ _ hg hd
    have H' : (compactSupportCoefficientTransition l E Y h).app N ≫
        (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E Y m n h)).map
          (e n).hom = (e m).hom ≫ coefCompactSupportTau l E c K h := by
      simpa only [N, coefCompactSupportTau, coefficientFiniteDerivedExtension, e,
        Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
        Category.assoc] using H
    apply (cancel_mono ((coefCompactSupportRestrictionIso l E Y h).hom.app
      (coefCompactSupportLevel l E c K n))).mp
    rw [Category.assoc, (coefCompactSupportRestrictionIso l E Y h).hom.naturality]
    rw [← Category.assoc]
    have hτ := NatTrans.congr_app (derivedTransition_direct l E Y h) N
    change (coefficientSequenceDerivedTransition l E Y h).app N ≫
      (coefCompactSupportRestrictionIso l E Y h).hom.app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N) = _ at hτ
    rw [hτ]
    simp only [coefCompactSupportNormalizedTau, Category.assoc,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact H'
  let T : NormalizedDVRTower l E Y D hl := {
    M := fun n ↦ (coefficientSequenceDerivedEvaluation l E Y n).obj N
    tau := fun h ↦ (coefficientSequenceDerivedTransition l E Y h).app N
    tau_refl := derivedTransition_id l E Y N
    tau_comp := fun h₁ h₂ ↦ derivedTransition_comp l E Y N h₁ h₂
    tower := (coefficientSequenceDerivedRestriction l E Y).obj N
    evaluationIso := fun n ↦ (coefficientRestrictedEvaluationIso l E Y n).app N
    tower_tau := fun h ↦ derivedRestrictedTransition l E Y D hl N h
    normalization := compactSupportSystem_normalized l c D.k hlk E ⟨K, _hK⟩ S }
  obtain ⟨P, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q N
  let C (n : ℕ) :=
    ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P
  let j (n : ℕ) : DerivedCategory.Q.obj (C n) ≅ coefCompactSupportLevel l E c K n :=
    ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.app P).symm ≪≫
      (coefficientSequenceDerivedEvaluation l E Y n).mapIso i ≪≫ e n
  let t {m n : ℕ} (h : n ≤ m) : C m ⟶
      ((normalizedDVRModuleRes l E Y h).mapHomologicalComplex (.up ℤ)).obj (C n) :=
    (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E Y h) (.up ℤ)).app P
  let U := coefficientSequenceRestriction l E Y
  let Q := (U.mapHomologicalComplex (.up ℤ)).obj P
  let q : DerivedCategory.Q.obj Q ≅ T.tower :=
    (U.mapDerivedCategoryFactors.app P).symm ≪≫
      (coefficientSequenceDerivedRestriction l E Y).mapIso i
  let v (n : ℕ) :
      (((evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E Y D hl)).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((completedIntegralRestrictScalars l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj
        (C n) :=
    (NatIso.mapHomologicalComplex
      (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)) (.up ℤ)).app P
  let R : CoefCompactSupportRealization l E D hl c K := {
    normalized := T
    levels := e
    complexes := C
    identifications := j
    chainMaps := fun h ↦ t h
    strict := Q
    strictIso := q
    strictEvaluations := v }
  refine ⟨R, he, ?_, ?_⟩
  · intro m n h
    have hf := CategoryTheory.derivedTransition_fac
      (coefficientSequenceEvaluation l E Y m) (coefficientSequenceEvaluation l E Y n)
      (normalizedDVRModuleRes l E Y h) (coefficientSequenceTransition l E Y h) P
    rw [← derivedTransition_eq] at hf
    have hf' : DerivedCategory.Q.map (t h) ≫
        (normalizedDVRModuleRes l E Y h).mapDerivedCategoryFactors.inv.app (C n) ≫
        (normalizedDVRRes l E Y h).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.inv.app P) =
      (coefficientSequenceEvaluation l E Y m).mapDerivedCategoryFactors.inv.app P ≫
        (coefficientSequenceDerivedTransition l E Y h).app (DerivedCategory.Q.obj P) := by
      apply (cancel_epi
        ((coefficientSequenceEvaluation l E Y m).mapDerivedCategoryFactors.hom.app P)).mp
      dsimp only [t]
      rw [← reassoc_of% hf]
      simp only [C, Iso.hom_inv_id_app_assoc]
      change (coefficientSequenceDerivedTransition l E Y h).app (DerivedCategory.Q.obj P) ≫
        (normalizedDVRRes l E Y h).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app P) ≫
        (normalizedDVRRes l E Y h).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.inv.app P) = _
      rw [← Functor.map_comp, Iso.hom_inv_id_app]
      erw [(normalizedDVRRes l E Y h).map_id, Category.comp_id]
    change DerivedCategory.Q.map (t h) ≫
      (normalizedDVRModuleRes l E Y h).mapDerivedCategoryFactors.inv.app (C n) ≫
      (normalizedDVRRes l E Y h).map (j n).hom =
        (j m).hom ≫ coefCompactSupportNormalizedTau l E c K h
    dsimp only [j, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% hf']
    have hn := (coefficientSequenceDerivedTransition l E Y h).naturality i.hom
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn, he]
    rfl
  · intro m n h
    change (NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E Y D hl)).map (homOfLE h).op)
      (.up ℤ)).app Q ≫ (v n).hom = (v m).hom ≫
        ((completedIntegralRestrictScalars l E Y D hl m).mapHomologicalComplex (.up ℤ)).map
          (t h) ≫ (Functor.mapHomologicalComplexCompIso
            (coefCompactSupportCompletedModuleComp l E Y D hl h) (.up ℤ)).hom.app (C n)
    have hc : coefCompactSupportCompletedModuleComp l E Y D hl h =
        completedCompO l E Y D hl h := by
      unfold coefCompactSupportCompletedModuleComp completedCompO restrictCompIso
      rfl
    rw [hc]
    apply HomologicalComplex.hom_ext
    intro k
    simp only [Q, U, v, C, t, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, NatIso.mapHomologicalComplex,
      Iso.app_hom, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplex_map_f]
    exact restrictedTransition l E Y D hl (P.X k) h

end WeilConjectures
