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
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.Paper.FiniteCompactSupportScalarComparison
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

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
  sorry

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
  sorry

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
  sorry

/-- The first arrow in the specified tensor comparison factorization.
Source: blueprint proof paragraph 2; Stacks Tags 07A6 and 0GL6
(blueprint: lem-coef-compact-support-normalized-realization). -/
def coefCompactSupportTensor {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) {m n : ℕ} (h : n ≤ m) :=
  AlgebraicGeometry.ProEtale.intrinsicCompactSupportCoefficientComparison
    (compactSupportLevelQuotient l E m n h) c
    ((scalarReductionDerivedExtension l E X m).obj K)

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

/-- The actual compact-support quotient tower is normalized and has a coherent
realization retaining its finite coefficient chain complexes and prescribed transitions.
Source: blueprint main-20261015, lem-coef-integral-compact-support, proof paragraph 2;
Stacks Tags 06YS, 0D6D, 07A6 and 05RT
(blueprint: lem-coef-compact-support-normalized-realization).

Proof:
1. Resolve K by a flat-term K-flat complex P (lem-pc-kflat-resolution).
Derived change of rings computes every reduction on P. The successive quotient
normalization sends (x tensor u) tensor v to x tensor q(u)v. Its adjoint is the
quotient-induced rho, independent of P, with identity and quotient cocycle
(lem-pur-derived-change-of-rings, lem-sfb-successive-derived-quotient-normalization,
lem-pur-sheaf-ring-derived-coefficient-adjunction).
2. Apply the fixed compactification to rho and then the specified scalar restriction
comparison. Naturality and its composition identity give the output identity and cocycle
(lem-sf-compact-support-restriction-of-scalars).
3. The defining scalar-unit equation for the compact-support tensor comparison shows
that its composite with F_n(beta) has adjunct exactly tau. Injectivity of the derived
adjunction identifies these arrows (def-coef-compact-support-tensor-comparison).
4. The reductions are bounded constructible. Their iterated ordinary reduction is the
next bounded constructible reduction. The canonical finite compact-support scalar
comparison is therefore invertible, as is F_n(beta)
(lem-finite-compact-support-scalar-comparison). The hypotheses l != p, finite type
and separatedness are precisely those required; the common Tor interval supplies
finite-Tor input. No quotient is assumed flat.
5. Choose C_1 representing M_1. Inductively represent the next transition by a roof
D <- C_(n+1) -> Res C_n whose left map is a quasi-isomorphism. Localizing the left
map identifies C_(n+1) with M_(n+1). This never changes an earlier C_n. Quotient
cocycles identify every composite with the specified tau
(lem-pc-quasi-isomorphisms-multiplicative-system, Stacks Tag 05RT).
6. Restrict the complexes and maps to the completed coefficient sheaf. Projection
compatibility makes this a strict inverse sequence. In each cochain degree take
that tower; the differentials commute with transitions and square to zero levelwise.
Localizing this complex of towers gives the coherent derived object; its evaluations
and transitions are those of the chosen complexes and maps, by construction
(def-weil-pbc-adic-coefficient-datum, def-coef-normalized-dvr-tower).
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
  sorry

end WeilConjectures
