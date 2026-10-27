module

public import Sheaf.Paper.CompactSupportQuotientCocycleData
import Sheaf.Paper.CompactSupportQuotientCocycleRepresentativesData
import Sheaf.Paper.CompactSupportQuotientComputationSquares
import Sheaf.Paper.CompactSupportQuotientInputLaws
import Sheaf.Paper.CompactSupportQuotientAdjunct
import Sheaf.Paper.CompactSupportQuotientRawInput
import Sheaf.Paper.CompactSupportQuotientRawOutputIdentity
import Sheaf.Paper.CompactSupportQuotientRawOutputComposition

/-! # Unit and cocycle for compact-support coefficient quotients

Source: the current blueprint, lem-coef-integral-compact-support.proof.md,
finite-level coefficient comparison; Stacks Tags 03EK, 06YS, 06YY and 07A6
(blueprint: lem-coef-compact-support-quotient-cocycle).

Index n denotes exponent n+1, so every positive coefficient exponent is included.
All reduction maps are the published normalized adjuncts of the actual quotient maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Keep distinct quotient levels from unfolding their valuation-theoretic ideal data.
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Quotient and balancing formulas on EVERY flat-term K-flat representative.
The two commuting squares use the universal computation maps. Thus they identify the
specified arrows independently of the representative, not only up to some isomorphism.
The scalar-first convention writes (x tensor s) tensor t as t tensor (s tensor x).
Source: blueprint proof paragraph 2; Stacks Tags 03EK, 06YS, 06YY and 07A6
(blueprint: lem-coef-compact-support-quotient-cocycle).
Proof: the universal derived counit is invertible on the given K-flat complex.
The ordinary normalized adjunctions give a natural quotient transformation and the
canonical balancing isomorphism of composed left adjoints. Naturality makes their
components chain maps, their unit equations give the two section formulas, and
componentwise invertibility makes the balancing chain map invertible. Use the actual
ordinary-extension terms and identity isomorphisms for the HEq witnesses. Apply the
universal comparison-square theorem to these constructed maps, and pair the resulting
squares with the computation-map isomorphisms. -/
theorem compactSupportQuotient_representatives (W : Scheme.{u})
    (m n : ℕ) (h : n ≤ m)
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (_hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      W.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} W.ProEt) (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) P)
    (_hf : ∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      W.ProEt inferInstance (ProEt.topology W) inferInstance
      (integralCoefficientAbLocallyBijective.{u, u} W)
      (@HasSheafify.isRightAdjoint _ _ _ _ _ (integralCoefficientAbSheafify.{u, u} W))
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (P.X i)) :
    IsIso (compactSupportQuotientComputation l E W m P) ∧
    IsIso (compactSupportQuotientComputation l E W n P) ∧
    ∃ (a : (compactSupportQuotientComplex l E W m).obj P ⟶
        ((proEtaleCoefficientRestrictScalars W
          (compactSupportLevelQuotient l E m n h)).mapHomologicalComplex (.up ℤ)).obj
            ((compactSupportQuotientComplex l E W n).obj P))
      (b : ((pbcExtend.{u} (compactSupportLevelSheafQuotient l E W m n h)).mapHomologicalComplex
          (.up ℤ)).obj ((compactSupportQuotientComplex l E W m).obj P) ⟶
        (compactSupportQuotientComplex l E W n).obj P),
      (∀ i : ℤ, ∃
        (Mm : scalarReductionTarget.{u, u} l E W m)
        (Mn : scalarReductionTarget.{u, u} l E W n)
        (em : (scalarReductionExtension.{u, u} l E W m).obj (P.X i) ≅ Mm)
        (en : (scalarReductionExtension.{u, u} l E W n).obj (P.X i) ≅ Mn)
        (a₀ : Mm ⟶ (proEtaleCoefficientRestrictScalars W
          (compactSupportLevelQuotient l E m n h)).obj Mn)
        (b₀ : (pbcExtend (compactSupportLevelSheafQuotient l E W m n h)).obj Mm ⟶ Mn),
        HEq em.hom (𝟙 ((scalarReductionExtension.{u, u} l E W m).obj (P.X i))) ∧
        HEq en.hom (𝟙 ((scalarReductionExtension.{u, u} l E W n).obj (P.X i))) ∧
        HEq (a.f i) a₀ ∧ HEq (b.f i) b₀ ∧
          CompactSupportQuotientModuleSpec l E W m n h (P.X i) Mm Mn em en a₀ b₀) ∧
      IsIso b ∧
      (compactSupportReductionMap l E W m n h (DerivedCategory.Q.obj P) ≫
          (proEtaleCoefficientRestrictScalars W
            (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
              (compactSupportQuotientComputation l E W n P) ≫
          (proEtaleCoefficientRestrictScalars W
            (compactSupportLevelQuotient l E m n h)).mapDerivedCategoryFactors.hom.app
              ((compactSupportQuotientComplex l E W n).obj P) =
        compactSupportQuotientComputation l E W m P ≫ DerivedCategory.Q.map a) ∧
      ((((pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E W m n h)).homEquiv
        _ _).symm (compactSupportReductionMap l E W m n h (DerivedCategory.Q.obj P))) ≫
          compactSupportQuotientComputation l E W n P =
        (pbcDerivedExtend (compactSupportLevelSheafQuotient l E W m n h)).map
            (compactSupportQuotientComputation l E W m P) ≫
          pbcComplexCounit.{u} (compactSupportLevelSheafQuotient l E W m n h)
            ((compactSupportQuotientComplex l E W m).obj P) ≫ DerivedCategory.Q.map b) := by
  have hcomp (j : ℕ) : IsIso (compactSupportQuotientComputation l E W j P) := by
    let := scalarReductionExtensionAdditive.{u, u} l E W j
    have : IsIso ((scalarReductionCounit.{u, u} l E W j).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
      (scalarReductionDerivedExistence.{u, u} l E W j).choose_spec.choose_spec.2.2 P _hP
    unfold compactSupportQuotientComputation
    infer_instance
  rcases compactSupportQuotient_chain_maps l E W m n h P with ⟨a, b, hdata, hb⟩
  obtain ⟨hsq, hmate⟩ :=
    compactSupportQuotient_computation_squares l E W m n h P _hP _hf a b hdata
  exact ⟨hcomp m, hcomp n, a, b, hdata, hb, hsq, hmate⟩

/-- The specified quotient arrows and their compact-support images satisfy unit and
composition on arbitrary unbounded objects. No constructibility or Tor bound is assumed.
Source: blueprint proof paragraph 2; Stacks Tags 03EK, 06YY and 07A6
(blueprint: lem-coef-compact-support-quotient-cocycle).
Proof: the twice-transposed final unit is the component of the canonical
left-adjoint composition isomorphism, so the quotient adjunct is invertible. The
inverse Hom-equivalence identity gives its displayed unit equation. Apply the input
quotient identity and composition laws. The normalized identity coefficient square
transports the input identity to compact support. For composition, map the invertible
prime in the base field to each stalk, specialize the coefficient composition square
to the two quotient maps with their direct-quotient equality cast, and use naturality
to move the middle quotient arrow across the comparison. Combine the compact-support
maps by functoriality and use the input cocycle. The canonical coefficient presentation
aliases have exactly the existing maps as values, so these are the stated arrows. -/
theorem compactSupport_quotient_cocycle
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (∀ (m n : ℕ) (h : n ≤ m),
      IsIso ((((pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E X m n h)).homEquiv
        _ _).symm (compactSupportReductionMap l E X m n h K))) ∧
      compactSupportReductionMap l E X m n h K =
        (pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E X m n h)).unit.app
            ((scalarReductionDerivedExtension.{u, u} l E X m).obj K) ≫
          (proEtaleCoefficientRestrictScalars X
            (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
              ((((pbcDerivedScalarAdjunction
        (compactSupportLevelSheafQuotient l E X m n h)).homEquiv
        _ _).symm (compactSupportReductionMap l E X m n h K)))) ∧
    (∀ n : ℕ, compactSupportReductionMap l E X n n le_rfl K ≫
      (compactSupportQuotientResId l E X n).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      compactSupportReductionMap l E X r m hrm K ≫
          (proEtaleCoefficientRestrictScalars X
            (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory.map
              (compactSupportReductionMap l E X m n hmn K) ≫
          (compactSupportQuotientResComp l E X r m n hrm hmn).hom.app
            ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) =
        compactSupportReductionMap l E X r n (hmn.trans hrm) K) ∧
    (∀ n : ℕ, ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
        (compactSupportReductionMap l E X n n le_rfl K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E n n le_rfl)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) ≫
      (compactSupportQuotientResId l E Y n).hom.app
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (r + 1))).map
        (compactSupportReductionMap l E X r m hrm K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E r m hrm)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X m).obj K)) ≫
          (proEtaleCoefficientRestrictScalars Y
            (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory.map
              (((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
        (compactSupportReductionMap l E X m n hmn K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n hmn)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))) ≫
          (compactSupportQuotientResComp l E Y r m n hrm hmn).hom.app
            ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
              ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) =
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (r + 1))).map
        (compactSupportReductionMap l E X r n (hmn.trans hrm) K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E r n (hmn.trans hrm))).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))) := by
  let hi := compactSupportQuotient_input_laws l E X K
  have hraw := compactSupportQuotient_raw_input l E X K hi
  exact ⟨compactSupportQuotient_adjunct l E X K, hraw.1, hraw.2,
    compactSupportQuotient_raw_output_identity l E c K hi.1,
    compactSupportQuotient_raw_output_composition l E k _hl c K hi⟩

end WeilConjectures
