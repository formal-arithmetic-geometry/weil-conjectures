module

public import Sheaf.Paper.CompactSupportScalarLimitFoundations
public import Sheaf.Paper.ScalarRoosComparisonUnique

public import Sheaf.Paper.CompactSupportStrictScalarMate
public import Sheaf.Paper.CompactSupportNormalizedRealization
public import Sheaf.Paper.NormalizedDVREffectivity
public import Sheaf.CategoryTheory.CompactSupportRoosCofinality
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Sheaf.Paper.CompactSupportScalarRoosTensorNormalization
import Sheaf.Paper.CompactSupportScalarRoosNormalization
import Sheaf.Paper.CompactSupportNativeRealization
import Sheaf.Paper.CompactSupportNativeEffectivity
import Sheaf.Paper.CompactSupportScalarLimitCompletedComparison
import all Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import all Sheaf.CategoryTheory.RoosTensorNormalization
import Sheaf.Paper.CompactSupportCoefficientModels
import all Sheaf.CategoryTheory.ConstantFiniteFreeSectionBasis
import all Sheaf.Paper.CompletedIntegralFiniteFree

/-! # Normalized compact-support scalar limits and their finite reductions

Source: Stacks Tags 0941, 07A6 and 0GL6; auxiliary comparison Steps 5--6
(blueprint: lem-pur-compact-support-scalar-limit-reduction).

The helpers specify the total limit and its projections, the tensor and cofinal
maps, completed/constant coefficient transports, and projection-adjoint reductions.
The main theorem is `compactSupportScalarLimitReduction`; strict augmentation
preservation is `scalarLimitArrow_augmentation`.

All limits below are total right derived limits of strict towers. Natural-number
index `n` denotes positive exponent `n+1`, including in arithmetic subsequences.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme hiding Modules
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

attribute [local irreducible] constantMap completedCoefficientMap

attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] scalarCompletion

/-- The unit-normalized Roos presentation of the actual total right-derived limit.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarRoosComparison (W : Scheme.{u}) :=
  (scalarRoosComparison_existsUnique l E W).choose

private theorem scalarRoosComparison_unit (W : Scheme.{u})
    (K : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ) :
    DerivedCategory.Q.map (roosι K) ≫ (scalarRoosComparison l E W).hom.app K =
      DerivedCategory.Q.map
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval K.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval K.asFunctor⟩).hom ≫
        Functor.rightDerivedFunctorUnitQ
          (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤
            Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) K :=
  (scalarRoosComparison_existsUnique l E W).choose_spec.1 K

attribute [local irreducible] scalarRoosComparison roosAdditiveComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The cofinal factor and every strict augmentation are the recorded chain maps.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: the selection/block coordinate equation of compactSupportRoosCofinality
commutes with the kernel inclusion. The universal derived unit identifies it with
scalarLimitRestriction. The inclusion of any compatible cone has coordinates
(0,γ), so the same equation proves the augmentation identity. -/
theorem scalarRoosNormalization (W : Scheme.{u})
    (K : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
    (e : ℕ) (he : 1 ≤ e) :
    QuasiIso (scalarRoosRestriction l E W K e he) ∧
      (∀ p : ℤ,
        (scalarRoosRestriction l E W K e he).f (p + 1) ≫
            (strictRoosCoordinates ((CategoryTheory.StrictTowerArithmetic.complexRestriction
              (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) e).obj K)
                p).hom =
          (strictRoosCoordinates K p).hom ≫
            biprod.map ((CategoryTheory.StrictTowerArithmetic.block e K.asFunctor).f p)
              ((CategoryTheory.StrictTowerArithmetic.selection e K.asFunctor).f (p + 1))) ∧
      (DerivedCategory.Q.map (scalarRoosRestriction l E W K e he) ≫
          (scalarRoosComparison l E W).hom.app
            ((CategoryTheory.StrictTowerArithmetic.complexRestriction
              (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) e).obj K) ≫
          (scalarLimit l E W).map
            ((ordinarySubsequence l E W e).mapDerivedCategoryFactors.inv.app K) =
        (scalarRoosComparison l E W).hom.app K ≫
          (scalarLimitRestriction l E W e).app (DerivedCategory.Q.obj K)) ∧
      (∀ (P : CochainComplex
          (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
        (a : ∀ n : ℕ, P ⟶ K.asFunctor.obj (op n))
        (ha : ∀ n : ℕ, a (n + 1) ≫
          K.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n),
        ∃ h : ∀ n : ℕ, a (e * (n + 2) - 1) ≫
            K.asFunctor.map
              ((CategoryTheory.StrictTowerArithmetic.index e).map
                (homOfLE (Nat.le_succ n)).op) = a (e * (n + 1) - 1),
          roosAugment a ha ≫ scalarRoosRestriction l E W K e he =
            roosAugment (fun n : ℕ ↦ a (e * (n + 1) - 1)) h) := by
  exact scalarRoosNormalization_of_unit l E W (scalarRoosComparison l E W)
    (scalarRoosComparison_unit l E W) K e he


/-- The specified strict augmentation followed by the fixed Roos/limit comparison.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitAugmentation (W : Scheme.{u})
    (K : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
    (P : CochainComplex
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
    (a : ∀ n : ℕ, P ⟶ K.asFunctor.obj (op n))
    (ha : ∀ n : ℕ, a (n + 1) ≫
      K.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n) :=
  DerivedCategory.Q.map (roosAugment a ha) ≫ (scalarRoosComparison l E W).hom.app K

/-- The middle factor R(q) carries each strict augmentation to its composite with q.
Together with scalarRoosNormalization and scalarRoosTensorNormalization this is
augmentation preservation for the three factors defining scalarLimitArrow.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: the coordinate formula for roosF.map sends (0,a) to (0,a composed with q).
Coordinate extensionality gives the strict equation; naturality of the one fixed
Roos comparison gives exactly the displayed derived equation, including for roofs. -/
theorem scalarLimitMapAugmentation (W : Scheme.{u})
    (K L : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ) (q : K ⟶ L)
    (P : CochainComplex
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
    (a : ∀ n : ℕ, P ⟶ K.asFunctor.obj (op n))
    (ha : ∀ n : ℕ, a (n + 1) ≫
      K.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n) :
    ∃ h : ∀ n : ℕ,
        (a (n + 1) ≫ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app
          (op (n + 1))) ≫ L.asFunctor.map (homOfLE (Nat.le_succ n)).op =
            a n ≫ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n),
      scalarLimitAugmentation l E W K P a ha ≫
          (scalarLimit l E W).map (DerivedCategory.Q.map q) =
        scalarLimitAugmentation l E W L P
          (fun n : ℕ ↦ a n ≫
            (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) h := by
  let q' := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q
  have hb (n : ℕ) :
      (a (n + 1) ≫ q'.app (op (n + 1))) ≫
          L.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n ≫ q'.app (op n) := by
    calc
      _ = a (n + 1) ≫ (q'.app (op (n + 1)) ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj L).map
            (homOfLE (Nat.le_succ n)).op) := Category.assoc _ _ _
      _ = a (n + 1) ≫
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj K).map
            (homOfLE (Nat.le_succ n)).op ≫ q'.app (op n)) :=
        congrArg (fun z ↦ a (n + 1) ≫ z) (q'.naturality _).symm
      _ = (a (n + 1) ≫ K.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫
          q'.app (op n) := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun z ↦ z ≫ q'.app (op n)) (ha n)
  refine ⟨hb, ?_⟩
  have haug : roosAugment a ha ≫ roosF.map q =
      roosAugment (fun n ↦ a n ≫ q'.app (op n)) hb := by
    apply HomologicalComplex.Hom.ext
    funext k
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
    apply (cancel_mono (roosχ L p).hom).1
    simp only [HomologicalComplex.comp_f, Category.assoc, roosF_map_χ,
      roosAugment_χ]
    rw [← Category.assoc, roosAugment_χ]
    apply biprod.hom_ext
    · simp
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd,
        biprod.lift_snd_assoc]
      rw [← HomologicalComplex.comp_f]
      congr 1
      apply Pi.hom_ext
      intro n
      simp [roosPmap, q']
  have hn := (scalarRoosComparison l E W).hom.naturality q
  dsimp only [Functor.comp_map] at hn
  simp only [scalarLimitAugmentation]
  rw [Category.assoc, ← hn, ← Category.assoc, ← DerivedCategory.Q.map_comp, haug]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarTensor_preservesLimits (W : Scheme.{u})
    (J₀ : Type*) [Category J₀]
    [HasLimitsOfShape J₀
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W)]
    [HasLimitsOfShape J₀
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W)] :
    PreservesLimitsOfShape J₀ (pbcExtend (constantMap l E F i W)) := by
  classical
  let := i.toAlgebra
  let := (integralScalarIntegerInclusion l E F i).toAlgebra
  obtain ⟨b⟩ := WeilConjectures.integral_basis l E F i
  let : Algebra (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (Padic.coefficientExtensionIntegers l F) :=
    ULift.algebra' (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l F)
  let A : CommRingCat.{u + 1} :=
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
  let B : CommRingCat.{u + 1} :=
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F))
  let J := ProEt.topology W
  let e := @CategoryTheory.basisSheafIso.{u + 1, u, u + 1} W.ProEt inferInstance J
    (integralCoefficientRingSheafify.{u, u} W)
    (inferInstance : J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    (integralCoefficientAbSheafify.{u, u} W)
    (integralCoefficientAbLocallyBijective.{u, u} W)
    A B inferInstance (Module.finrank E F) (WeilConjectures.liftedBasis.{u, u} b)
  have : (pbcRestrict (constantMap l E F i W)).ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties (constantMap l E F i W)).2.2
  have : PreservesLimitsOfShape J₀
      (pbcExtend (constantMap l E F i W) ⋙ pbcRestrict (constantMap l E F i W)) :=
    preservesLimitsOfShape_of_natIso
      (ordinaryCoordinates W (constantMap l E F i W) (Module.finrank E F)
        (by unfold constantMap; exact e.symm)).symm
  have : (pbcRestrict (constantMap l E F i W)).IsRightAdjoint :=
    (pbcScalarAdjunction (constantMap l E F i W)).isRightAdjoint
  have : ReflectsLimitsOfShape J₀ (pbcRestrict (constantMap l E F i W)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (pbcRestrict (constantMap l E F i W))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual complex tensor/product comparison is invertible by finite freeness.
Source: Stacks 03EK, 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: choose a finite integral basis. Tensor, products and their canonical
comparison become a finite biproduct and the coordinate interchange; the inverse
interchange is compatible with the differentials and all tower maps. -/
theorem scalarRoosTensorProducts (W : Scheme.{u})
    (K : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ) :
    IsIso (piComparison ((pbcExtend (constantMap l E F i W)).mapHomologicalComplex
      (.up ℤ)) (fun n : ℕ ↦ K.asFunctor.obj (op n))) := by
  have := scalarTensor_preservesLimits l E F i W (Discrete ℕ)
  infer_instance

/-- The recorded product/cone tensor map. Its two coordinates are the product
comparison, so the chosen witness is determined as an actual chain map.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarRoosTensor (W : Scheme.{u})
    (K : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ) :=
  (strictRoosAdditiveComparison (pbcExtend (constantMap l E F i W))
    (scalarRoosTensorProducts l E F i W)).choose K

attribute [local irreducible] scalarRoosTensor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived tau is the canonical coordinate tensor map, with the universal
Roos normalization. It carries a strict augmentation to its termwise tensor.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: the two product comparisons send x tensor b to the sequence x_n tensor b.
Apply the coordinate equation of strictRoosAdditiveComparison. It commutes with
the kernel inclusion and thus, by the derived-unit universal property, with tau.
On (0,a), its shifted-product coordinate stays zero; the remaining coordinate
is the tensor of a. Coordinate extensionality gives the second equation. -/
theorem scalarRoosTensorNormalization (W : Scheme.{u})
    (K : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ) :
    (baseTensor l E F i W).map ((scalarRoosComparison l E W).hom.app K) ≫
        (scalarLimitTensor l E F i W).hom.app (DerivedCategory.Q.obj K) =
      baseTensorCounit l E F i W (roosF.obj K) ≫
        DerivedCategory.Q.map (scalarRoosTensor l E F i W K).hom ≫
        (scalarRoosComparison l F W).hom.app
          (((tensor l E F i W).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (scalarLimit l F W).map
          ((tensor l E F i W).mapDerivedCategoryFactors.inv.app K) ∧
    (∀ (P : CochainComplex
        (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
      (a : ∀ n : ℕ, P ⟶ K.asFunctor.obj (op n))
      (ha : ∀ n : ℕ, a (n + 1) ≫
        K.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n),
      ∃ h : ∀ n : ℕ,
        ((pbcExtend (constantMap l E F i W)).mapHomologicalComplex (.up ℤ)).map
            (a (n + 1)) ≫
          (((tensor l E F i W).mapHomologicalComplex (.up ℤ)).obj K).asFunctor.map
            (homOfLE (Nat.le_succ n)).op =
          ((pbcExtend (constantMap l E F i W)).mapHomologicalComplex (.up ℤ)).map (a n),
        ((pbcExtend (constantMap l E F i W)).mapHomologicalComplex (.up ℤ)).map
            (roosAugment a ha) ≫ (scalarRoosTensor l E F i W K).hom =
          roosAugment (fun n : ℕ ↦
            ((pbcExtend (constantMap l E F i W)).mapHomologicalComplex (.up ℤ)).map (a n)) h) := by
  let G := pbcExtend (constantMap l E F i W)
  have hθ : (scalarRoosTensor l E F i W K).hom = roosAdditiveComparison G K := by
    unfold scalarRoosTensor
    exact CategoryTheory.RoosTensor.chosenComparison_eq G
      (scalarRoosTensorProducts l E F i W) K
  exact scalarRoosTensorNormalization_of_units l E F i W
    (scalarRoosComparison l E W) (scalarRoosComparison l F W)
    (scalarRoosComparison_unit l E W) (scalarRoosComparison_unit l F W) K
    (scalarRoosTensor l E F i W K) hθ

section Augmentation

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] scalarLimitAugmentation scalarLimitArrow
  scalarLimitTensor scalarLimitCofinalInverse baseTensorCounit support arrow

private theorem augmentation_composite
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (G : C ⥤ A) (H : D ⥤ B) (T : C ⥤ D) (F : A ⥤ B)
    (τ : G ⋙ F ⟶ T ⋙ H) {K L : C} {V V₀ : D} {P : A} {Q Z : B}
    (a : P ⟶ G.obj K) (u : K ⟶ L) (q : T.obj L ⟶ V)
    (r : H.obj V ⟶ Z) (b : F.obj P ⟶ Q) (d : Q ⟶ H.obj V₀)
    (v : V₀ ⟶ T.obj K)
    (ha : F.map a ≫ τ.app K = b ≫ d ≫ H.map v) :
    F.map (a ≫ G.map u) ≫ (τ.app L ≫ H.map q ≫ r) =
      b ≫ d ≫ H.map (v ≫ T.map u ≫ q) ≫ r := by
  have hn := τ.naturality u
  dsimp only [Functor.comp_map] at hn
  simp only [F.map_comp, H.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% ha]


private theorem augmentation_tensor
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Q : A ⥤ C) (R : B ⥤ D) (F : C ⥤ D) (E : A ⥤ B)
    (ε : Q ⋙ F ⟶ E ⋙ R)
    {P K : A} {L : C} {Y : B} {N V : D}
    (a : P ⟶ K) (κ : Q.obj K ⟶ L) (τ : F.obj L ⟶ V)
    (θ : E.obj K ⟶ Y) (b : E.obj P ⟶ Y) (c : R.obj Y ⟶ N) (v : N ⟶ V)
    (ht : F.map κ ≫ τ = ε.app K ≫ R.map θ ≫ c ≫ v)
    (hh : E.map a ≫ θ = b) :
    F.map (Q.map a ≫ κ) ≫ τ = ε.app P ≫ (R.map b ≫ c) ≫ v := by
  rw [F.map_comp, Category.assoc, ht]
  have hn := ε.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (F.map (Q.map a)), hn]
  simp only [Category.assoc]
  rw [← R.map_comp_assoc, hh]

/-- Augmentation preservation for the actual compact-support scalar-limit map,
including the zero shifted-product coordinate. No arbitrary comparison is supplied.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: apply scalarRoosTensorNormalization to the strict source augmentation (0,a).
Naturality transports its equality along the representative isomorphism u. Compose
with the actual derived map arrow and the inverse of the recorded cofinal restriction.
scalarLimitMapAugmentation and scalarRoosNormalization identify these last two
operations with composition of the augmentation and restriction of its coordinates.
The defining three-factor formula for scalarLimitArrow gives this equation. -/
theorem scalarLimitArrow_augmentation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X))
    (K : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y) ℤ)
    (uK : DerivedCategory.Q.obj K ≅ (support l E c S).obj M)
    (P : CochainComplex
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y) ℤ)
    (a : ∀ n : ℕ, P ⟶ K.asFunctor.obj (op n))
    (ha : ∀ n : ℕ, a (n + 1) ≫
      K.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n) :
    ∃ h : ∀ n : ℕ,
        ((pbcExtend (constantMap l E F i Y)).mapHomologicalComplex (.up ℤ)).map
            (a (n + 1)) ≫
          (((tensor l E F i Y).mapHomologicalComplex (.up ℤ)).obj K).asFunctor.map
            (homOfLE (Nat.le_succ n)).op =
          ((pbcExtend (constantMap l E F i Y)).mapHomologicalComplex (.up ℤ)).map (a n),
      (baseTensor l E F i Y).map
          (scalarLimitAugmentation l E Y K P a ha ≫ (scalarLimit l E Y).map uK.hom) ≫
          scalarLimitArrow l E F i c S S' e he hepos M =
        baseTensorCounit l E F i Y P ≫
          scalarLimitAugmentation l F Y
            (((tensor l E F i Y).mapHomologicalComplex (.up ℤ)).obj K)
            (((pbcExtend (constantMap l E F i Y)).mapHomologicalComplex (.up ℤ)).obj P)
            (fun n : ℕ ↦
              ((pbcExtend (constantMap l E F i Y)).mapHomologicalComplex (.up ℤ)).map (a n)) h ≫
          (scalarLimit l F Y).map
            ((tensor l E F i Y).mapDerivedCategoryFactors.inv.app K ≫
              (T l E F i Y).map uK.hom ≫ (arrow l E F i c S S' e he hepos).app M) ≫
          scalarLimitCofinalInverse l F Y e hepos
            ((support l F c S').obj
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) := by
  have := (baseTensor_exact l E F i Y).1
  have := (baseTensor_exact l E F i Y).2
  obtain ⟨h, hh⟩ := (scalarRoosTensorNormalization l E F i Y K).2 P a ha
  refine ⟨h, ?_⟩
  unfold scalarLimitArrow
  apply augmentation_composite (scalarLimit l E Y) (scalarLimit l F Y)
    (T l E F i Y) (baseTensor l E F i Y) (scalarLimitTensor l E F i Y).hom
    (scalarLimitAugmentation l E Y K P a ha) uK.hom
    ((arrow l E F i c S S' e he hepos).app M)
    (scalarLimitCofinalInverse l F Y e hepos
      ((support l F c S').obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)))
    (baseTensorCounit l E F i Y P)
    (scalarLimitAugmentation l F Y
      (((tensor l E F i Y).mapHomologicalComplex (.up ℤ)).obj K)
      (((pbcExtend (constantMap l E F i Y)).mapHomologicalComplex (.up ℤ)).obj P)
      (fun n : ℕ ↦
        ((pbcExtend (constantMap l E F i Y)).mapHomologicalComplex (.up ℤ)).map (a n)) h)
    ((tensor l E F i Y).mapDerivedCategoryFactors.inv.app K)
  unfold scalarLimitAugmentation baseTensorCounit
  exact augmentation_tensor DerivedCategory.Q DerivedCategory.Q (baseTensor l E F i Y)
    ((pbcExtend (constantMap l E F i Y)).mapHomologicalComplex (.up ℤ))
    (pbcExtend (constantMap l E F i Y)).mapDerivedCategoryFactors.hom
    (roosAugment a ha) ((scalarRoosComparison l E Y).hom.app K)
    ((scalarLimitTensor l E F i Y).hom.app (DerivedCategory.Q.obj K))
    (scalarRoosTensor l E F i Y K).hom
    (roosAugment (fun n : ℕ ↦
      ((pbcExtend (constantMap l E F i Y)).mapHomologicalComplex (.up ℤ)).map (a n)) h)
    ((scalarRoosComparison l F Y).hom.app
      (((tensor l E F i Y).mapHomologicalComplex (.up ℤ)).obj K))
    ((scalarLimit l F Y).map
      ((tensor l E F i Y).mapDerivedCategoryFactors.inv.app K))
    (by
      set_option backward.isDefEq.respectTransparency false in
        simpa only [baseTensorCounit, Functor.comp_obj] using
      (scalarRoosTensorNormalization l E F i Y K).1) hh

end Augmentation

private theorem projection_adjoint
    {C B : Type*} [Category C] [Category B] {L : C ⥤ B} {R : B ⥤ C}
    (adj : L ⊣ R) {X Y : C} {Z Z' : B}
    {a : X ⟶ Y} {p : Y ⟶ R.obj Z} {q : Z ⟶ Z'} {b : L.obj X ⟶ Z'}
    (h : a ≫ p ≫ R.map q = adj.unit.app X ≫ R.map b) :
    L.map a ≫ (adj.homEquiv Y Z).symm p ≫ q = b := by
  apply (adj.homEquiv X Z').injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    Equiv.apply_symm_apply, adj.homEquiv_unit]
  exact h

section Geometry

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- Normalized reduction and scalar total-limit identification on the specified
compact-support towers, with finite projection and adjoint equations.
Source: Stacks 0941, 07A6, 0GL6; auxiliary comparison Steps 5--6
(blueprint: lem-pur-compact-support-scalar-limit-reduction).

Proof (the seven steps of the DAG node):
1. The coefficient-model comparison gives finite-Tor constructibility of C_X M.
Apply compactSupport_normalized_realization separately over E and F. Its transition
adjunct is the finite compact-support tensor comparison followed by iterated
reduction. Identify the coherent native towers themselves, retaining every power
of the F uniformizer; their quotient cocycles give normalization.
2. Apply normalized-DVR effectivity to these full towers. The resulting epsilon
maps are the adjoints of the actual limit projections under the scalar adjunction,
and are isomorphisms with the identity and all quotient cocycles.
3. Exact pro-etale countable products and strictRoosComparison identify the shifted
product cone with the total right-derived limit, preserving projections and every
strict augmentation (0,a). The whole-system reduction adjunction identifies these
same limits with completed support. scalarCompletion is fixed on local pure tensors
and on complex counits, so supplies the specified ordinary/strict comparison chi.
4. Finite freeness gives scalarLimitTensor, the canonical tensor/product tau.
compactSupportRoosCofinality gives the selection/block rho and its quasi-isomorphism;
scalarRoosNormalization identifies it with scalarLimitRestriction. The recorded
compactSupportStrictScalarMate makes arrow invertible on the asserted domain.
Their composite is scalarLimitArrow. It is natural and preserves augmentations;
transport through scalarCompletion and scalarSupportLimit gives the completed
comparison, so also the completed S_Y-action and the recorded compact-support value.
5. Compute the retained projection of the composite. Selection keeps the en-th
coordinate, block has no projection contribution, and tau tensors each coordinate.
The sourceEvaluation/targetEvaluation equations of the strict mate identify its
level with finiteTensorMap. This is the displayed projection equation.
6. Transpose that equation under the finite scalar/restriction adjunction.
The counits are the specified epsilon maps; scalarReductionBalancing is d_n.
Adjunction naturality gives exactly the displayed finite reduction equation,
including the input tensor associator in the target identification.
7. The two full normalized towers give the epsilon quotient cocycles. Combine these
with the transition equation for arrow and ramified_quotient_square. For any other
commuting coefficient square, apply mate_vcomp and mate_hcomp to the proper and
open squares and cancel their common tensorSquare associator. This yields the
explicit pasted equation, including identity and longer quotient maps. -/
theorem compactSupportScalarLimitReduction (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    : ∃ γ : (finiteTorConstructibleIntegral l E X).ι ⋙ scalarSupport l E c S ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i Y) ⟶
      (finiteTorConstructibleIntegral l E X).ι ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙ scalarSupport l F c S',
      IsIso γ ∧
      ∀ (M : finiteTorConstructibleIntegralCategory l E X),
    finiteTorConstructibleIntegral l F X
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj) ∧
    IsSfDerivedComplete l E Y ((scalarSupport l E c S).obj M.obj) ∧
    IsSfDerivedComplete l F Y ((scalarSupport l F c S').obj
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)) ∧
    (∃ (RE : CoefCompactSupportRealization l E D hl c M.obj)
        (RF : CoefCompactSupportRealization l F D hl c
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)),
      CoefCompactSupportRealizationSpec l E D hl c M.obj RE ∧
      CoefCompactSupportRealizationSpec l F D hl c
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj) RF ∧
      RE.normalized.tower = (scalarSupportCompletedTower l E c S).obj M.obj ∧
      RF.normalized.tower = (scalarSupportCompletedTower l F c S').obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)) ∧
    (∀ (m n : ℕ) (h : n ≤ m),
      scalarSupportNativeCounit l E c S m M.obj ≫
          (coefficientSequenceDerivedTransition l E Y h).app
            ((scalarSupportNative l E c S).obj M.obj) =
        normalizedDVRReductionTransition l E Y D hl h ((scalarSupport l E c S).obj M.obj) ≫
          (normalizedDVRRes l E Y h).map (scalarSupportNativeCounit l E c S n M.obj)) ∧
    (∀ (m n : ℕ) (h : n ≤ m),
      scalarSupportNativeCounit l F c S' m
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj) ≫
          (coefficientSequenceDerivedTransition l F Y h).app
            ((scalarSupportNative l F c S').obj
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)) =
        normalizedDVRReductionTransition l F Y D hl h
            ((scalarSupport l F c S').obj
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)) ≫
          (normalizedDVRRes l F Y h).map
            (scalarSupportNativeCounit l F c S' n
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj))) ∧
    (∀ n : ℕ, IsIso (scalarSupportCounit l E c S n M.obj) ∧
      IsIso (scalarSupportCounit l F c S' n
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj))) ∧
    IsIso (scalarLimitArrow l E F i c S S' e he hepos M.obj) ∧
    ((baseTensor l E F i Y).map
          ((scalarSupportLimit l E c S).hom.app M.obj) ≫
          scalarLimitArrow l E F i c S S' e he hepos M.obj =
        (scalarCompletion l E F i Y).hom.app
            ((scalarSupport l E c S).obj M.obj) ≫
          (scalarConstantRestriction l F Y).map
            (γ.app M) ≫
          (scalarSupportLimit l F c S').hom.app
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)) ∧
    (∀ n : ℕ,
      scalarLimitArrow l E F i c S S' e he hepos M.obj ≫
          (scalarLimitProjection l F Y (e * (n + 1) - 1)).app
            ((support l F c S').obj
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)) ≫
          (positiveSupportEvaluation l F c S' (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n))).hom.app
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj) ≫
          (positiveRestriction l F Y (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
              ((PurCompactSupport.image (PurCompactSupport.finite l F (e * (n + 1))
                (Nat.mul_pos hepos (Nat.le_add_left 1 n))) c).map
                  ((scalarReductionBalancing l E F i X e he hepos n).hom.app M.obj)) =
        (baseTensor l E F i Y).map
            ((scalarLimitProjection l E Y n).app ((support l E c S).obj M.obj) ≫
              (supportEvaluation l E c S n).hom.app M.obj) ≫
          (finiteBalancing l E F i Y e he hepos n).hom.app
            ((PurCompactSupport.image (PurCompactSupport.finite l E (n + 1)
              (Nat.le_add_left 1 n)) c).obj
                ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
                  (Nat.le_add_left 1 n) X)).obj M.obj)) ≫
          (positiveRestriction l F Y (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
              (PurCompactSupport.finiteTensorMap l E F i e he hepos n c M.obj)) ∧
    (∀ n : ℕ,
      γ.app M ≫
          scalarSupportPositiveProjection l F c S' (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n))
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj) ≫
          (pbcDerivedRestrict (PurCompactSupport.projection l F (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).map
            ((PurCompactSupport.image (PurCompactSupport.finite l F (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n))) c).map
                ((scalarReductionBalancing l E F i X e he hepos n).hom.app M.obj)) =
        (pbcDerivedScalarAdjunction (PurCompactSupport.projection l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).unit.app _ ≫
          (pbcDerivedRestrict (PurCompactSupport.projection l F (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).map
            ((scalarReductionBalancing l E F i Y e he hepos n).hom.app
                ((scalarSupport l E c S).obj M.obj) ≫
              (pbcDerivedExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
                (Nat.le_add_left 1 n)).map Y)).map (scalarSupportCounit l E c S n M.obj) ≫
              PurCompactSupport.finiteTensorMap l E F i e he hepos n c M.obj)) ∧
    (∀ n : ℕ,
      (pbcDerivedExtend (PurCompactSupport.projection l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).map
          (γ.app M) ≫
        scalarSupportPositiveCounit l F c S' (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n))
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj) ≫
        (PurCompactSupport.image (PurCompactSupport.finite l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n))) c).map
            ((scalarReductionBalancing l E F i X e he hepos n).hom.app M.obj) =
      (scalarReductionBalancing l E F i Y e he hepos n).hom.app
          ((scalarSupport l E c S).obj M.obj) ≫
        (pbcDerivedExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n)).map Y)).map (scalarSupportCounit l E c S n M.obj) ≫
        PurCompactSupport.finiteTensorMap l E F i e he hepos n c M.obj) ∧
    (∀ (m n : ℕ) (hmn : n ≤ m)
      (K : DerivedCategory (pbcModules X ((PurCompactSupport.finite l E (m + 1)
        (Nat.le_add_left 1 m)).ring X))),
      PurCompactSupport.ComparisonSquareEquation
        (PurCompactSupport.finiteChange l E F i e he hepos (m + 1)
          (Nat.le_add_left 1 m))
        (PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n))
        (PurCompactSupport.finiteQuotientChange l E (m + 1) (n + 1)
          (Nat.le_add_left 1 m) (Nat.le_add_left 1 n) (Nat.add_le_add_right hmn 1))
        (PurCompactSupport.finiteQuotientChange l F (e * (m + 1)) (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 m))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n))
          (Nat.mul_le_mul_left e (Nat.add_le_add_right hmn 1)))
        (PurCompactSupport.ramified_quotient_square l E F i e he hepos (m + 1) (n + 1)
          (Nat.le_add_left 1 m) (Nat.le_add_left 1 n) (Nat.add_le_add_right hmn 1)) c K) ∧
    (∀ {R S₀ A B : PurCompactSupport.Coefficients.{u}}
      (a : PurCompactSupport.Change R S₀) (b : PurCompactSupport.Change A B)
      (r : PurCompactSupport.Change R A) (s : PurCompactSupport.Change S₀ B)
      (h : ∀ W, a.map W ≫ s.map W = r.map W ≫ b.map W)
      (K : DerivedCategory (pbcModules X (R.ring X))),
      (pbcDerivedExtend (s.map Y)).map ((PurCompactSupport.comparison a c).app K) ≫
          (PurCompactSupport.comparison s c).app ((pbcDerivedExtend (a.map X)).obj K) ≫
          (PurCompactSupport.image B c).map
            ((PurCompactSupport.tensorSquare (a.map X) (b.map X) (r.map X) (s.map X)
              (h X)).hom.app K) =
        (PurCompactSupport.tensorSquare (a.map Y) (b.map Y) (r.map Y) (s.map Y)
          (h Y)).hom.app ((PurCompactSupport.image R c).obj K) ≫
          (pbcDerivedExtend (b.map Y)).map ((PurCompactSupport.comparison r c).app K) ≫
          (PurCompactSupport.comparison b c).app ((pbcDerivedExtend (r.map X)).obj K)) := by
  obtain ⟨γ, hγ, hcomparison⟩ :=
    scalarLimitCompletedComparison l E F i D hl f c S S' e he hepos
  refine ⟨γ, hγ, ?_⟩
  intro M
  have hF := (compactSupportCoefficientModels_scalar l E F i D hl e hepos he X
    M.obj M.property).1
  have hE := compactSupport_native_effectivity l E D hl c S M.obj M.property.1
  have hFsupport := compactSupport_native_effectivity l F D hl c S'
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj) hF.1
  obtain ⟨RE, hRE, hREtower⟩ :=
    compactSupport_native_realization l E D hl c S M.obj M.property.1
  obtain ⟨RF, hRF, hRFtower⟩ := compactSupport_native_realization l F D hl c S'
    ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj) hF.1
  have hstrict := (compactSupportStrictScalarMate l E F i D hl f c S S' e he hepos).1
  have harrow : IsIso ((arrow l E F i c S S' e he hepos).app M.obj) := by
    have := hstrict
    exact (inferInstance : IsIso
      ((Functor.whiskerLeft (finiteTorConstructibleIntegral l E X).ι
        (arrow l E F i c S S' e he hepos)).app M))
  have hlimit : IsIso (scalarLimitArrow l E F i c S S' e he hepos M.obj) := by
    have := harrow
    have := scalarLimitRestriction_isIso l F Y e hepos
    unfold scalarLimitArrow scalarLimitCofinalInverse
    infer_instance
  have hMcomparison := hcomparison M
  refine ⟨hF, hE.1, hFsupport.1, ⟨RE, RF, hRE, hRF, hREtower, hRFtower⟩,
    hE.2.1, hFsupport.2.1, (fun n ↦ ⟨hE.2.2 n, hFsupport.2.2 n⟩), hlimit,
    hMcomparison.1, hMcomparison.2.1, hMcomparison.2.2, ?_, ?_, ?_⟩
  · intro n
    apply projection_adjoint
      (pbcDerivedScalarAdjunction (PurCompactSupport.projection l F (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y))
    exact hMcomparison.2.2 n
  · intro m n hmn K
    exact PurCompactSupport.comparison_quotients l E F i e he hepos
      (m + 1) (n + 1) (Nat.le_add_left 1 m) (Nat.le_add_left 1 n)
      (Nat.add_le_add_right hmn 1) c K
  · intro R S₀ A B a b r s h K
    exact PurCompactSupport.comparisonSquare a b r s h c K

end Geometry
end WeilConjectures.PurStrictScalar
