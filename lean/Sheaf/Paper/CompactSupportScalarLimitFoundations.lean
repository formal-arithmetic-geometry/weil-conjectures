module

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
import Sheaf.Paper.CompactSupportCoefficientModels
import Sheaf.Paper.CompletedScalarLocalizationBalancing
import all Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
import Sheaf.CategoryTheory.StrictRoosDerivation
import all Sheaf.CategoryTheory.DerivedExactSquareCoherence
import Mathlib.CategoryTheory.Limits.Final
import all Sheaf.CategoryTheory.ConstantFiniteFreeSectionBasis
import all Sheaf.Paper.CompletedIntegralFiniteFree
import Sheaf.Paper.ScalarLimitTensorKInjective
import Sheaf.Paper.ScalarLimitRestrictionKInjective
import Sheaf.Paper.ScalarLimitRestrictionLimits

/-! # Foundations of normalized compact-support scalar limits

The canonical scalar limits, arithmetic restriction, completed coefficient
balancing, and native compact-support limit comparisons.
Source: Stacks Tags 0941, 06YY and 099L
(blueprint: def-pur-compact-support-scalar-limit-maps).
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

/-- Additivity of the actual inverse-limit functor follows from its finite products.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarLimit_additive (W : Scheme.{u}) :
    (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤
      Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The specified total derived inverse limit on discrete integral strict towers.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
abbrev scalarLimit (W : Scheme.{u}) :=
  (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤
    Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W).rightDerivedFunctor

/-- The actual limit projection, derived from the ordinary cone leg.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitProjection (W : Scheme.{u}) (n : ℕ) :
    scalarLimit l E W ⟶ ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W n :=
  Functor.rightDerivedFunctorNatTrans (lim.π (op n)) ≫
    (((evaluation ℕᵒᵖ
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W)).obj
        (op n)).rightDerivedFunctorIsoMapDerivedCategory).hom

/-- Ordinary restriction of the limit cone to the arithmetic subsequence.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitRestrictionOrdinary (W : Scheme.{u}) (e : ℕ) :
    (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤ _) ⟶
      ordinarySubsequence l E W e ⋙ lim where
  app K := limit.pre K (CategoryTheory.StrictTowerArithmetic.index e)
  naturality _K _L a := limit.map_pre a (CategoryTheory.StrictTowerArithmetic.index e)

/-- Canonical derived arithmetic restriction, with the ordinary cone normalization.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitRestriction (W : Scheme.{u}) (e : ℕ) :
    scalarLimit l E W ⟶ subsequence l E W e ⋙ scalarLimit l E W :=
  Functor.rightDerivedPullback (ordinarySubsequence l E W e)
    (scalarLimitRestrictionOrdinary l E W e)

/-- Finite-free integral scalar extension is exact and preserves strict K-injectives.
Source: Stacks 03CY, 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: one integral basis identifies restricted tensor with a finite biproduct,
including all tower transitions. The dual basis makes tensor a right adjoint of
an exact functor. The exact-left-adjoint criterion gives preservation of K-injectives. -/
theorem scalarLimitTensor_exact (W : Scheme.{u}) :
    PreservesFiniteLimits (pbcExtend (constantMap l E F i W)) ∧
      PreservesFiniteColimits (pbcExtend (constantMap l E F i W)) ∧
      PreservesLimitsOfShape ℕᵒᵖ (pbcExtend (constantMap l E F i W)) ∧
      (tensor l E F i W).PreservesKInjectiveComplexes := by
  have h := baseTensor_exact l E F i W
  have hlim := scalarTensor_preservesLimits l E F i W (ℕᵒᵖ)
  exact ⟨h.1, h.2, hlim, scalarTensor_preservesKInjective l E F i W⟩

/-- The canonical tensor/product comparison on total derived limits. Its factors
are the unit-normalized derived-composite comparisons and ordinary limit comparison.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitTensor (W : Scheme.{u}) :
    scalarLimit l E W ⋙ baseTensor l E F i W ≅
      T l E F i W ⋙ scalarLimit l F W :=
  haveI := (scalarLimitTensor_exact l E F i W).1
  haveI := (scalarLimitTensor_exact l E F i W).2.1
  haveI := (scalarLimitTensor_exact l E F i W).2.2.1
  haveI := (scalarLimitTensor_exact l E F i W).2.2.2
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤ _)
      (pbcExtend (constantMap l E F i W))).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (preservesLimitNatIso (J := ℕᵒᵖ) (pbcExtend (constantMap l E F i W))) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso (tensor l E F i W)
      (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W ⥤ _)

private theorem scalarIndex_initial (e : ℕ) (he : 1 ≤ e) :
    (CategoryTheory.StrictTowerArithmetic.index e).Initial := by
  let ceil : ℕᵒᵖ ⥤ ℕᵒᵖ :=
    (show ℕ →o ℕ from
      { toFun := fun n ↦ n / e
        monotone' := fun _ _ h ↦ Nat.div_le_div_right h }).monotone.functor.op
  have hgc (a n : ℕ) : a / e ≤ n ↔ a ≤ e * (n + 1) - 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (show 0 < e from he)]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  let adj : CategoryTheory.StrictTowerArithmetic.index e ⊣ ceil :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun n a ↦
          { toFun := fun f ↦ (homOfLE ((hgc a.unop n.unop).2 f.unop.le)).op
            invFun := fun f ↦ (homOfLE ((hgc a.unop n.unop).1 f.unop.le)).op
            left_inv := fun _ ↦ Subsingleton.elim _ _
            right_inv := fun _ ↦ Subsingleton.elim _ _ } }
  exact Functor.initial_of_adjunction adj

/-- Arithmetic restriction is invertible for every full tower and positive e.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: use compactSupportRoosCofinality on a simultaneous strict K-injective
resolution. Its selection/block map is a quasi-isomorphism and is the restriction
of the ordinary limit cone under strictRoosComparison. Cancel the derived units. -/
theorem scalarLimitRestriction_isIso (W : Scheme.{u}) (e : ℕ) (he : 1 ≤ e) :
    IsIso (scalarLimitRestriction l E W e) := by
  let A := Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W
  let P := ordinarySubsequence l E W e
  let H : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤ A := lim
  let α := scalarLimitRestrictionOrdinary l E W e
  have := scalarIndex_initial e he
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    change IsIso (limit.pre K (CategoryTheory.StrictTowerArithmetic.index e))
    infer_instance
  have : P.PreservesKInjectiveComplexes := subsequence_preservesKInjective l E W e he
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  obtain ⟨I, hI, ⟨uI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  have hi : IsIso ((Functor.rightDerivedPullback P α).app (DerivedCategory.Q.obj I)) := by
    have h := Functor.rightDerivedFunctorUnitQ_rightDerivedPullback_app' P α I
    have : IsIso (H.rightDerivedFunctorUnitQ I) := by
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have : IsIso (H.rightDerivedFunctorUnitQ ((P.mapHomologicalComplex (.up ℤ)).obj I)) := by
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have : IsIso ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I) := by
      have (n : ℤ) : IsIso (((NatTrans.mapHomologicalComplex α (.up ℤ)).app I).f n) :=
        inferInstanceAs (IsIso (α.app (I.X n)))
      exact HomologicalComplex.Hom.isIso_of_components _
    have : IsIso (H.rightDerivedFunctorUnitQ I ≫
        (Functor.rightDerivedPullback P α).app (DerivedCategory.Q.obj I)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (H.rightDerivedFunctorUnitQ I) _
  have hn := (Functor.rightDerivedPullback P α).naturality uI.hom
  have : IsIso ((Functor.rightDerivedPullback P α).app M ≫
      (P.mapDerivedCategory ⋙ H.rightDerivedFunctor).map uI.hom) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right ((Functor.rightDerivedPullback P α).app M)
    ((P.mapDerivedCategory ⋙ H.rightDerivedFunctor).map uI.hom)

/-- The inverse of the specific arithmetic restriction, using its cofinality theorem.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitCofinalInverse (W : Scheme.{u}) (e : ℕ) (he : 1 ≤ e)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :
    (scalarLimit l E W).obj ((subsequence l E W e).obj K) ⟶
      (scalarLimit l E W).obj K :=
  haveI := scalarLimitRestriction_isIso l E W e he
  inv ((scalarLimitRestriction l E W e).app K)

/-- The scalar-limit map is formed from the recorded strict scalar mate itself.
The inverse is the inverse of the actual cofinal restriction, not an arbitrary iso.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarLimitArrow {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (baseTensor l E F i Y).obj ((support l E c S ⋙ scalarLimit l E Y).obj M) ⟶
      (support l F c S' ⋙ scalarLimit l F Y).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) :=
  (scalarLimitTensor l E F i Y).hom.app ((support l E c S).obj M) ≫
    (scalarLimit l F Y).map ((arrow l E F i c S S' e he hepos).app M) ≫
    scalarLimitCofinalInverse l F Y e hepos
      ((support l F c S').obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))


private theorem restriction_preservesLimits
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} α) := by
  let U := SheafOfModules.toSheaf.{u + 1} R
  let e : SheafOfModules.restrictScalars α ⋙ U ≅ SheafOfModules.toSheaf.{u + 1} S :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars α ⋙ U) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

private theorem restriction_preservesColimits
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} α) := by
  let U := SheafOfModules.toSheaf.{u + 1} R
  let e : SheafOfModules.restrictScalars α ⋙ U ≅ SheafOfModules.toSheaf.{u + 1} S :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars α ⋙ U) :=
    preservesFiniteColimits_of_natIso e.symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ U

/-- Restriction to constant scalars preserves finite limits, detected on abelian
sheaves. Source: Stacks 03DA
(blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarConstantRestriction_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (constantRestriction l E W) :=
  restriction_preservesLimits (integralConstantToCompletionOfUniverses l E W)

/-- Restriction to constant scalars preserves finite colimits, detected on abelian
sheaves. Source: Stacks 03DA
(blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarConstantRestriction_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (constantRestriction l E W) :=
  restriction_preservesColimits (integralConstantToCompletionOfUniverses l E W)

/-- Additivity of the specified constant restriction.
Source: Stacks 03DA (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarConstantRestriction_additive (W : Scheme.{u}) :
    (constantRestriction l E W).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The exact constant restriction on the fixed derived module categories.
Source: Stacks 03DA (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarConstantRestriction (W : Scheme.{u}) :=
  (constantRestriction l E W).mapDerivedCategory

/-- The ordinary scalar/completion composite is additive.
Source: Stacks 03DA (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarCompletionTarget_additive (W : Scheme.{u}) :
    (pbcExtend (completedCoefficientMap l E F i W) ⋙ constantRestriction l F W).Additive := by
  infer_instance

/-- The canonical composition identification for finite restriction.
Source: Stacks 03DA (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarFiniteRestrictionComp (W : Scheme.{u}) (n : ℕ) :
    pbcDerivedRestrict (PurCompactSupport.projection l E (n + 1)
      (Nat.le_add_left 1 n) W) ⋙ scalarConstantRestriction l E W ≅
        finiteRestriction l E W n :=
  haveI := scalarConstantRestriction_limits l E W
  haveI := scalarConstantRestriction_colimits l E W
  (Functor.mapDerivedCategoryCompIso
    (pbcRestrict (PurCompactSupport.projection l E (n + 1)
      (Nat.le_add_left 1 n) W)) (constantRestriction l E W)).symm

/-- Ordinary scalar/completion balancing, determined on every local pure tensor.
Source: Stacks 03EK, 099L (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: an integral basis makes completed scalar extension a finite biproduct.
The displayed pure-tensor map and its inverse descend through tensor relations
and sheafification. Local pure tensors generate, proving uniqueness and naturality. -/
theorem scalarCompletionOrdinary_existsUnique (W : Scheme.{u}) :
    ∃! β : constantRestriction l E W ⋙ pbcExtend (constantMap l E F i W) ≅
        pbcExtend (completedCoefficientMap l E F i W) ⋙ constantRestriction l F W,
      ∀ (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
        (b : ((constants l F).ring W).obj.obj U) (x : M.val.obj U),
        (β.hom.app M).val.app U
            (pbcTensorSection (constantMap l E F i W)
              ((constantRestriction l E W).obj M) U b x) =
          pbcTensorSection (completedCoefficientMap l E F i W) M U
            (((integralConstantToCompletionOfUniverses l F W).hom.app U) b) x := by
  exact compactSupportCoefficientModels_ordinary l E F i W

/-- The ordinary balancing map with its prescribed pure-tensor normalization.
Source: Stacks 03EK (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarCompletionOrdinary (W : Scheme.{u}) :=
  (scalarCompletionOrdinary_existsUnique l E F i W).choose

/-- Termwise localization of the already fixed ordinary balancing.
Source: Stacks 06YY (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarCompletionOrdinaryComplex (W : Scheme.{u}) :
    (constantRestriction l E W ⋙ pbcExtend (constantMap l E F i W)).mapHomologicalComplex
        (.up ℤ) ≅
      (pbcExtend (completedCoefficientMap l E F i W) ⋙
        constantRestriction l F W).mapHomologicalComplex (.up ℤ) :=
  haveI := scalarConstantRestriction_additive l F W
  haveI := scalarCompletionTarget_additive l E F i W
  NatIso.mapHomologicalComplex (scalarCompletionOrdinary l E F i W) (.up ℤ)

/-- The scalar/completion comparison is fixed on all complex counits, before
passing to finite levels. It therefore cannot be an independently chosen iso.
Source: Stacks 06YY, 099L (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: finite freeness makes both ordinary tensors exact. Localize the prescribed
ordinary balancing; the universal derived counits give the equation and uniqueness. -/
theorem scalarCompletion_existsUnique (W : Scheme.{u}) :
    ∃! χ : scalarConstantRestriction l E W ⋙ baseTensor l E F i W ≅
        pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙
          scalarConstantRestriction l F W,
      ∀ P : CochainComplex (scalarReductionSource l E W) ℤ,
        χ.hom.app (DerivedCategory.Q.obj P) ≫
            (constantRestriction l F W).mapDerivedCategory.map
              (pbcComplexCounit (completedCoefficientMap l E F i W) P) ≫
            (constantRestriction l F W).mapDerivedCategoryFactors.hom.app
              (((pbcExtend (completedCoefficientMap l E F i W)).mapHomologicalComplex
                (.up ℤ)).obj P) =
          (baseTensor l E F i W).map
              ((constantRestriction l E W).mapDerivedCategoryFactors.hom.app P) ≫
            baseTensorCounit l E F i W
              (((constantRestriction l E W).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((scalarCompletionOrdinaryComplex l E F i W).hom.app P) := by
  simpa only [scalarConstantRestriction, scalarCompletionOrdinaryComplex] using
    completedScalarBalancing_existsUnique l E F i W (scalarCompletionOrdinary l E F i W)

/-- The quotient-compatible ordinary/strict scalar comparison χ.
Source: Stacks 06YY (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarCompletion (W : Scheme.{u}) :=
  (scalarCompletion_existsUnique l E F i W).choose

attribute [local irreducible] scalarCompletion

attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived

/-- The specified separately derived proper/open quotient system before restriction.
Source: Stacks 0940 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSupportNative {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :=
  S.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g

/-- The native whole quotient tower with completed, rather than constant, scalars.
Source: Stacks 0940 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSupportCompletedTower {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :=
  scalarSupportNative l E c S ⋙ coefficientSequenceDerivedRestriction l E Y

/-- Compact support P^c is the total derived inverse limit of this native system.
Source: blueprint def-weil-integral-rational-qbar-compact-support; Stacks 0941
(blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSupport {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :=
  scalarSupportNative l E c S ⋙ coefficientSequenceLimit l E Y

/-- Native evaluation with its finite coefficient scalars retained. Each factor is
an existing normalized singleton or derived scalar-adjunction comparison.
Source: Stacks 0940 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSupportEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X) (n : ℕ) :
    scalarSupportNative l E c S ⋙ coefficientSequenceDerivedEvaluation l E Y n ≅
      pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
        (Nat.le_add_left 1 n) X) ⋙
        PurCompactSupport.image (PurCompactSupport.finite l E (n + 1)
          (Nat.le_add_left 1 n)) c :=
  Functor.isoWhiskerLeft S.reduction (compactSupportSystemEvaluation l E c n) ≪≫
    Functor.isoWhiskerRight (S.reductionEvaluation n)
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))) ≪≫
    Functor.isoWhiskerRight (PurCompactSupport.finiteReductionIso l E X n).symm
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))) ≪≫
    Functor.isoWhiskerLeft
      (pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
        (Nat.le_add_left 1 n) X)) (PurCompactSupport.finiteImageIso l E n c).symm

/-- The actual completed-coefficient limit projection to the restricted finite image.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSupportProjection {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (n : ℕ) (M : DerivedCategory (scalarReductionSource l E X)) :=
  (coefficientSequenceProjection l E Y n).app ((scalarSupportNative l E c S).obj M) ≫
    (coefficientFiniteDerivedRestriction l E Y n).map
      ((scalarSupportEvaluation l E c S n).hom.app M)

/-- Epsilon is the adjunct of the actual limit projection; no compact-support
comparison or finite-level isomorphism is substituted for this definition.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSupportCounit {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (n : ℕ) (M : DerivedCategory (scalarReductionSource l E X)) :=
  ((pbcDerivedScalarAdjunction (PurCompactSupport.projection l E (n + 1)
    (Nat.le_add_left 1 n) Y)).homEquiv _ _).symm (scalarSupportProjection l E c S n M)

/-- The projection adjunct before the finite proper/open presentation is applied.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSupportNativeCounit {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (n : ℕ) (M : DerivedCategory (scalarReductionSource l E X)) :=
  ((coefficientFiniteAdjunction l E Y n).homEquiv _ _).symm
    ((coefficientSequenceProjection l E Y n).app ((scalarSupportNative l E c S).obj M))

/-- Positive-exponent projection without an implicit predecessor transport.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSupportPositiveProjection {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (m : ℕ) (hm : 1 ≤ m) (M : DerivedCategory (scalarReductionSource l E X)) :
    (scalarSupport l E c S).obj M ⟶
      (pbcDerivedRestrict (PurCompactSupport.projection l E m hm Y)).obj
        ((PurCompactSupport.image (PurCompactSupport.finite l E m hm) c).obj
          ((pbcDerivedExtend (PurCompactSupport.projection l E m hm X)).obj M)) :=
  match m, hm with
  | 0, h => False.elim (Nat.not_succ_le_zero 0 h)
  | n + 1, _ => scalarSupportProjection l E c S n M

/-- Positive-exponent epsilon, still the adjunct of the specified projection.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSupportPositiveCounit {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (m : ℕ) (hm : 1 ≤ m) (M : DerivedCategory (scalarReductionSource l E X)) :=
  ((pbcDerivedScalarAdjunction (PurCompactSupport.projection l E m hm Y)).homEquiv _ _).symm
    (scalarSupportPositiveProjection l E c S m hm M)

/-- Restriction from completed to constant scalars commutes with the derived limit.
Source: Stacks 03DA, 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction).
Proof: restriction is exact and preserves ordinary limits. The constant-to-completed
map is flat (torsion-free over the discrete valuation ring), so its tensor left
adjoint is exact and restriction preserves K-injectives, also on whole towers. -/
theorem scalarLimitRestriction_exact (W : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ (constantRestriction l E W) ∧
      (towerConstantRestriction l E W).PreservesKInjectiveComplexes := by
  exact ⟨scalarRestriction_preservesLimits l E W,
    scalarRestriction_preservesKInjective l E W⟩

/-- The canonical limit/restriction comparison, with the universal derived units.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarCompletedLimitRestriction (W : Scheme.{u}) :
    coefficientConstantTowerLimit l E W ⋙ scalarConstantRestriction l E W ≅
      toConstant l E W ⋙ scalarLimit l E W :=
  letI : Abelian.HasKInjectiveResolutions
      (ℕᵒᵖ ⥤ scalarReductionSource l E W) :=
    coefficientConstantTowersKInjectives.{u, u} l E W
  haveI := scalarConstantRestriction_limits l E W
  haveI := scalarConstantRestriction_colimits l E W
  haveI := (scalarLimitRestriction_exact l E W).1
  haveI := (scalarLimitRestriction_exact l E W).2
  haveI := (towerConstantRestriction_exact l E W).1
  haveI := (towerConstantRestriction_exact l E W).2
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ _) (constantRestriction l E W)).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (preservesLimitNatIso (J := ℕᵒᵖ) (constantRestriction l E W)) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso
      (C := ℕᵒᵖ ⥤ scalarReductionSource l E W)
      (towerConstantRestriction l E W)
      (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤ _)

/-- Restriction of the same native system, as a composite of exact derived functors.
Source: Stacks 0940 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSystemRestrictionComp (W : Scheme.{u}) :
    systemU l E W ≅ coefficientSequenceDerivedRestriction l E W ⋙ toConstant l E W :=
  haveI := (towerConstantRestriction_exact l E W).1
  haveI := (towerConstantRestriction_exact l E W).2
  Functor.mapDerivedCategoryCompIso (coefficientSequenceRestriction l E W)
    (towerConstantRestriction l E W)

/-- The actual native completed limit restricted to constants is the same strict
constant-coefficient limit, through universal derived-composite comparisons.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarSupportLimit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    scalarSupport l E c S ⋙ scalarConstantRestriction l E Y ≅
      support l E c S ⋙ scalarLimit l E Y :=
  Functor.isoWhiskerLeft (scalarSupportNative l E c S)
    (Functor.isoWhiskerLeft (coefficientSequenceDerivedRestriction l E Y)
      (scalarCompletedLimitRestriction l E Y)) ≪≫
    Functor.isoWhiskerLeft (scalarSupportNative l E c S)
      (Functor.isoWhiskerRight (scalarSystemRestrictionComp l E Y).symm (scalarLimit l E Y))

/-- The canonical tensor reassociation d_n at the ramified finite quotient.
Source: Stacks 06YY (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarReductionBalancing (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) (n : ℕ) :=
  PurCompactSupport.tensorSquare (completedCoefficientMap l E F i W)
    ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n)).map W)
    (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W)
    (PurCompactSupport.projection l F (e * (n + 1))
      (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W)
    (PurCompactSupport.ramified_reduction_square l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n) W)

/-- Exact countable products on this specific constant coefficient category.
Source: blueprint det-pe-products-exact
(blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
instance scalarRoos_exactProducts (W : Scheme.{u}) :
    HasExactLimitsOfShape (Discrete ℕ)
      (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :=
  ProEt.products_exact.{u, u, 0} W _ ℕ

/-- The recorded cofinality map, fixed by its selection and block coordinates.
The witness is determined as a chain map by those coordinates, not just up to iso.
Source: Stacks 0941 (blueprint: lem-pur-compact-support-scalar-limit-reduction). -/
def scalarRoosRestriction (W : Scheme.{u})
    (K : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
    (e : ℕ) (he : 1 ≤ e) :=
  (compactSupportRoosCofinality.{u + 1, u, 0} (ProEt.topology W)
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).choose K e he


end WeilConjectures.PurStrictScalar
