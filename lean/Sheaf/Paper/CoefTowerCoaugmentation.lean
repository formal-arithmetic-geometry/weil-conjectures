/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.IntegralCompactSupportPrescribedReductions
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.MixedTensorPointwiseLeftDerived
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.DerivedReductionResolutionIndependence
import Sheaf.Paper.QcqsCompactSupportRealization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Generator.Presheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# The compact-support tower coaugmentation

Source: Weil blueprint, `prop-coef-integral-dualizing`, proof paragraph 2, third
mapping-complex comparison; Stacks Tags 0940, 0941, 09T5 and 0FND
(blueprint: lem-coef-tower-coaugmentation).

## Main definitions

- `adjunction`, `projection`: the actual derived constant/limit adjunction and its projections.
- `compactSupportProjection`, `coaugmentation`: the specified projection and derived counit map.

## Main statements

- `compactSupport_tower_coaugmentation`: natural comparison, evaluation, and scalar adjunct.

The index `n : ℕ` denotes exponent `n+1`. All coefficient modules use the existing
common `ULift` to the point-section universe. The input strict tower and its natural
evaluation identifications are supplied, rather than chosen from a mere existence
statement. All transitions, including nonadjacent ones, are constrained below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale MonoidalCategory
namespace WeilConjectures.CoefTower

/-- Standard localization of ordinary strict module towers.
Source: Stacks Tag 0941 (blueprint: lem-coef-tower-coaugmentation). -/
instance moduleTowersDerived (R : Type r) [CommRing R] :
    HasDerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{r} R) := HasDerivedCategory.standard _

/-- Ordinary module towers admit simultaneous K-injective resolutions.
Source: Stacks Tags 079P and 0941 (blueprint: lem-coef-tower-coaugmentation).
Proof: realize the functor category as module sheaves on the sequence site over
one point. The free diagrams on the regular module give a small generating family,
and filtered colimits are exact levelwise. Thus it is Grothendieck abelian; apply
the functorial K-injective resolution theorem. -/
@[instance]
theorem moduleTowersKInjectives (R : Type r) [CommRing R] :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ ModuleCat.{r} R) := by
  let A := ModuleCat.{r} R
  let : HasFilteredColimitsOfSize.{r, r} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{r, r} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A) := {}
  exact Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

/-- Inverse limit is additive, since it preserves finite products.
Source: Stacks Tag 0940 (blueprint: lem-coef-tower-coaugmentation). -/
instance moduleLimitAdditive (R : Type r) [CommRing R] :
    (lim : (ℕᵒᵖ ⥤ ModuleCat.{r} R) ⥤ ModuleCat.{r} R).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The exact constant functor after localization, retaining the strict diagram.
Source: Stacks Tag 0940 (blueprint: lem-coef-tower-coaugmentation). -/
abbrev constant (R : Type r) [CommRing R] [HasDerivedCategory (ModuleCat.{r} R)] :=
  (Functor.const ℕᵒᵖ : ModuleCat.{r} R ⥤ (ℕᵒᵖ ⥤ ModuleCat.{r} R)).mapDerivedCategory

/-- Total derived inverse limit of ordinary module towers.
Source: Stacks Tag 0941 (blueprint: lem-coef-tower-coaugmentation). -/
abbrev totalLimit (R : Type r) [CommRing R] [HasDerivedCategory (ModuleCat.{r} R)] :=
  (lim : (ℕᵒᵖ ⥤ ModuleCat.{r} R) ⥤ ModuleCat.{r} R).rightDerivedFunctor

/-- The derived adjunction is the one induced from the actual constant/limit adjunction.
Source: Stacks Tags 09T5 and 0FND (blueprint: lem-coef-tower-coaugmentation). -/
def adjunction (R : Type r) [CommRing R] [HasDerivedCategory (ModuleCat.{r} R)] :
    constant R ⊣ totalLimit R :=
  (constLimAdj : (Functor.const ℕᵒᵖ : ModuleCat.{r} R ⥤ _) ⊣ lim)
    |>.mapDerivedCategoryRightDerivedAdjunction

/-- Exact evaluation of an ordinary strict derived tower.
Source: Stacks Tag 0941 (blueprint: lem-coef-tower-coaugmentation). -/
abbrev evaluate (R : Type r) [CommRing R] [HasDerivedCategory (ModuleCat.{r} R)]
    (n : ℕ) :=
  ((evaluation ℕᵒᵖ (ModuleCat.{r} R)).obj (op n)).mapDerivedCategory

/-- The projection obtained by deriving the actual ordinary limit projection.
Source: Stacks Tag 0941 (blueprint: lem-coef-tower-coaugmentation). -/
def projection (R : Type r) [CommRing R] [HasDerivedCategory (ModuleCat.{r} R)]
    (n : ℕ) : totalLimit R ⟶ evaluate R n :=
  Functor.rightDerivedFunctorNatTrans (lim.π (op n)) ≫
    (Functor.rightDerivedFunctorIsoMapDerivedCategory
      ((evaluation ℕᵒᵖ (ModuleCat.{r} R)).obj (op n))).hom

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing integral coefficient ring in the point-section universe.
Source: blueprint coefficient-point convention (blueprint: lem-coef-tower-coaugmentation). -/
abbrev coefficient := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The levelwise sections functor, before any inverse limit is taken.
Source: Stacks Tag 0940 (blueprint: lem-coef-tower-coaugmentation). -/
abbrev towerSections :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointIntegralSections l E D.k)

/-- Levelwise exact sections preserve finite limits of strict towers.
Source: Stacks Tag 0940 (blueprint: lem-coef-tower-coaugmentation). -/
instance towerSectionsLimits : PreservesFiniteLimits (towerSections D l E) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- Levelwise exact sections preserve finite colimits of strict towers.
Source: Stacks Tag 0940 (blueprint: lem-coef-tower-coaugmentation). -/
instance towerSectionsColimits : PreservesFiniteColimits (towerSections D l E) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- Exact point sections on the strict tower derived category.
Source: Stacks Tags 0940 and 0946 (blueprint: lem-coef-tower-coaugmentation). -/
abbrev derivedTowerSections := (towerSections D l E).mapDerivedCategory

/-- Point sections commute with evaluation by their termwise identity comparison.
Source: Stacks Tag 0940 (blueprint: lem-coef-tower-coaugmentation). -/
def sectionsEvaluation (n : ℕ) :
    derivedTowerSections D l E ⋙ evaluate (coefficient l E) n ≅
      pbcTowerEvaluation (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) n ⋙
          (pointIntegralSections l E D.k).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (towerSections D l E)
    ((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefficient l E))).obj (op n))).symm ≪≫
      Functor.mapDerivedCategoryCompIso
        ((evaluation ℕᵒᵖ (scalarReductionSource l E (Spec (.of D.k)))).obj (op n))
        (pointIntegralSections l E D.k)

private theorem finiteScalar (n : ℕ) (a : coefficient l E) :
    (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of D.k)) n).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (pointIntegralSectionMap l E D.k a) =
      pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1))
        (pointReductionQuotient l E n a) := by
  let W := op (ProEt.mk (𝟙 (Spec (.of D.k))))
  have h := congrArg (fun f ↦ f.hom.app W
      (pointConstantSectionMap D.k (Padic.coefficientExtensionIntegers l E) a))
    (limit.lift_π (integralConstantCoefficientCone l E (Spec (.of D.k))) (op n))
  change _ = _ at h
  rw [show (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of D.k)) n).hom.app
      W (pointIntegralSectionMap l E D.k a) = _ from h]
  let f := CommRingCat.ofHom (pointReductionQuotient l E n)
  have hn := CategoryTheory.toSheafify_naturality
    (ProEt.topology (Spec (.of D.k))) ((Functor.const _).map f)
  have hv := congrArg (fun t ↦ (t.app W).hom a) hn
  exact hv.symm

/-- The scalar-restriction comparison is identity on every section, fixing its normalization.
Source: Stacks Tags 03DA and 0946 (blueprint: lem-coef-tower-coaugmentation).
Proof: the constant-to-completion map followed by its n-th projection is the
constant quotient map. Thus both scalar actions agree. Identity on sections is
linear, natural, and inverse to itself. Its underlying function determines each
component, proving uniqueness. -/
theorem finiteSectionsRestriction_existsUnique (n : ℕ) :
    ∃! e : scalarReductionRestriction l E (Spec (.of D.k)) n ⋙
        pointIntegralSections l E D.k ≅
      pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointReductionQuotient l E n),
      ∀ (M : scalarReductionTarget l E (Spec (.of D.k)) n)
        (x : M.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        (e.hom.app M).hom x = x := by
  let e : scalarReductionRestriction l E (Spec (.of D.k)) n ⋙
      pointIntegralSections l E D.k ≅
      pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        ModuleCat.restrictScalars (pointReductionQuotient l E n) :=
    NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
      (X₁ := (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙
        pointIntegralSections l E D.k).obj M)
      (X₂ := (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        ModuleCat.restrictScalars (pointReductionQuotient l E n)).obj M)
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a x ↦ by
          change ((completedIntegralCommRingProjectionUnrestricted l E
            (Spec (.of D.k)) n).hom.app (op (ProEt.mk (𝟙 (Spec (.of D.k))))))
              (pointIntegralSectionMap l E D.k a) •
                (show M.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k))))) from x) =
            pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1))
              (pointReductionQuotient l E n a) •
                (show M.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k))))) from x)
          rw [finiteScalar D l E n a] })
      (fun _ ↦ by ext x; rfl)
  refine ⟨e, ?_, ?_⟩
  · intro M x
    rfl
  · intro e' he
    apply Iso.ext
    ext M x
    exact he M x


/-- Identity on sections with the quotient and integral scalar actions identified.
Source: Stacks Tag 0946 (blueprint: lem-coef-tower-coaugmentation). -/
def finiteSectionsRestriction (n : ℕ) :=
  (finiteSectionsRestriction_existsUnique D l E n).exists.choose

/-- Additivity of scalar extension, with the fixed common module universe.
Source: Stacks Tag 06Y6 (blueprint: lem-coef-tower-coaugmentation). -/
instance quotientExtensionAdditive (n : ℕ) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointReductionQuotient l E n)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (pointReductionQuotient l E n)).left_adjoint_additive

/-- The same identity comparison on derived categories, using exact-functor factorization.
Source: Stacks Tag 0946 (blueprint: lem-coef-tower-coaugmentation). -/
def derivedFiniteSectionsRestriction (n : ℕ) :
    scalarReductionDerivedRestriction l E (Spec (.of D.k)) n ⋙
        (pointIntegralSections l E D.k).mapDerivedCategory ≅
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (pointReductionQuotient l E n)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (scalarReductionRestriction l E (Spec (.of D.k)) n)
    (pointIntegralSections l E D.k)).symm ≪≫
      @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
        (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙
          pointIntegralSections l E D.k)
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointReductionQuotient l E n))
        inferInstance (Functor.additive_of_iso (finiteSectionsRestriction D l E n))
        inferInstance inferInstance
        (preservesFiniteLimits_of_natIso (finiteSectionsRestriction D l E n))
        (preservesFiniteColimits_of_natIso (finiteSectionsRestriction D l E n))
        (finiteSectionsRestriction D l E n) ≪≫
        Functor.mapDerivedCategoryCompIso
          (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (pointReductionQuotient l E n))

/-- The mixed tensor by the quotient in degree zero is ordinary termwise scalar extension.
Source: Stacks Tag 06Y6 (blueprint: lem-coef-tower-coaugmentation). -/
def tensorSingleIso (n : ℕ)
    (P : CochainComplex (ModuleCat.{u + 1} (coefficient l E)) ℤ) :
    (((ModuleCat.mixedTensor (pointReductionQuotient l E n)).flip.map₂CochainComplex).obj P).obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ≅
      ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
         (pointReductionQuotient l E n)).mapHomologicalComplex
        (.up ℤ)).obj P :=
  CochainComplex.mapBifunctorSingle₂Iso
    (ModuleCat.mixedTensor.{u + 1} (pointReductionQuotient l E n)).flip
    (𝟙_ (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) P ≪≫
    (NatIso.mapHomologicalComplex
      (Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (pointReductionQuotient l E n))
        (MonoidalCategory.leftUnitorNatIso (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ≪≫
            Functor.rightUnitor _) (.up ℤ)).app P

/-- The existing derived tensor's universal comparison to ordinary scalar extension.
Source: Stacks Tag 06Y6 (blueprint: lem-coef-tower-coaugmentation). -/
def tensorCounit (n : ℕ)
    (P : CochainComplex (ModuleCat.{u + 1} (coefficient l E)) ℤ) :
    (pointReductionModuleTensor l E n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (pointReductionQuotient l E n)).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  ((DerivedCategory.exists_derivedTensor_second_factor_functor
    (pointReductionQuotient l E n)).2.choose_spec.choose _).app P ≫
      DerivedCategory.Q.map (tensorSingleIso l E n P).hom

private theorem moduleKFlatDerivability (R : Type r) [CommRing R] :
    (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)).localizerMorphismKFlat
      |>.IsLeftDerivabilityStructure := by
  have (M : ModuleCat.{r} R) : PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{r} R)).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight M))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{r} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{r} R)
      (AsSmall.equiv (C := ℤ)).symm
  infer_instance

private theorem leftDerivedCounitIso
    {C₀ C D H H' : Type*} [Category* C₀] [Category* C] [Category* D]
    [Category* H] [Category* H'] {V : MorphismProperty C₀} {W : MorphismProperty C}
    (Φ : LocalizerMorphism V W) [Φ.IsLeftDerivabilityStructure]
    (Q : C ⥤ D) [Q.IsLocalization W] (L : D ⥤ H) {F F' : C ⥤ H}
    (ε : Q ⋙ L ⟶ F) (e : F ≅ F')
    (hε : ∀ X : C₀, IsIso (ε.app (Φ.functor.obj X))) (G : H ⥤ H') :
    L.IsLeftDerivedFunctor (ε ≫ e.hom) W ∧
      (L ⋙ G).IsLeftDerivedFunctor
        ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight (ε ≫ e.hom) G) W := by
  have hi (X : C₀) : IsIso ((ε ≫ e.hom).app (Φ.functor.obj X)) := by
    have := hε X
    change IsIso (ε.app _ ≫ e.hom.app _)
    infer_instance
  exact ⟨Φ.isLeftDerivedFunctor_of_isLeftDerivabilityStructure _ hi,
    Φ.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure _ hi G⟩

private theorem normalizedDerivedAdjunction
    {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂] {F : C₁ ⥤ C₂} {U : C₂ ⥤ C₁}
    (a : F ⊣ U) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [Q₁.IsLocalization W₁] [Q₂.IsLocalization W₂]
    (L : D₁ ⥤ D₂) (UD : D₂ ⥤ D₁)
    (α : Q₁ ⋙ L ⟶ F ⋙ Q₂) (e : Q₂ ⋙ UD ≅ U ⋙ Q₁)
    [L.IsLeftDerivedFunctor α W₁]
    [(L ⋙ UD).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α UD) W₁] :
    ∃! adj : L ⊣ UD,
      ∀ P : C₁, adj.unit.app (Q₁.obj P) ≫ UD.map (α.app P) ≫
        e.hom.app (F.obj P) = Q₁.map (a.unit.app P) := by
  let β : U ⋙ Q₁ ⟶ Q₂ ⋙ UD := e.inv
  have : UD.IsRightDerivedFunctor β W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ UD e
  have : (UD ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight β L ≫ (Functor.associator _ _ _).hom) W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ (UD ⋙ L)
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e L)
  let adj : L ⊣ UD := a.derived W₁ W₂ α β
  have hnormalize (P : C₁) :
      adj.unit.app (Q₁.obj P) ≫ UD.map (α.app P) ≫ e.hom.app (F.obj P) =
        Q₁.map (a.unit.app P) := by
    have h := a.derivedη_fac_app W₁ α β P
    change adj.unit.app _ ≫ _ = _ at h
    rw [reassoc_of% h]
    dsimp only [β]
    rw [Iso.inv_hom_id_app]
    exact Category.comp_id _
  refine ⟨adj, hnormalize, ?_⟩
  intro adj' h'
  apply Adjunction.ext
  apply (L ⋙ UD).leftDerived_ext
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α UD) W₁
  ext P
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  simp only [Category.id_comp]
  apply (cancel_mono (e.hom.app (F.obj P))).mp
  simpa only [Category.assoc] using (h' P).trans (hnormalize P).symm

private instance moduleExtensionAdditive {R A : Type r} [CommRing R] [CommRing A]
    (f : R →+* A) : (ModuleCat.extendScalars.{r, r, r} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{r, r, r} f).left_adjoint_additive

private def moduleTensorSingleIso {R A : Type r} [CommRing R] [CommRing A]
    (f : R →+* A) :
    (ModuleCat.mixedTensor.{r} f).flip.map₂CochainComplex.flip.obj
        ((HomologicalComplex.single (ModuleCat.{r} A) (.up ℤ) 0).obj (𝟙_ _)) ≅
      (ModuleCat.extendScalars.{r, r, r} f).mapHomologicalComplex (.up ℤ) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (ModuleCat.mixedTensor.{r} f).flip (𝟙_ (ModuleCat.{r} A)) ≪≫
    NatIso.mapHomologicalComplex
      (Functor.isoWhiskerLeft (ModuleCat.extendScalars.{r, r, r} f)
        (leftUnitorNatIso (ModuleCat.{r} A)) ≪≫ Functor.rightUnitor _) (.up ℤ)

private theorem moduleTensorAdjunction {R A : Type r} [CommRing R] [CommRing A]
    [HasDerivedCategory (ModuleCat.{r} R)] [HasDerivedCategory (ModuleCat.{r} A)]
    (f : R →+* A)
    (L : DerivedCategory (ModuleCat.{r} R) ⥤ DerivedCategory (ModuleCat.{r} A))
    (ε : DerivedCategory.Q ⋙ L ⟶
      (ModuleCat.mixedTensor.{r} f).flip.map₂CochainComplex.flip.obj
        ((HomologicalComplex.single (ModuleCat.{r} A) (.up ℤ) 0).obj (𝟙_ _)) ⋙
          DerivedCategory.Q)
    (hε : ∀ P : CochainComplex (ModuleCat.{r} R) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P → IsIso (ε.app P)) :
    ∃! adj : L ⊣ (ModuleCat.restrictScalars.{r, r, r} f).mapDerivedCategory,
      ∀ P : CochainComplex (ModuleCat.{r} R) ℤ,
        adj.unit.app (DerivedCategory.Q.obj P) ≫
            (ModuleCat.restrictScalars.{r, r, r} f).mapDerivedCategory.map
              (ε.app P ≫ DerivedCategory.Q.map ((moduleTensorSingleIso f).hom.app P)) ≫
            (ModuleCat.restrictScalars.{r, r, r} f).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.extendScalars.{r, r, r} f).mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{r, r, r} f).mapHomologicalComplex
              (.up ℤ)).unit.app P) := by
  let U := ModuleCat.restrictScalars.{r, r, r} f
  let F := ModuleCat.extendScalars.{r, r, r} f
  let α := ε ≫ Functor.whiskerRight (moduleTensorSingleIso f).hom DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)
  let V := HomologicalComplex.quasiIso (ModuleCat.{r} A) (.up ℤ)
  have : W.localizerMorphismKFlat.IsLeftDerivabilityStructure := moduleKFlatDerivability R
  obtain ⟨hL, hLU⟩ := leftDerivedCounitIso W.localizerMorphismKFlat
    DerivedCategory.Q L ε (Functor.isoWhiskerRight (moduleTensorSingleIso f) DerivedCategory.Q)
    (fun P ↦ hε P.obj P.property) U.mapDerivedCategory
  have : L.IsLeftDerivedFunctor α W := hL
  have : (L ⋙ U.mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α U.mapDerivedCategory) W := hLU
  exact normalizedDerivedAdjunction
    ((ModuleCat.extendRestrictScalarsAdj.{r, r, r} f).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q W V L U.mapDerivedCategory α U.mapDerivedCategoryFactors

/-- The tensor/restriction adjunction, uniquely normalized by the ordinary tensor unit.
Source: Stacks Tags 07A6 and 0FND (blueprint: lem-coef-tower-coaugmentation).
Proof: mixed tensor with the regular quotient in degree zero is scalar extension.
Its universal left-derived comparison is tensorCounit. Restriction is exact.
Apply the derived-adjoint theorem to the ordinary extension/restriction adjunction.
The fraction formula identifies the unit after tensorCounit with the ordinary
unit x to 1 tensor x. K-flat resolutions make tensorCounit invertible, so this
normalization determines the unit on every derived object and hence the adjunction. -/
theorem reductionAdjunction_existsUnique (n : ℕ) :
    ∃! adj : pointReductionModuleTensor l E n ⊣
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (pointReductionQuotient l E n)).mapDerivedCategory,
      ∀ P : CochainComplex (ModuleCat.{u + 1} (coefficient l E)) ℤ,
        adj.unit.app (DerivedCategory.Q.obj P) ≫
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
              (pointReductionQuotient l E n)).mapDerivedCategory.map
              (tensorCounit l E n P) ≫
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
              (pointReductionQuotient l E n)).mapDerivedCategoryFactors.hom.app
                (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
                    (pointReductionQuotient l E n)).mapHomologicalComplex
                  (.up ℤ)).obj P) =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
                (pointReductionQuotient l E n)).unit
                (.up ℤ)).app P) := by
  exact moduleTensorAdjunction (pointReductionQuotient l E n)
    (pointReductionModuleTensor l E n)
    ((DerivedCategory.exists_derivedTensor_second_factor_functor
      (pointReductionQuotient l E n)).2.choose_spec.choose _)
    ((DerivedCategory.exists_derivedTensor_second_factor_functor
      (pointReductionQuotient l E n)).2.choose_spec.choose_spec.2.2.1 _)

/-- The canonical ordinary-module derived scalar adjunction with tensor-unit normalization.
Source: Stacks Tag 07A6 (blueprint: lem-coef-tower-coaugmentation). -/
def reductionAdjunction (n : ℕ) :=
  (reductionAdjunction_existsUnique l E n).exists.choose

/-- Evaluation of a derived constant tower, identified with its original object.
Source: Stacks Tag 0940 (blueprint: lem-coef-tower-coaugmentation). -/
def constantEvaluation (R : Type r) [CommRing R] [HasDerivedCategory (ModuleCat.{r} R)]
    (n : ℕ) : constant R ⋙ evaluate R n ≅ 𝟭 (DerivedCategory (ModuleCat.{r} R)) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The derived constant/limit counit evaluates to the actual total-limit projections.
Source: Stacks Tags 0941 and 0FND (blueprint: lem-coef-tower-coaugmentation).
Proof: on a K-injective tower I the universal right-derived unit identifies Rlim(QI)
with Q(lim I). The fraction formula for the derived adjunction sends its identity
to the ordinary counit, whose components are the projections of lim I. Exact
factorization of evaluation identifies these with the derived projection defined
above. Every tower admits such a resolution; naturality transports the equality. -/
theorem counit_projection (R : Type r) [CommRing R]
    [HasDerivedCategory (ModuleCat.{r} R)]
    (B : DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{r} R)) (n : ℕ) :
    (evaluate R n).map ((adjunction R).counit.app B) =
      (constantEvaluation R n).hom.app ((totalLimit R).obj B) ≫
        (projection R n).app B := by
  let t : totalLimit R ⟶ evaluate R n :=
    Functor.whiskerLeft (totalLimit R) (constantEvaluation R n).inv ≫
      Functor.whiskerRight (adjunction R).counit (evaluate R n)
  have ht : t = projection R n := by
    apply (totalLimit R).rightDerived_ext
      (lim : (ℕᵒᵖ ⥤ ModuleCat.{r} R) ⥤ ModuleCat.{r} R).rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso _ (.up ℤ))
    ext I
    dsimp only [t, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    have hn := (constantEvaluation R n).inv.naturality
      ((lim : (ℕᵒᵖ ⥤ ModuleCat.{r} R) ⥤ ModuleCat.{r} R).rightDerivedFunctorUnit.app I)
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    erw [← Category.assoc, hn, Category.assoc]
    rw [← Functor.map_comp]
    have hc := (constLimAdj :
        (Functor.const ℕᵒᵖ : ModuleCat.{r} R ⥤ _) ⊣ lim).mapHomotopyCategory (.up ℤ)
      |>.derivedε_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
        (Functor.const ℕᵒᵖ : ModuleCat.{r} R ⥤ _).mapDerivedCategoryFactorsh.hom
        (lim : (ℕᵒᵖ ⥤ ModuleCat.{r} R) ⥤ ModuleCat.{r} R).rightDerivedFunctorUnit I
    change _ = _ at hc
    erw [hc]
    dsimp only [projection, NatTrans.comp_app]
    rw [← Category.assoc]
    erw [Functor.rightDerivedNatTrans_app]
    rw [Category.assoc]
    have hp := NatTrans.congr_app
      (Functor.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
        ((evaluation ℕᵒᵖ (ModuleCat.{r} R)).obj (op n))) I
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hp
    erw [hp]
    rw [← cancel_mono
      (((evaluation ℕᵒᵖ (ModuleCat.{r} R)).obj (op n)).mapDerivedCategoryFactorsh.hom.app I)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    simp only [Functor.map_comp, Category.assoc]
    erw [((evaluation ℕᵒᵖ (ModuleCat.{r} R)).obj (op n)).mapDerivedCategoryFactorsh.hom.naturality]
    dsimp only [constantEvaluation, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
    simp only [Category.assoc]
    erw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh_assoc]
    change (Functor.mapDerivedCategoryIdIso (ModuleCat.{r} R)).inv.app _ ≫
      (𝟭 (ModuleCat.{r} R)).mapDerivedCategoryFactorsh.hom.app _ ≫ _ = _
    rw [← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj,
      Iso.inv_hom_id_app_assoc]
    obtain ⟨P, rfl⟩ := I.quotient_obj_surjective
    simp only [Functor.comp_map, Adjunction.mapHomotopyCategory_counit_app_quotient,
      Functor.mapHomotopyCategory_map, NatTrans.mapHomotopyCategory,
      Functor.whiskerRight_app]
    apply DerivedCategory.Qh.congr_map
    apply (HomotopyCategory.quotient _ _).congr_map
    ext i
    rfl
  have h := NatTrans.congr_app ht B
  dsimp only [t, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at h
  rw [← h, Iso.hom_inv_id_app_assoc]

variable {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)} (c : Compactification a)

/-- The input objects have integral constructibility and one fixed finite Tor interval.
The full subcategory retains every derived morphism between these objects.
Source: blueprint integral dualizing proof, paragraph 2
(blueprint: lem-coef-tower-coaugmentation). -/
def inputs (a₀ b₀ : ℤ) : ObjectProperty (DerivedCategory (scalarReductionSource l E X)) :=
  fun K ↦ sfIntegralConstructible l E X K ∧ ∀ n : ℕ,
    HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E X n).obj K) a₀ b₀

variable
  (T : DerivedCategory (scalarReductionSource l E X) ⥤
    DerivedCategory (pbcTowers (Spec (.of D.k))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))

/-- Total inverse limit of the specified strict compact-support reduction tower.
This is the strict-tower interpretation used in step 1 of this item's proof;
the original integral, rational and Qbar compact-support value definitions remain unchanged.
Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, compact-support reduction;
lem-coef-tower-coaugmentation, proof step 1
(blueprint: lem-coef-tower-coaugmentation). -/
def strictIntegralCompactSupport :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E (Spec (.of D.k))) :=
  T ⋙ completedRlim (Spec (.of D.k))
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))

/-- Integral compact-support sections C, from total limit of the specified strict tower.
Source: blueprint integral dualizing proof, paragraph 2
(blueprint: lem-coef-tower-coaugmentation). -/
abbrev integralSections :=
  strictIntegralCompactSupport D l E T ⋙
    (pointIntegralSections l E D.k).mapDerivedCategory

/-- The ordinary-module strict derived tower B, with no limit in its sections operation.
Source: Stacks Tag 0940 (blueprint: lem-coef-tower-coaugmentation). -/
abbrev sectionsTower := T ⋙ derivedTowerSections D l E

/-- The finite compact-support sections C_n before forgetting quotient scalars.
Source: blueprint integral dualizing proof, paragraph 2
(blueprint: lem-coef-tower-coaugmentation). -/
abbrev finiteSections (n : ℕ) :=
  scalarReductionDerivedExtension l E X n ⋙
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory

variable
  (e : ∀ n : ℕ, T ⋙ pbcTowerEvaluation (Spec (.of D.k))
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) n ≅
      compactSupportRestrictedLevel l E c n)

/-- The natural identification ev_n B = Res C_n, induced by the supplied tower
comparison and the identity on sections with their restricted scalar actions.
Source: Stacks Tags 0940 and 0946 (blueprint: lem-coef-tower-coaugmentation). -/
def finiteEvaluation (n : ℕ) :
    sectionsTower D l E T ⋙ evaluate (coefficient l E) n ≅
      finiteSections D l E c n ⋙
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (pointReductionQuotient l E n)).mapDerivedCategory :=
  Functor.isoWhiskerLeft T (sectionsEvaluation D l E n) ≪≫
    Functor.isoWhiskerRight (e n) (pointIntegralSections l E D.k).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft
        (scalarReductionDerivedExtension l E X n ⋙
          sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
        (derivedFiniteSectionsRestriction D l E n)

/-- The actual compact-support projection: apply sections to the total-limit
projection, then the finite-level identification. No cone-completion map is chosen.
Source: blueprint integral dualizing proof, paragraph 2
(blueprint: lem-coef-tower-coaugmentation). -/
def compactSupportProjection (n : ℕ) :
    integralSections D l E T ⟶ finiteSections D l E c n ⋙
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (pointReductionQuotient l E n)).mapDerivedCategory :=
  Functor.whiskerRight
    (Functor.whiskerLeft T
      (completedRlimProjection (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) n) ≫ (e n).hom)
    (pointIntegralSections l E D.k).mapDerivedCategory ≫
      (Functor.isoWhiskerLeft
        (scalarReductionDerivedExtension l E X n ⋙
          sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
        (derivedFiniteSectionsRestriction D l E n)).hom

/-- The canonical finite reduction comparison is the scalar-extension adjunct of
that very compact-support projection, with the normalized tensor-unit adjunction.
Source: blueprint integral dualizing proof, paragraph 2, third comparison
(blueprint: lem-coef-tower-coaugmentation). -/
def reductionComparison (n : ℕ) (K : DerivedCategory (scalarReductionSource l E X)) :
    (pointReductionModuleTensor l E n).obj ((integralSections D l E T).obj K) ⟶
      (finiteSections D l E c n).obj K :=
  ((reductionAdjunction l E n).homEquiv _ _).symm
    ((compactSupportProjection D l E c T e n).app K)

/-- The coaugmentation is constant(lambda) followed by the derived counit, as a
natural transformation in the derived category of strict module towers itself.
Source: Stacks Tags 0940 and 09T5 (blueprint: lem-coef-tower-coaugmentation). -/
def coaugmentation (a₀ b₀ : ℤ)
    (lambda : (inputs l E (X := X) a₀ b₀).ι ⋙ integralSections D l E T ≅
      (inputs l E (X := X) a₀ b₀).ι ⋙ sectionsTower D l E T ⋙ totalLimit (coefficient l E)) :
    (inputs l E (X := X) a₀ b₀).ι ⋙ integralSections D l E T ⋙ constant (coefficient l E) ⟶
      (inputs l E (X := X) a₀ b₀).ι ⋙ sectionsTower D l E T :=
  Functor.whiskerRight lambda.hom (constant (coefficient l E)) ≫
    Functor.whiskerLeft ((inputs l E (X := X) a₀ b₀).ι ⋙ sectionsTower D l E T)
      (adjunction (coefficient l E)).counit

/-- Compact-support sections are the total limit of their strict section tower.
The counit coaugmentation has the actual finite projections, and their scalar
adjuncts are the canonical finite-reduction isomorphisms. Naturality is in the
full input category, hence includes every morphism of the given integral objects.

`T,e,htransition` are the specified strict compact-support tower and its evaluation
identifications from exists_compactSupportReductionTower. They are parameters
identifying that construction, not extra assumptions on K or a. The completed
coefficient sheaf and small pro-etale site are unchanged. The exceptional functors
and omega_n in the node fix notation only; neither occurs in its conclusion.

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, third displayed
comparison; Stacks Tags 0940, 0941, 09T5, 0FND, 06YS and 07A6
(blueprint: lem-coef-tower-coaugmentation).

Proof, following all ten DAG steps:
1. The strict compact-support tower evaluates naturally to restricted F_n K_n,
with all quotient transitions. Its total limit is the integral compact-support
functor and its actual projections are those used in compactSupportProjection
(lem-weil-compact-support-reduction-tower-functor and the compact-support definition).
2. Point sections followed by integral scalar restriction are exact, as is their
levelwise tower functor. Exact-functor derived factorization identifies B with the
separately derived tower sections, without taking an inverse limit (exact point
sections, levelwise tower abelianness, and def-pc-sheaf-restrict-scalars).
3. Countable products are sectionwise on the pro-etale site and exact there and in
ordinary modules. Point sections preserve their actual projections. Apply
lem-cbc-exact-product-functor-strict-limit to obtain lambda with its projection
equations, naturally on every derived strict tower.
4. The ordinary correspondence from maps into lim to compatible projection maps
gives constLimAdj. Constant towers are exact, so derive this adjunction using
lem-pc-derived-adjoint-functors and the total-limit theorem.
5. The fraction normalization of lem-pc-pre-derived-adjoint-functors-general on a
K-injective tower identifies the derived counit with its ordinary projection cone.
Thus coaugmentation, defined as constant(lambda) followed by this counit, evaluates
to exactly compactSupportProjection, by step 3.
6. Naturality of lambda and of the counit gives naturality of coaugmentation in
the derived tower category. No equality is inferred from equality of evaluations.
7. lem-coef-integral-compact-support applies to the given dimension and common Tor
bounds. Its canonical sheaf reduction comparison is invertible. Composing its
sections with lem-pod-point-sections-derived-reduction gives the finite isomorphism.
8. The DVR quotient has the two-term finite-free resolution R --varpi^(n+1)--> R.
Completed constant-sheaf reduction identifies its sheaf version with (A_n)_s.
On a flat-term K-flat representative P, the point comparison is the universal
derived-tensor counit followed by the section quotient map Gamma(P)/t to Gamma(P/t)
(standard perfect quotients, completed reduction and resolution independence).
9. Take a flat-term K-flat module resolution Q to Gamma(P). Counit naturality
represents the comparison by x-bar to q(x) mod t. Its adjunct is x to q(x) mod t,
which is sections of the sheaf reduction unit. This uses no K-flatness of Gamma(P)
(lem-pc-kflat-resolution and the normalized derived coefficient adjunction).
10. Compose with sections of the canonical compact-support sheaf comparison. Its
adjunct is the actual compact-support projection, hence is precisely
reductionComparison. Step 7 makes it an isomorphism, identifying the specified
canonical maps from both cited finite-reduction theorems. -/
theorem compactSupport_tower_coaugmentation
    (_hl : l ≠ D.p)
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a₀ b₀ : ℤ) (_hab : a₀ ≤ b₀)
    (_htransition : ∀ (m n : ℕ) (h : n ≤ m)
      (K : DerivedCategory (scalarReductionSource l E X)),
      (pbcTowerTransition (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) m n h).app
          (T.obj K) ≫ (e n).hom.app K =
        (e m).hom.app K ≫ compactSupportRestrictedTransition l E c m n h K) :
    ∃ lambda : (inputs l E (X := X) a₀ b₀).ι ⋙ integralSections D l E T ≅
        (inputs l E (X := X) a₀ b₀).ι ⋙ sectionsTower D l E T ⋙ totalLimit (coefficient l E),
      (∀ (K : (inputs l E (X := X) a₀ b₀).FullSubcategory) (n : ℕ),
        lambda.hom.app K ≫ (projection (coefficient l E) n).app
            ((sectionsTower D l E T).obj K.obj) ≫
            (finiteEvaluation D l E c T e n).hom.app K.obj =
          (compactSupportProjection D l E c T e n).app K.obj) ∧
      (∀ (K : (inputs l E (X := X) a₀ b₀).FullSubcategory) (n : ℕ),
        (evaluate (coefficient l E) n).map ((coaugmentation D l E T a₀ b₀ lambda).app K) ≫
            (finiteEvaluation D l E c T e n).hom.app K.obj =
          (constantEvaluation (coefficient l E) n).hom.app
            ((integralSections D l E T).obj K.obj) ≫
              (compactSupportProjection D l E c T e n).app K.obj) ∧
      ∀ (K : (inputs l E (X := X) a₀ b₀).FullSubcategory) (n : ℕ),
        IsIso (reductionComparison D l E c T e n K.obj) := by
  sorry

end WeilConjectures.CoefTower
