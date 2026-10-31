/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.AlgebraicGeometry.StrictTower.DiagonalNormalization.ConstantTowerNormalizationData
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization
import all WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

/-! # Derived semilinear evaluation through the constant diagonal

Source: Stacks Project, Tags 07A7 and 03DI; the evaluation factorization in
`SemilinearProperOpenMatePasting`, lines 2112–2444.
(blueprint: lem-sf-semilinear-evaluation-derived-adjunction)

The comparisons below retain the specified adjunctions. They are transformations on
whole unbounded derived categories, with arbitrary coefficient transition maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Avoid repeating the dependent localization conversions during tactic linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf


private theorem mate_pasted
    {A B D F H I : Type*} [Category A] [Category B] [Category D]
    [Category F] [Category H] [Category I]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {L₃ : H ⥤ I} {R₃ : I ⥤ H}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {T₁ : A ⥤ D} {B₁ : B ⥤ F} {T₂ : D ⥤ H} {B₂ : F ⥤ I}
    {T : A ⥤ H} {S : B ⥤ I}
    (w₁ : TwoSquare T₁ L₁ L₂ B₁) (w₂ : TwoSquare T₂ L₂ L₃ B₂)
    (w : TwoSquare T L₁ L₃ S) (a : T ≅ T₁ ⋙ T₂) (b : S ≅ B₁ ⋙ B₂)
    (h : ∀ X, w.app X ≫ b.hom.app (L₁.obj X) =
      L₃.map (a.hom.app X) ≫ (w₁.hComp w₂).app X) (M : B) :
    (mateEquiv a₁ a₃ w).app M ≫ R₃.map (b.hom.app M) =
      a.hom.app (R₁.obj M) ≫
        T₂.map ((mateEquiv a₁ a₂ w₁).app M) ≫
        (mateEquiv a₂ a₃ w₂).app (B₁.obj M) := by
  have hw : w = ((w₁.hComp w₂).whiskerTop a.hom).whiskerBottom b.inv := by
    ext X
    apply (cancel_mono (b.hom.app (L₁.obj X))).mp
    simpa [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, Category.assoc] using h X
  rw [hw, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp a₁ a₂ a₃]
  dsimp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc, ← R₃.map_comp, b.inv_hom_id_app,
    R₃.map_id, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  erw [Category.comp_id]

private theorem inverse_mate_pasted
    {A B D F H I : Type*} [Category A] [Category B] [Category D]
    [Category F] [Category H] [Category I]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {L₃ : H ⥤ I} {R₃ : I ⥤ H}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {T₁ : A ⥤ D} {B₁ : B ⥤ F} {T₂ : D ⥤ H} {B₂ : F ⥤ I}
    {T : A ⥤ H} {S : B ⥤ I}
    (w₁ : TwoSquare R₁ B₁ T₁ R₂) (w₂ : TwoSquare R₂ B₂ T₂ R₃)
    (w : TwoSquare R₁ S T R₃) (a : T ≅ T₁ ⋙ T₂) (b : S ≅ B₁ ⋙ B₂)
    (h : ∀ X, w.app X ≫ R₃.map (b.hom.app X) =
      a.hom.app (R₁.obj X) ≫ (w₁.vComp w₂).app X) (M : A) :
    ((mateEquiv a₁ a₃).symm w).app M ≫ b.hom.app (L₁.obj M) =
      L₃.map (a.hom.app M) ≫
        ((mateEquiv a₂ a₃).symm w₂).app (T₁.obj M) ≫
        B₂.map (((mateEquiv a₁ a₂).symm w₁).app M) := by
  let v := ((mateEquiv a₁ a₂).symm w₁).hComp ((mateEquiv a₂ a₃).symm w₂)
  have hv : mateEquiv a₁ a₃ v = w₁.vComp w₂ := by
    dsimp only [v]
    rw [mateEquiv_vcomp a₁ a₂ a₃, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hw : mateEquiv a₁ a₃ ((v.whiskerTop a.hom).whiskerBottom b.inv) = w := by
    rw [mateEquiv_whiskerTop_whiskerBottom, hv]
    ext X
    apply (cancel_mono (R₃.map (b.hom.app X))).mp
    simpa [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, Category.assoc,
      ← R₃.map_comp] using (h X).symm
  rw [← hw, Equiv.symm_apply_apply]
  dsimp only [v, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.assoc, Category.id_comp, Category.comp_id, b.inv_hom_id_app]
  erw [Category.comp_id]

private theorem constant_square_factor
    {A B D F : Type*} [Category A] [Category B] [Category D] [Category F]
    (L : A ⥤ B) (E₀ : A ⥤ D) (E₁ : B ⥤ F) (G : D ⥤ F)
    (s : (E₀ ⋙ Functor.const ℕᵒᵖ) ⋙ (Functor.whiskeringRight ℕᵒᵖ D F).obj G ≅
      L ⋙ (E₁ ⋙ Functor.const ℕᵒᵖ)) (M : A) :
    ((Functor.whiskeringRight ℕᵒᵖ D F).obj G).map
        ((Iso.refl (E₀ ⋙ Functor.const ℕᵒᵖ)).hom.app M) ≫
      (Functor.compConstIso ℕᵒᵖ G).inv.app (E₀.obj M) ≫
      (Functor.const ℕᵒᵖ).map
        ((Functor.isoWhiskerRight s ((evaluation ℕᵒᵖ F).obj (op 0))).hom.app M) =
    s.hom.app M ≫ (Iso.refl (E₁ ⋙ Functor.const ℕᵒᵖ)).hom.app (L.obj M) := by
  apply NatTrans.ext
  funext m
  change G.map (𝟙 _) ≫ 𝟙 _ ≫ (s.hom.app M).app (op 0) =
    (s.hom.app M).app m ≫ 𝟙 _
  have h := (s.hom.app M).naturality (homOfLE (Nat.zero_le m.unop)).op
  change G.map (𝟙 _) ≫ (s.hom.app M).app (op 0) =
    (s.hom.app M).app m ≫ 𝟙 _ at h
  simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using h


private theorem exact_adjunction_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory = exactLocalizationDerivedAdjunction a := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  let K' := (HomotopyCategory.quotient A (.up ℤ)).obj K
  have hs : (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc]
    rw [← R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso A (.up ℤ))
      L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit K'
    change a.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Q.obj K) ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K') = _ at hu
    erw [reassoc_of% hu]
    have hf := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((L.mapHomotopyCategory (.up ℤ)).obj K')
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [reassoc_of% hf, Iso.inv_hom_id_app, Category.comp_id]
  have he : (exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    rw [CategoryTheory.exact_unit_app]
    have hl := StrictTower.ConstantNormalization.factorsh_hom L K
    have hr := StrictTower.ConstantNormalization.factorsh_hom R
      ((L.mapHomologicalComplex (.up ℤ)).obj K)
    change L.mapDerivedCategoryFactorsh.hom.app K' = _ at hl
    change R.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj K') = _ at hr
    rw [hl, hr]
    simp only [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id_app]
    erw [R.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
      Category.comp_id]
    change DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj K))
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    rfl
  exact (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
    R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K'))).mp
    (by simpa only [Category.assoc] using hs.trans he.symm)

end

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- The canonical exact-composition identification of evaluation followed by the diagonal.
Source: Stacks 07A7; exact localization of the evaluation/diagonal composite.
(blueprint: lem-sf-semilinear-evaluation-derived-adjunction) -/
def evaluationDiagonal (n : ℕ) (X : Scheme.{u}) :
    E C τ n X ≅ VaryingRing.ev C τ X n ⋙ StrictTower.DiagonalNormalization.delta (C n) X :=
  Functor.mapDerivedCategoryCompIso (VaryingRing.eval C τ X n) (Functor.const ℕᵒᵖ)

/-- The ordinary single-level pullback square, recovered at index zero from the
specified ordinary tower mate. Its section and unit normalization are retained.
Source: Stacks 07A7; ordinary evaluation normalization.
(blueprint: lem-sf-semilinear-evaluation-derived-adjunction) -/
def evaluationLevelPullOrdinary {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pull C τ f ⋙ VaryingRing.eval C τ X n ≅
      VaryingRing.eval C τ Y n ⋙ StrictTower.modulePullback (C n) f :=
  Functor.isoWhiskerRight
    (@asIso _ _ _ _ (evalPullInv C τ n f) (evalPullInv_isIso C τ n f)).symm
    ((CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules (C n) X)).obj (op 0))

/-- The single-level inverse-image square after exact localization.
Source: Stacks 07A7, with the ordinary unit normalization retained.
(blueprint: lem-sf-semilinear-evaluation-derived-adjunction) -/
def evaluationLevelPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    P C τ f ⋙ VaryingRing.ev C τ X n ≅
      VaryingRing.ev C τ Y n ⋙ (StrictTower.modulePullback (C n) f).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (evaluationLevelPullOrdinary C τ f n)

/-- The actual single-level direct-image mate, for the specified system adjunction.
Source: Stacks 07A7, remark-base-change.
(blueprint: lem-sf-semilinear-evaluation-derived-adjunction) -/
def evaluationLevelDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    R C τ f ⋙ VaryingRing.ev C τ Y n ⟶
      VaryingRing.ev C τ X n ⋙ StrictTower.DiagonalNormalization.push (C n) f :=
  mateEquiv (adj C τ f) (VaryingRing.levelAdj C f n)
    (evaluationLevelPull C τ f n).inv

/-- The diagonal direct-image mate for the specified single-level and tower adjunctions.
Source: Stacks 07A7, remark-base-change; the constant-diagonal square.
(blueprint: lem-sf-semilinear-evaluation-derived-adjunction) -/
def evaluationDiagonalDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    StrictTower.DiagonalNormalization.push (C n) f ⋙
        StrictTower.DiagonalNormalization.delta (C n) Y ⟶
      StrictTower.DiagonalNormalization.delta (C n) X ⋙ StrictTower.R (C n) f :=
  mateEquiv (VaryingRing.levelAdj C f n) (StrictTower.adj (C n) f)
    (StrictTower.DiagonalNormalization.deltaPull (C n) f).hom

/-- The single-level inverse open mate, with the specified system open adjunction.
Source: Stacks 03DI, lemma-extension-by-zero, and exact localization.
(blueprint: lem-sf-semilinear-evaluation-derived-adjunction) -/
def evaluationLevelOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    VaryingRing.ev C τ U n ⋙ (StrictTower.moduleJ (C n) j).mapDerivedCategory ⟶
      J C τ j ⋙ VaryingRing.ev C τ X n :=
  (mateEquiv (jAdj C τ j) (VaryingRing.levelJAdj C j n)).symm
    (evaluationLevelPull C τ j n).hom

/-- The diagonal inverse open mate for the specified localized open adjunctions.
Source: Stacks 03DI; the diagonal restriction square has identity components.
(blueprint: lem-sf-semilinear-evaluation-derived-adjunction) -/
def evaluationDiagonalOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    StrictTower.DiagonalNormalization.delta (C n) U ⋙ StrictTower.J (C n) j ⟶
      (StrictTower.moduleJ (C n) j).mapDerivedCategory ⋙
        StrictTower.DiagonalNormalization.delta (C n) X :=
  (mateEquiv (VaryingRing.levelJAdj C j n) (StrictTower.jAdj (C n) j)).symm
    (StrictTower.DiagonalNormalization.deltaPull (C n) j).inv

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
  evalPullInv

private theorem evaluation_pull_pasting {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Derived C τ Y) :
    (evalP C τ n f).inv.app M ≫
        (evaluationDiagonal C τ n X).hom.app ((P C τ f).obj M) =
      (StrictTower.G (C n) f).map ((evaluationDiagonal C τ n Y).hom.app M) ≫
        (StrictTower.DiagonalNormalization.deltaPull (C n) f).hom.app
          ((VaryingRing.ev C τ Y n).obj M) ≫
        (StrictTower.DiagonalNormalization.delta (C n) X).map
          ((evaluationLevelPull C τ f n).inv.app M) := by
  have : (pull C τ f).Additive := pull_additive C τ f
  have : PreservesFiniteLimits (pull C τ f) := pull_limits C τ f
  have : PreservesFiniteColimits (pull C τ f) := pull_colimits C τ f
  let s := @asIso _ _ _ _ (evalPullInv C τ n f) (evalPullInv_isIso C τ n f)
  have hp : (evalP C τ n f).inv = (Functor.mapDerivedCategorySquareIso s).hom := by
    simp only [evalP, s, Functor.mapDerivedCategorySquareIso, Iso.trans_inv,
      Iso.symm_inv, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rfl
  rw [hp]
  let q := (Functor.compConstIso ℕᵒᵖ (StrictTower.modulePullback (C n) f)).symm
  have hq := constant_square_factor (pull C τ f)
    (VaryingRing.eval C τ Y n) (VaryingRing.eval C τ X n)
    (StrictTower.modulePullback (C n) f) s
  let e : VaryingRing.eval C τ Y n ⋙ StrictTower.modulePullback (C n) f ≅
      pull C τ f ⋙ VaryingRing.eval C τ X n := Functor.isoWhiskerRight s
    ((CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules (C n) X)).obj (op 0))
  have hc := Functor.exactSquare_comp_forward
    (VaryingRing.eval C τ Y n) (Functor.const ℕᵒᵖ)
      (VaryingRing.eval C τ Y n ⋙ Functor.const ℕᵒᵖ)
    (VaryingRing.eval C τ X n) (Functor.const ℕᵒᵖ)
      (VaryingRing.eval C τ X n ⋙ Functor.const ℕᵒᵖ)
    (pull C τ f) (StrictTower.modulePullback (C n) f)
    (StrictTower.towerPullback (C n) f)
    e q s (Iso.refl _) (Iso.refl _) hq M
  have he : evaluationLevelPullOrdinary C τ f n = e.symm := by
    exact (Functor.isoWhiskerRight_symm s _).symm
  have heD : (evaluationLevelPull C τ f n).inv =
      (Functor.mapDerivedCategorySquareIso e).hom := by
    unfold evaluationLevelPull
    rw [he]
    exact (Functor.square_symm_hom e.symm).symm
  rw [heD]
  simp only [evaluationDiagonal, E, levelTower, VaryingRing.eval,
    StrictTower.DiagonalNormalization.deltaPull, StrictTower.ConstantNormalization.deltaPull,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Functor.mapDerivedCategoryNatIso_refl, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.id_comp, P, VaryingRing.ev, StrictTower.G,
    StrictTower.DiagonalNormalization.delta, StrictTower.ConstantNormalization.delta,
    s, q, Category.assoc] at hc ⊢
  exact hc.symm

private theorem evaluation_pull_pasting_forward {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Derived C τ Y) :
    (evalP C τ n f).hom.app M ≫
        (StrictTower.G (C n) f).map ((evaluationDiagonal C τ n Y).hom.app M) =
      (evaluationDiagonal C τ n X).hom.app ((P C τ f).obj M) ≫
        (StrictTower.DiagonalNormalization.delta (C n) X).map
          ((evaluationLevelPull C τ f n).hom.app M) ≫
        (StrictTower.DiagonalNormalization.deltaPull (C n) f).inv.app
          ((VaryingRing.ev C τ Y n).obj M) := by
  have h := evaluation_pull_pasting C τ f n M
  have hh := congrArg (fun t ↦ (evalP C τ n f).hom.app M ≫ t ≫
    (StrictTower.DiagonalNormalization.delta (C n) X).map
      ((evaluationLevelPull C τ f n).hom.app M) ≫
    (StrictTower.DiagonalNormalization.deltaPull (C n) f).inv.app
      ((VaryingRing.ev C τ Y n).obj M)) h
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app] at hh
  erw [(StrictTower.DiagonalNormalization.delta (C n) X).map_id,
    Category.id_comp] at hh
  erw [Iso.hom_inv_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

private theorem evaluation_diagonal_open {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) :
    evaluationDiagonalOpen C j n =
      (Functor.mapDerivedCategoryCompIso
        (Functor.const ℕᵒᵖ : StrictTower.Modules (C n) U ⥤ StrictTower.Towers (C n) U)
        (StrictTower.towerJ (C n) j)).inv ≫
      (Functor.mapDerivedCategoryNatIso
        (Functor.compConstIso ℕᵒᵖ (StrictTower.moduleJ (C n) j))).inv ≫
      (Functor.mapDerivedCategoryCompIso (StrictTower.moduleJ (C n) j)
        (Functor.const ℕᵒᵖ)).hom := by
  let a := StrictTower.moduleJAdj (C n) j
  let d := Functor.compConstIso ℕᵒᵖ (StrictTower.modulePullback (C n) j)
  let e := (Functor.compConstIso ℕᵒᵖ (StrictTower.moduleJ (C n) j)).symm
  have hm : ((mateEquiv a (a.whiskerRight ℕᵒᵖ)).symm
      (TwoSquare.mk _ _ _ _ d.hom)).natTrans = e.hom := by
    apply congrArg TwoSquare.natTrans
    apply (mateEquiv a (a.whiskerRight ℕᵒᵖ)).injective
    rw [Equiv.apply_symm_apply]
    exact (StrictTower.ConstantNormalization.const_mate _ _ a).symm
  have : IsIso ((mateEquiv a (a.whiskerRight ℕᵒᵖ)).symm
      (TwoSquare.mk _ _ _ _ d.hom)).natTrans := by
    rw [hm]
    infer_instance
  have hl := (exact_localization_inverse_mate a (a.whiskerRight ℕᵒᵖ) d).2.1
  have hb : asIso ((mateEquiv a (a.whiskerRight ℕᵒᵖ)).symm
      (TwoSquare.mk _ _ _ _ d.hom)).natTrans = e := Iso.ext hm
  rw [hb] at hl
  have ha : VaryingRing.levelJAdj C j n = exactLocalizationDerivedAdjunction a :=
    exact_adjunction_eq a
  have hat : StrictTower.jAdj (C n) j =
      exactLocalizationDerivedAdjunction (a.whiskerRight ℕᵒᵖ) :=
    exact_adjunction_eq (a.whiskerRight ℕᵒᵖ)
  unfold evaluationDiagonalOpen
  rw [ha, hat]
  have hd : (StrictTower.DiagonalNormalization.deltaPull (C n) j).inv =
      (Functor.mapDerivedCategorySquareIso d).hom := by
    exact (Functor.square_symm_hom d.symm).symm
  rw [hd]
  change ((mateEquiv (exactLocalizationDerivedAdjunction a)
    (exactLocalizationDerivedAdjunction (a.whiskerRight ℕᵒᵖ))).symm
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)).natTrans = _
  rw [hl]
  simp only [e, Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_symm]

/-- Evaluation factors through the normalized constant diagonal, and both specified
adjunction mates are invertible on the whole unbounded derived category.
Source: Stacks 07A7 (remark-base-change) and 03DI (lemma-extension-by-zero);
SemilinearProperOpenMatePasting, lines 2112–2444.
(blueprint: lem-sf-semilinear-evaluation-derived-adjunction)

Proof: (1) The ordinary evaluation-adjunction lemma identifies the inverse pullback mate
with the constant lift of the single-level square, including its units and counits.
The identity-component diagonal comparison gives its two-factor form.
(2) Evaluation, diagonal and inverse images are exact. Apply
lem-pod-derived-exact-square-composition to localize that equality, using the standard
exact-composition identifications. Inverting gives precisely evalP.
(3) lem-coef-semilinear-derived-sections, specialized to constant coefficient sheaves,
gives the single-level direct-image isomorphism. Its counit equation identifies it with
evaluationLevelDirect by the mate bijection, with the ordinary unit normalization retained.
(4) lem-weil-pbc-constant-tower-pushforward-normalization gives chi; its strict counit
equation identifies chi as the right mate of the diagonal inverse-image square.
(5) lem-weil-pbc-mate-pasting identifies evalR with the paste of these two mates, hence
it is invertible and has the displayed factorization before any evaluation of morphisms.
(6) For an open, extension by zero is the sheafification of the direct sum over lifts
into the open. Evaluation retains every summand, and its unit transpose is the ordinary
evaluation square. For the diagonal, the mate at each tower component is the triangle
identity, so it is compConstIso of ordinary extension by zero, inverted.
(7) lem-sf-exact-localization-inverse-mate localizes these ordinary inverse open mates
with their specified adjunctions. Reverse mate pasting gives evalJInv and its stated
factorization. Exact localization of compConstIso gives the last equation. All arguments
precede tower evaluation and require neither flat transitions nor bounded complexes. -/
theorem semilinearEvaluationDerivedAdjunction (n : ℕ) :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IsIso (evalR C τ n f) ∧
      evaluationDiagonalDirect C f n =
        (StrictTower.DiagonalNormalization.chi (C n) f).hom ∧
      ∀ M : Derived C τ X,
        (evalR C τ n f).app M ≫
            (StrictTower.R (C n) f).map ((evaluationDiagonal C τ n X).hom.app M) =
          (evaluationDiagonal C τ n Y).hom.app ((R C τ f).obj M) ≫
            (StrictTower.DiagonalNormalization.delta (C n) Y).map
              ((evaluationLevelDirect C τ f n).app M) ≫
            (StrictTower.DiagonalNormalization.chi (C n) f).hom.app
              ((VaryingRing.ev C τ X n).obj M)) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
      IsIso (evalJInv C τ n j) ∧
      (∀ M : Derived C τ U,
        (evalJInv C τ n j).app M ≫
            (evaluationDiagonal C τ n X).hom.app ((J C τ j).obj M) =
          (StrictTower.J (C n) j).map ((evaluationDiagonal C τ n U).hom.app M) ≫
            (evaluationDiagonalOpen C j n).app ((VaryingRing.ev C τ U n).obj M) ≫
            (StrictTower.DiagonalNormalization.delta (C n) X).map
              ((evaluationLevelOpen C τ j n).app M)) ∧
      evaluationDiagonalOpen C j n =
        (Functor.mapDerivedCategoryCompIso
          (Functor.const ℕᵒᵖ : StrictTower.Modules (C n) U ⥤ StrictTower.Towers (C n) U)
          (StrictTower.towerJ (C n) j)).inv ≫
        (Functor.mapDerivedCategoryNatIso
          (Functor.compConstIso ℕᵒᵖ (StrictTower.moduleJ (C n) j))).inv ≫
        (Functor.mapDerivedCategoryCompIso (StrictTower.moduleJ (C n) j)
          (Functor.const ℕᵒᵖ)).hom) := by
  constructor
  · intro X Y f
    refine ⟨evalR_isIso C τ n f, ?_, ?_⟩
    · exact (StrictTower.ConstantNormalization.chi_mate (C n) f).symm
    · intro M
      have hd : evaluationDiagonalDirect C f n =
          (StrictTower.DiagonalNormalization.chi (C n) f).hom :=
        (StrictTower.ConstantNormalization.chi_mate (C n) f).symm
      rw [← hd]
      exact mate_pasted (adj C τ f) (VaryingRing.levelAdj C f n)
        (StrictTower.adj (C n) f)
        (TwoSquare.mk _ _ _ _ (evaluationLevelPull C τ f n).inv)
        (TwoSquare.mk _ _ _ _
          (StrictTower.DiagonalNormalization.deltaPull (C n) f).hom)
        (TwoSquare.mk _ _ _ _ (evalP C τ n f).inv)
        (evaluationDiagonal C τ n Y) (evaluationDiagonal C τ n X)
        (by
          intro N
          simpa [TwoSquare.hComp, Category.assoc] using evaluation_pull_pasting C τ f n N) M
  · intro U X j hj
    refine ⟨evalJInv_isIso C τ n j, ?_, ?_⟩
    · intro M
      exact inverse_mate_pasted (jAdj C τ j) (VaryingRing.levelJAdj C j n)
        (StrictTower.jAdj (C n) j)
        (TwoSquare.mk _ _ _ _ (evaluationLevelPull C τ j n).hom)
        (TwoSquare.mk _ _ _ _
          (StrictTower.DiagonalNormalization.deltaPull (C n) j).inv)
        (TwoSquare.mk _ _ _ _ (evalP C τ n j).hom)
        (evaluationDiagonal C τ n U) (evaluationDiagonal C τ n X)
        (by
          intro N
          simpa [TwoSquare.vComp, Category.assoc] using
            evaluation_pull_pasting_forward C τ j n N) M
    · exact evaluation_diagonal_open C j n

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
