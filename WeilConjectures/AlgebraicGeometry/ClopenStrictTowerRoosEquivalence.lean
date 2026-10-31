/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenStrictTowerRoosCore
public import WeilConjectures.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.PUnit
import all WeilConjectures.AlgebraicGeometry.ClopenStrictTowerRoosCore
import all WeilConjectures.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus
import all WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherenceSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import all Mathlib.CategoryTheory.Sites.CompatibleSheafification
import all Mathlib.CategoryTheory.Limits.Types.Products
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Strict towers and the signed Roos comparison on a clopen partition

Source: Stacks Project, Tags 04TS, 07KC and 08TC, finite-clopen application
(blueprint: lem-pur-clopen-strict-tower-roos-equivalence).

The statements below jointly record the tower equivalence, its section coordinates,
projection-normalized products and signed mapping fibres, localization, and descent
of specified triangles. All tower constructions use the recorded strict Roos model.
-/

@[expose] public noncomputable section

attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.restrictionLimits
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.restrictionColimits
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.restrictionAdditive
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric

-- Keep the fixed-universe instances of the original strict-tower interface.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived

set_option autoImplicit false
set_option Elab.async false
-- These type-scanning linters are costly on the fully specified gluing identities.
-- The theorem hypotheses use Finite, and the proofs retain ordinary kernel checking.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
universe t u v w d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme.ProEt
namespace ClopenRoos

attribute [local instance] modulesAbelian restrictionAdditive restrictionLimits
  restrictionColimits piPreadditive

private theorem module_countable_exact (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) : CountableAB4Star (Modules.{t, u, v} X R) := by
  exact module_countable_exactCore X R

private theorem zero_category_equivalence (A : Type*) [Category A] [HasZeroObject A]
    [HasZeroMorphisms A] (hA : ∀ M : A, IsZero M) :
    Nonempty (A ≌ Discrete PUnit) := by
  exact zero_category_equivalenceCore A hA

private theorem empty_modules_zero (X : Scheme.{t}) [IsEmpty X]
    (R : Sheaf (topology X) RingCat.{u}) (M : Modules.{t, u, v} X R) : IsZero M := by
  exact empty_modules_zeroCore X R M

section GenericComparison

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasCountableProducts A] [HasCountableProducts B] (F : A ⥤ B) [F.Additive]

private theorem comparison_transition_generic (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosU C) ≫ roosProductComparison F C =
      roosProductComparison F C ≫ roosU ((roosTowerAction F).obj C) := by
  exact comparison_transition_genericCore F C

private def comparison_iso [PreservesLimitsOfShape (Discrete ℕ) F] :
    roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ roosTowerAction F ⋙ roosF := by
  exact comparison_isoCore F

private theorem comparison_iso_coordinates [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    ((comparison_iso F).hom.app C).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj C) p).hom =
      F.map (roosχ C p).hom ≫ F.biprodComparison _ _ ≫
        biprod.map ((roosProductComparison F C).f p)
          ((roosProductComparison F C).f (p + 1)) := by
  exact comparison_iso_coordinatesCore F C p

private theorem comparison_iso_projection [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosProj C) ≫ roosProductComparison F C =
      (comparison_iso F).hom.app C ≫ roosProj ((roosTowerAction F).obj C) := by
  exact comparison_iso_projectionCore F C

private theorem comparison_iso_evaluation [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosEval C n) =
      (comparison_iso F).hom.app C ≫ roosEval ((roosTowerAction F).obj C) n := by
  exact comparison_iso_evaluationCore F C n

private theorem comparison_iso_boundary [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (boundary C) ≫
      ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((comparison_iso F).hom.app C)⟦(1 : ℤ)⟧' =
      roosProductComparison F C ≫ boundary ((roosTowerAction F).obj C) := by
  exact comparison_iso_boundaryCore F C

private theorem comparison_iso_localized [PreservesLimitsOfShape (Discrete ℕ) F]
    {D : Type*} [Category D] (Q : CochainComplex B ℤ ⥤ D)
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Q.map ((F.mapHomologicalComplex (.up ℤ)).map (roosProj C)) ≫
        Q.map (roosProductComparison F C) =
      (Q.mapIso ((comparison_iso F).app C)).hom ≫
        Q.map (roosProj ((roosTowerAction F).obj C)) ∧
    (∀ n, Q.map ((F.mapHomologicalComplex (.up ℤ)).map (roosEval C n)) =
      (Q.mapIso ((comparison_iso F).app C)).hom ≫
        Q.map (roosEval ((roosTowerAction F).obj C) n)) ∧
    Q.map ((F.mapHomologicalComplex (.up ℤ)).map (boundary C) ≫
      ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((comparison_iso F).hom.app C)⟦(1 : ℤ)⟧') =
      Q.map (roosProductComparison F C) ≫
        Q.map (boundary ((roosTowerAction F).obj C)) := by
  exact comparison_iso_localizedCore F Q C

end GenericComparison

attribute [local irreducible] comparison_iso roosF roosAdditiveComparison roosχ
  DerivedCategory.Q

private theorem pushforward_countable_limits
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.pushforward.{v} φ) := by
  exact pushforward_countable_limitsCore φ

private theorem restriction_countable_limits {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) RingCat.{u}) :
    PreservesLimitsOfShape (Discrete ℕ) (restriction.{t, u, v} j R) := by
  exact restriction_countable_limitsCore j R

private theorem complexRestriction_countable_limits {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) RingCat.{u}) :
    PreservesLimitsOfShape (Discrete ℕ) (complexRestriction.{t, u, v} j R) := by
  exact complexRestriction_countable_limitsCore j R

private def productSections (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u})
    (C : Towers.{t, u, v} X R) (p : ℤ) (U : X.ProEt) :
    ((roosP C).X p).val.obj (op U) ≃+
      ∀ n : ℕ, (((C.X p).obj (op n)).val.obj (op U)) := by
  exact productSectionsCore X R C p U

private theorem productSections_projection (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (C : Towers.{t, u, v} X R)
    (p : ℤ) (U : X.ProEt) (x) (n : ℕ) :
    productSections X R C p U x n =
      ((Pi.π (fun n : ℕ ↦ C.asFunctor.obj (op n)) n).f p).val.app (op U) x := by
  exact productSections_projectionCore X R C p U x n

private def transposeAddEquiv {J K : Type*} (P : J → K → Type*)
    [∀ i k, Add (P i k)] : (∀ i k, P i k) ≃+ ∀ k i, P i k := by
  exact transposeAddEquivCore P

private theorem transposeAddEquiv_apply {J K : Type*} (P : J → K → Type*)
    [∀ i k, Add (P i k)] (x : ∀ i k, P i k) (k : K) (i : J) :
    transposeAddEquiv P x k i = x i k := by
  exact transposeAddEquiv_applyCore P x k i

private theorem normalized_module_gluing
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hv : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) RingCat.{u})
    (hr : ∀ (U : X.ProEtᵒᵖ) (a b : R.obj.obj U), a * b = b * a) :
    ∃ (G : (∀ i, Modules.{t, u, v} (Y i) (restrictedRing (j i) R)) ⥤ Modules.{t, u, v} X R)
      (η : 𝟭 _ ≅ Functor.pi' (fun i ↦ restriction.{t, u, v} (j i) R) ⋙ G)
      (ε : G ⋙ Functor.pi' (fun i ↦ restriction.{t, u, v} (j i) R) ≅ 𝟭 _),
      G.Additive ∧
      (∀ M, (Functor.pi' (fun i ↦ restriction.{t, u, v} (j i) R)).map (η.hom.app M) ≫
        ε.hom.app ((Functor.pi' (fun i ↦ restriction.{t, u, v} (j i) R)).obj M) = 𝟙 _) ∧
      (∀ M, η.hom.app (G.obj M) ≫ G.map (ε.hom.app M) = 𝟙 _) ∧
      ∃ σ : ∀ M U, (G.obj M).val.obj (op U) ≃+
        (∀ i, (M i).val.obj (op (clopenTestPiece (j i) U))),
        (∀ M U (a : R.obj.obj (op U)) x i,
          σ M U (a • x) i = R.obj.map (clopenTestInclusion (j i) U).op a • σ M U x i) ∧
        (∀ M (U V : X.ProEt) (f : V ⟶ U) x i,
          σ M V ((G.obj M).val.map f.op x) i =
            (M i).val.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j i)).map f).op
              (σ M U x i)) ∧
        (∀ M N (f : M ⟶ N) U x i,
          σ N U ((G.map f).val.app (op U) x) i =
            (f i).val.app (op (clopenTestPiece (j i) U)) (σ M U x i)) ∧
        (∀ M U x i, σ ((Functor.pi' (fun i ↦ restriction (j i) R)).obj M) U
          ((η.hom.app M).val.app (op U) x) i =
            M.val.map (clopenTestInclusion (j i) U).op x) ∧
        (∀ M i (W : (Y i).ProEt) x,
          ((ε.hom.app M) i).val.app (op W) x =
            (M i).val.map (clopenDiagonal (j i) W).op
              (σ M ((MorphismProperty.Over.map ⊤
                (inferInstance : WeaklyEtale (j i))).obj W) x i)) := by
  exact normalized_module_gluingCore X I Y j hd hv R hr

attribute [local irreducible] productSections transposeAddEquiv

private abbrev towerAction {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive] :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (.up ℤ)

private def towerGluingLevel {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (G : (∀ i, B i) ⥤ A) [G.Additive]
    (C : ∀ i, CochainComplex (ℕᵒᵖ ⥤ B i) ℤ) (p : ℤ) : ℕᵒᵖ ⥤ A :=
          { obj n := G.obj (fun i ↦ ((C i).X p).obj n)
            map f := G.map (fun i ↦ ((C i).X p).map f)
            map_id n := by
              convert G.map_id (fun i ↦ ((C i).X p).obj n) using 1
              congr 1
              funext i
              exact ((C i).X p).map_id n
            map_comp f g := by
              rw [← G.map_comp]
              congr 1
              funext i
              exact ((C i).X p).map_comp f g }

private def towerGluingObj {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (G : (∀ i, B i) ⥤ A) [G.Additive]
    (C : ∀ i, CochainComplex (ℕᵒᵖ ⥤ B i) ℤ) : CochainComplex (ℕᵒᵖ ⥤ A) ℤ :=
      { X p := towerGluingLevel G C p
        d p q :=
          { app n := G.map (fun i ↦ ((C i).d p q).app n)
            naturality n m f := by
              change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
              rw [← G.map_comp, ← G.map_comp]
              congr 1
              funext i
              exact ((C i).d p q).naturality f }
        shape p q h := by
          apply NatTrans.ext
          funext n
          change G.map _ = 0
          rw [← G.map_zero]
          congr 1
          funext i
          exact congrArg (fun f ↦ f.app n) ((C i).shape p q h)
        d_comp_d' p q r _ _ := by
          apply NatTrans.ext
          funext n
          change G.map _ ≫ G.map _ = 0
          rw [← G.map_comp, ← G.map_zero]
          congr 1
          funext i
          exact congrArg (fun f ↦ f.app n) ((C i).d_comp_d p q r) }

private def towerGluingMap {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (G : (∀ i, B i) ⥤ A) [G.Additive]
    {C D : ∀ i, CochainComplex (ℕᵒᵖ ⥤ B i) ℤ} (f : C ⟶ D) :
    towerGluingObj G C ⟶ towerGluingObj G D :=
      { f p :=
          { app n := G.map (fun i ↦ ((f i).f p).app n)
            naturality n m g := by
              change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
              rw [← G.map_comp, ← G.map_comp]
              congr 1
              funext i
              exact ((f i).f p).naturality g }
        comm' p q _ := by
          apply NatTrans.ext
          funext n
          change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
          rw [← G.map_comp, ← G.map_comp]
          congr 1
          funext i
          exact congrArg (fun f ↦ f.app n) ((f i).comm p q) }

private def towerGluing {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (G : (∀ i, B i) ⥤ A) [G.Additive] :
    (∀ i, CochainComplex (ℕᵒᵖ ⥤ B i) ℤ) ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ :=
  { obj C := towerGluingObj G C
    map f := towerGluingMap G f
    map_id C := by
      apply HomologicalComplex.hom_ext
      intro p
      apply NatTrans.ext
      funext n
      change G.map (𝟙 (fun i ↦ ((C i).X p).obj n)) = 𝟙 _
      exact G.map_id _
    map_comp f g := by
      apply HomologicalComplex.hom_ext
      intro p
      apply NatTrans.ext
      funext n
      change G.map ((fun i ↦ ((f i).f p).app n) ≫
        (fun i ↦ ((g i).f p).app n)) = _
      exact G.map_comp _ _ }


private def towerUnitLevel {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
    (G : (∀ i, B i) ⥤ A) [G.Additive] (η₀ : 𝟭 A ≅ Functor.pi' F ⋙ G)
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    C.X p ≅ ((towerGluing G).obj
      ((Functor.pi' (fun i ↦ towerAction (F i))).obj C)).X p :=
  NatIso.ofComponents (fun n ↦ η₀.app ((C.X p).obj n))
    (fun f ↦ η₀.hom.naturality ((C.X p).map f))

private def towerUnitObj {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
    (G : (∀ i, B i) ⥤ A) [G.Additive] (η₀ : 𝟭 A ≅ Functor.pi' F ⋙ G)
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    C ≅ (towerGluing G).obj ((Functor.pi' (fun i ↦ towerAction (F i))).obj C) :=
  HomologicalComplex.Hom.isoOfComponents (towerUnitLevel F G η₀ C)
    (by intro p q hpq; apply NatTrans.ext; funext n
        exact (η₀.hom.naturality ((C.d p q).app n)).symm)

private def towerUnit {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
    (G : (∀ i, B i) ⥤ A) [G.Additive] (η₀ : 𝟭 A ≅ Functor.pi' F ⋙ G) :
    𝟭 _ ≅ Functor.pi' (fun i ↦ towerAction (F i)) ⋙ towerGluing G :=
  NatIso.ofComponents (towerUnitObj F G η₀)
    (by intro C D f; apply HomologicalComplex.hom_ext; intro p
        apply NatTrans.ext; funext n
        exact η₀.hom.naturality ((f.f p).app n))

private def towerCounitLevel {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
    (G : (∀ i, B i) ⥤ A) [G.Additive] (ε₀ : G ⋙ Functor.pi' F ≅ 𝟭 _)
    (C : ∀ i, CochainComplex (ℕᵒᵖ ⥤ B i) ℤ) (i : J) (p : ℤ) :
    (((towerAction (F i)).obj ((towerGluing G).obj C)).X p) ≅ (C i).X p :=
  NatIso.ofComponents
    (fun n ↦ Pi.isoApp (ε₀.app (fun i ↦ ((C i).X p).obj n)) i)
    (by intro n m f
        exact congrFun (ε₀.hom.naturality (fun i ↦ ((C i).X p).map f)) i)

private def towerCounitObj {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
    (G : (∀ i, B i) ⥤ A) [G.Additive] (ε₀ : G ⋙ Functor.pi' F ≅ 𝟭 _)
    (C : ∀ i, CochainComplex (ℕᵒᵖ ⥤ B i) ℤ) (i : J) :
    (towerAction (F i)).obj ((towerGluing G).obj C) ≅ C i :=
  HomologicalComplex.Hom.isoOfComponents (towerCounitLevel F G ε₀ C i)
    (by intro p q hpq; apply NatTrans.ext; funext n
        exact (congrFun (ε₀.hom.naturality (fun i ↦ ((C i).d p q).app n)) i).symm)

private def towerCounit {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
    (G : (∀ i, B i) ⥤ A) [G.Additive] (ε₀ : G ⋙ Functor.pi' F ≅ 𝟭 _) :
    towerGluing G ⋙ Functor.pi' (fun i ↦ towerAction (F i)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun C ↦ Pi.isoMk (towerCounitObj F G ε₀ C))
    (by intro C D f; funext i; apply HomologicalComplex.hom_ext; intro p
        apply NatTrans.ext; funext n
        exact congrFun (ε₀.hom.naturality (fun i ↦ ((f i).f p).app n)) i)

private theorem tower_triangles {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
    (G : (∀ i, B i) ⥤ A) [G.Additive]
    (η₀ : 𝟭 A ≅ Functor.pi' F ⋙ G) (ε₀ : G ⋙ Functor.pi' F ≅ 𝟭 _)
    (h₁ : ∀ M, (Functor.pi' F).map (η₀.hom.app M) ≫
      ε₀.hom.app ((Functor.pi' F).obj M) = 𝟙 _)
    (h₂ : ∀ M, η₀.hom.app (G.obj M) ≫ G.map (ε₀.hom.app M) = 𝟙 _) :
    (∀ C, (Functor.pi' (fun i ↦ towerAction (F i))).map
      ((towerUnit F G η₀).hom.app C) ≫
        (towerCounit F G ε₀).hom.app
          ((Functor.pi' (fun i ↦ towerAction (F i))).obj C) = 𝟙 _) ∧
    (∀ C, (towerUnit F G η₀).hom.app ((towerGluing G).obj C) ≫
      (towerGluing G).map ((towerCounit F G ε₀).hom.app C) = 𝟙 _) := by
  constructor
  · intro C
    funext i
    apply HomologicalComplex.hom_ext
    intro p
    apply NatTrans.ext
    funext n
    exact congrFun (h₁ ((C.X p).obj n)) i
  · intro C
    apply HomologicalComplex.hom_ext
    intro p
    apply NatTrans.ext
    funext n
    exact h₂ (fun i ↦ ((C i).X p).obj n)

private theorem towerUnit_hom_component {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
    (G : (∀ i, B i) ⥤ A) [G.Additive] (η₀ : 𝟭 A ≅ Functor.pi' F ⋙ G)
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕᵒᵖ) :
    (((towerUnit F G η₀).hom.app C).f p).app n = η₀.hom.app ((C.X p).obj n) := rfl

private theorem towerCounit_hom_component {A : Type*} [Category A] [Preadditive A]
    {J : Type*} {B : J → Type*} [∀ i, Category (B i)] [∀ i, Preadditive (B i)]
    (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
    (G : (∀ i, B i) ⥤ A) [G.Additive] (ε₀ : G ⋙ Functor.pi' F ≅ 𝟭 _)
    (C : ∀ i, CochainComplex (ℕᵒᵖ ⥤ B i) ℤ) (i : J) (p : ℤ) (n : ℕᵒᵖ) :
    ((((towerCounit F G ε₀).hom.app C) i).f p).app n =
      ε₀.hom.app (fun i ↦ ((C i).X p).obj n) i := rfl

attribute [local irreducible] towerUnit towerCounit

attribute [local irreducible] isoTriangleOfIso₁₂

private def liftFamilyIso {A : Type*} [Category A] {J : Type*}
    (B : J → Type*) [∀ i, Category (B i)] (F : ∀ i, A ⥤ B i)
    [(Functor.pi' F).Full] [(Functor.pi' F).Faithful]
    {X Y : A} (e : ∀ i, (F i).obj X ≅ (F i).obj Y) : X ≅ Y :=
  (Functor.pi' F).preimageIso (Pi.isoMk e)

private theorem liftFamilyIso_map {A : Type*} [Category A] {J : Type*}
    (B : J → Type*) [∀ i, Category (B i)] (F : ∀ i, A ⥤ B i)
    [(Functor.pi' F).Full] [(Functor.pi' F).Faithful]
    {X Y : A} (e : ∀ i, (F i).obj X ≅ (F i).obj Y) (i : J) :
    (F i).map (liftFamilyIso B F e).hom = (e i).hom :=
  congrFun ((Functor.pi' F).map_preimage _) i

attribute [local irreducible] liftFamilyIso

private theorem distinguished_iff_family
    {A : Type*} [Category A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {J : Type*} (B : J → Type*) [∀ i, Category (B i)]
    [∀ i, HasZeroObject (B i)] [∀ i, HasShift (B i) ℤ] [∀ i, Preadditive (B i)]
    [∀ (i : J) (n : ℤ), (shiftFunctor (B i) n).Additive]
    [∀ i, Pretriangulated (B i)] (F : ∀ i, A ⥤ B i)
    [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]
    [(Functor.pi' F).Full] [(Functor.pi' F).Faithful] (T : Triangle A) :
    T ∈ distTriang A ↔ ∀ i, (F i).mapTriangle.obj T ∈ distTriang (B i) := by
  classical
  constructor
  · exact fun h i ↦ (F i).map_distinguished T h
  · intro h
    obtain ⟨Z, g, h', mem⟩ := distinguished_cocone_triangle T.mor₁
    let S := Triangle.mk T.mor₁ g h'
    let e (i : J) : (F i).mapTriangle.obj T ≅ (F i).mapTriangle.obj S :=
      isoTriangleOfIso₁₂ _ _ (h i) ((F i).map_distinguished S mem)
        (Iso.refl _) (Iso.refl _) (by
          change (F i).map T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ (F i).map T.mor₁
          simp)
    let P := Functor.pi' F
    let e₃ : T.obj₃ ≅ S.obj₃ := liftFamilyIso B F (fun i ↦
      Triangle.π₃.mapIso (e i))
    have he₃ (i : J) : (F i).map e₃.hom = (e i).hom.hom₃ := by
      exact liftFamilyIso_map B F (fun i ↦ Triangle.π₃.mapIso (e i)) i
    apply isomorphic_distinguished S mem T
    refine Triangle.isoMk T S (Iso.refl _) (Iso.refl _) e₃ ?_ ?_ ?_
    · exact Category.comp_id T.mor₁ |>.trans (Category.id_comp T.mor₁).symm
    · apply P.map_injective
      funext i
      change (F i).map (T.mor₂ ≫ e₃.hom) = (F i).map (𝟙 _ ≫ S.mor₂)
      rw [(F i).map_comp, he₃]
      have hi := (e i).hom.comm₂
      change (F i).map T.mor₂ ≫ (e i).hom.hom₃ =
        (e i).hom.hom₂ ≫ (F i).map S.mor₂ at hi
      have he₂ : (e i).hom.hom₂ = 𝟙 ((F i).obj T.obj₂) :=
        isoTriangleOfIso₁₂_hom_hom₂ _ _ _ _ _ _ _
      rw [he₂] at hi
      change (F i).map T.mor₂ ≫ (e i).hom.hom₃ = 𝟙 _ ≫ (F i).map S.mor₂ at hi
      simpa only [Category.id_comp, Functor.map_id] using hi
    · apply P.map_injective
      funext i
      change (F i).map (T.mor₃ ≫ (𝟙 _)⟦(1 : ℤ)⟧') =
        (F i).map (e₃.hom ≫ h')
      simp only [Functor.map_comp, Functor.map_id, Category.comp_id]
      rw [he₃]
      have hi := (e i).hom.comm₃
      change ((F i).map T.mor₃ ≫ ((F i).commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        ((e i).hom.hom₁)⟦(1 : ℤ)⟧' =
          (e i).hom.hom₃ ≫ ((F i).map h' ≫
            ((F i).commShiftIso (1 : ℤ)).hom.app T.obj₁) at hi
      have he₁ : (e i).hom.hom₁ = 𝟙 ((F i).obj T.obj₁) :=
        isoTriangleOfIso₁₂_hom_hom₁ _ _ _ _ _ _ _
      rw [he₁, (shiftFunctor (B i) (1 : ℤ)).map_id] at hi
      change ((F i).map T.mor₃ ≫ ((F i).commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        𝟙 _ = (e i).hom.hom₃ ≫ ((F i).map h' ≫
          ((F i).commShiftIso (1 : ℤ)).hom.app T.obj₁) at hi
      rw [Category.comp_id] at hi
      rw [(shiftFunctor A (1 : ℤ)).map_id, (F i).map_id, Category.comp_id]
      apply (cancel_mono (((F i).commShiftIso (1 : ℤ)).hom.app T.obj₁)).mp
      simpa only [Category.assoc] using hi



private theorem limit_triangle_descent
    {A : Type*} [Category A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {I : Type*} (B : I → Type*) [∀ i, Category (B i)]
    [∀ i, HasZeroObject (B i)] [∀ i, HasShift (B i) ℤ] [∀ i, Preadditive (B i)]
    [∀ (i : I) (n : ℤ), (shiftFunctor (B i) n).Additive]
    [∀ i, Pretriangulated (B i)] (F : ∀ i, A ⥤ B i)
    [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]
    [∀ i, PreservesLimitsOfShape (Discrete ℕ) (F i)]
    [(Functor.pi' F).Full] [(Functor.pi' F).Faithful] :
    ∀ (K : ℕ → A) [HasProduct K]
      [∀ i, HasProduct (fun n ↦
        (F i).obj (K n))],
      ∃ α : ∀ i,
        (F i).obj
          (∏ᶜ K) ≅ ∏ᶜ (fun n ↦
            (F i).obj
              (K n)),
        (∀ i, (α i).hom = piComparison
          (F i) K) ∧
        ∀ (t : ∀ n, K (n + 1) ⟶ K n)
          (M : A)
          (c : M ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ M⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle t M c δ ↔ ∀ i,
            IsDerivedLimitTriangle
              (fun n ↦ (F i).map (t n))
              ((F i).obj M)
              ((F i).map c ≫ (α i).hom)
              ((α i).inv ≫
                (F i).map δ ≫
                ((F i).commShiftIso (1 : ℤ)).hom.app M) := by
  classical
  intro K _ _
  let α (i : I) := PreservesProduct.iso (F i) K
  refine ⟨α, fun i ↦ PreservesProduct.iso_hom (F i) K, ?_⟩
  intro t M c δ
  change Triangle.mk c (towerTransitionEndomorphism t) δ ∈ distTriang _ ↔ _
  rw [distinguished_iff_family B F]
  apply forall_congr'
  intro i
  have ht : (F i).map (towerTransitionEndomorphism t) ≫ (α i).hom =
      (α i).hom ≫ towerTransitionEndomorphism (fun n ↦ (F i).map (t n)) := by
    apply Pi.hom_ext
    intro n
    simp only [α, PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π,
      towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Preadditive.sub_comp, Category.comp_id, Pi.lift_π, Functor.map_sub]
    rw [← Category.assoc, piComparison_comp_π, ← Functor.map_comp]
    rw [← Functor.map_comp, Pi.lift_π, Category.id_comp, Functor.map_comp]
  let T₁ := Triangle.mk ((F i).map c ≫ (α i).hom)
    (towerTransitionEndomorphism (fun n ↦ (F i).map (t n)))
    ((α i).inv ≫ (F i).map δ ≫ ((F i).commShiftIso (1 : ℤ)).hom.app M)
  let T₂ := (F i).mapTriangle.obj (Triangle.mk c (towerTransitionEndomorphism t) δ)
  exact (distinguished_iff_of_iso (Triangle.isoMk T₁ T₂ (Iso.refl _) (α i).symm
    (α i).symm
    (by change ((F i).map c ≫ (α i).hom) ≫ (α i).inv = 𝟙 _ ≫ (F i).map c; simp)
    (by
      change towerTransitionEndomorphism (fun n ↦ (F i).map (t n)) ≫ (α i).inv =
        (α i).inv ≫ (F i).map (towerTransitionEndomorphism t)
      apply (cancel_mono (α i).hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Iso.inv_hom_id_assoc] using congrArg (fun a ↦ (α i).inv ≫ a) ht.symm)
    (by
      change ((α i).inv ≫ (F i).map δ ≫ ((F i).commShiftIso (1 : ℤ)).hom.app M) ≫
        (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
          (α i).inv ≫ ((F i).map δ ≫ ((F i).commShiftIso (1 : ℤ)).hom.app M)
      simp))).symm


variable (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
  (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
  (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
  (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
  (R : Sheaf (topology X) RingCat.{u})
  (hcomm : ∀ (U : X.ProEtᵒᵖ) (a b : R.obj.obj U), a * b = b * a)

include hdisjoint hcover hcomm

/-- Strict towers glue by the sectionwise product, including the prescribed unit,
counit, actions, differentials, transitions and strict maps.
Source: Stacks 04TQ--04TS (blueprint: lem-pur-clopen-strict-tower-roos-equivalence).
Proof: step 1 applies lem-pur-clopen-ringed-module-gluing at every degree and level.
Apply its gluing functor to differentials, transitions and strict maps. Functoriality
checks all equations. Its unit and counit are natural for these maps and hence lift
with their triangle equations. Their section formulas give the two normalizations.
For gluing, products are sectionwise by lem-weil-proetale-countable-products-exact
(step 2), so the comparison τ of termwise products is σ in each level followed by the
reindexing `gluingProductReindex`, fixing every (i,n) coordinate.
Step 7 uses the empty-cover sheaf axiom when the partition is empty. -/
theorem strict_tower_equivalence :
    ∃ (G : (∀ i, Towers.{t, u, v} (Y i) (restrictedRing (j i) R)) ⥤
          Towers.{t, u, v} X R)
      (η : 𝟭 _ ≅ Functor.pi' (fun i ↦ towerRestriction.{t, u, v} (j i) R) ⋙ G)
      (ε : G ⋙ Functor.pi' (fun i ↦ towerRestriction.{t, u, v} (j i) R) ≅ 𝟭 _),
      (∀ C, (Functor.pi' (fun i ↦ towerRestriction.{t, u, v} (j i) R)).map
          (η.hom.app C) ≫ ε.hom.app
            ((Functor.pi' (fun i ↦ towerRestriction.{t, u, v} (j i) R)).obj C) = 𝟙 _) ∧
      (∀ F, η.hom.app (G.obj F) ≫ G.map (ε.hom.app F) = 𝟙 _) ∧
      ∃ σ : ∀ F (p : ℤ) (n : ℕᵒᵖ) (U : X.ProEt),
        (((G.obj F).X p).obj n).val.obj (op U) ≃+
          (∀ i, (((F i).X p).obj n).val.obj (op (clopenTestPiece (j i) U))),
        (∀ F p n U (a : R.obj.obj (op U)) x i,
          σ F p n U (a • x) i = R.obj.map (clopenTestInclusion (j i) U).op a •
            σ F p n U x i) ∧
        (∀ F p n (U V : X.ProEt) (f : V ⟶ U) x i,
          σ F p n V ((((G.obj F).X p).obj n).val.map f.op x) i =
            (((F i).X p).obj n).val.map
              ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j i)).map f).op
                (σ F p n U x i)) ∧
        (∀ F p n m (f : n ⟶ m) U x i,
          σ F p m U ((((G.obj F).X p).map f).val.app (op U) x) i =
            (((F i).X p).map f).val.app (op (clopenTestPiece (j i) U)) (σ F p n U x i)) ∧
        (∀ F p q n U x i,
          σ F q n U ((((G.obj F).d p q).app n).val.app (op U) x) i =
            (((F i).d p q).app n).val.app (op (clopenTestPiece (j i) U)) (σ F p n U x i)) ∧
        (∀ F H (f : F ⟶ H) p n U x i,
          σ H p n U ((((G.map f).f p).app n).val.app (op U) x) i =
            (((f i).f p).app n).val.app (op (clopenTestPiece (j i) U)) (σ F p n U x i)) ∧
        (∀ C p n U x i,
          σ ((Functor.pi' (fun i ↦ towerRestriction.{t, u, v} (j i) R)).obj C)
            p n U ((((η.hom.app C).f p).app n).val.app (op U) x) i =
              ((C.X p).obj n).val.map (clopenTestInclusion (j i) U).op x) ∧
        (∀ F i p n (W : (Y i).ProEt) x,
          ((((ε.hom.app F) i).f p).app n).val.app (op W) x =
            (((F i).X p).obj n).val.map (clopenDiagonal (j i) W).op
              (σ F p n
                ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).obj W)
                x i)) ∧
        ∃ τ : ∀ F (p : ℤ) (U : X.ProEt),
          ((roosP (G.obj F)).X p).val.obj (op U) ≃+
            (∀ i, ((roosP (F i)).X p).val.obj (op (clopenTestPiece (j i) U))),
          ∀ F p U x i (n : ℕ),
            ((Pi.π (fun n : ℕ ↦ (F i).asFunctor.obj (op n)) n).f p).val.app
                (op (clopenTestPiece (j i) U)) (τ F p U x i) =
              σ F p (op n) U
                (((Pi.π (fun n : ℕ ↦ (G.obj F).asFunctor.obj (op n)) n).f p).val.app
                  (op U) x) i := by
  have hglue := normalized_module_gluing.{t, u, v, w}
    X I Y j hdisjoint hcover R hcomm
  rcases hglue with ⟨G₀, η₀, ε₀, hadd, h₁, h₂, σ₀, hs, hr, hm, hu, he⟩
  let B (i : I) := Modules.{t, u, v} (Y i) (restrictedRing (j i) R)
  let P := Functor.pi' (fun i ↦ restriction.{t, u, v} (j i) R)
  let T := Functor.pi' (fun i ↦ towerRestriction.{t, u, v} (j i) R)
  let F := fun i ↦ restriction.{t, u, v} (j i) R
  let G : (∀ i, Towers.{t, u, v} (Y i) (restrictedRing (j i) R)) ⥤
      Towers.{t, u, v} X R := towerGluing G₀
  let η : 𝟭 _ ≅ T ⋙ G := towerUnit F G₀ η₀
  let ε : G ⋙ T ≅ 𝟭 _ := towerCounit F G₀ ε₀
  have ht := tower_triangles F G₀ η₀ ε₀ h₁ h₂
  let σ (C : ∀ i, Towers.{t, u, v} (Y i) (restrictedRing (j i) R))
      (p : ℤ) (n : ℕᵒᵖ) (U : X.ProEt) := σ₀ (fun i ↦ ((C i).X p).obj n) U
  refine Exists.intro G ?_
  refine Exists.intro η ?_
  refine Exists.intro ε ?_
  refine ⟨?_, ?_, σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ht.1
  · set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      exact ht.2
  · intro C p n U a x i
    exact hs _ U a x i
  · intro C p n U V f x i
    exact hr _ U V f x i
  · intro C p n m f U x i
    exact hm _ _ (fun i ↦ ((C i).X p).map f) U x i
  · intro C p q n U x i
    exact hm _ _ (fun i ↦ ((C i).d p q).app n) U x i
  · intro C D f p n U x i
    exact hm _ _ (fun i ↦ ((f i).f p).app n) U x i
  · intro C p n U x i
    change σ₀ _ U _ i = _
    rw [towerUnit_hom_component F G₀ η₀ C p n]
    exact hu ((C.X p).obj n) U x i
  · intro C i p n W x
    change (((((towerCounit F G₀ ε₀).hom.app C) i).f p).app n).val.app (op W) x = _
    rw [towerCounit_hom_component F G₀ ε₀ C i p n]
    exact he (fun i ↦ ((C i).X p).obj n) i W x
  · let τ (C : ∀ i, Towers.{t, u, v} (Y i) (restrictedRing (j i) R))
        (p : ℤ) (U : X.ProEt) :=
        (productSections X R (G.obj C) p U).trans
          ((AddEquiv.piCongrRight (fun n : ℕ ↦ σ C p (op n) U)).trans
            ((transposeAddEquiv _).trans
              (AddEquiv.piCongrRight (fun i ↦
                (productSections (Y i) (restrictedRing (j i) R) (C i) p
                  (clopenTestPiece (j i) U)).symm))))
    refine ⟨τ, ?_⟩
    intro C p U x i n
    change _ = σ C p (op n) U _ i
    rw [← productSections_projection]
    change (productSections (Y i) (restrictedRing (j i) R) (C i) p
      (clopenTestPiece (j i) U)) ((τ C p U) x i) n = _
    simp only [τ, AddEquiv.trans_apply, transposeAddEquiv_apply,
      AddEquiv.piCongrRight_apply,
      AddEquiv.apply_symm_apply]
    exact congrArg (fun y ↦ σ C p (op n) U y i)
      (productSections_projection X R (G.obj C) p U x n)





/-- Projection-normalized products and the signed two-summand Roos chain isomorphism.
Source: Stacks 07KC, 08TC, 014E (blueprint: lem-pur-clopen-strict-tower-roos-equivalence).
Proof: step 2 computes products sectionwise by lem-weil-proetale-countable-products-exact.
Every projection of alpha is the restricted projection, so the two expressions for
alpha r(v) and v alpha agree. Step 3 defines beta on both summands by alpha.
In the coordinates of def-weil-strict-roos-model the differential is (-dy-vx,dx),
so this is a chain map with diagonal inverse. Products of strict maps prove
naturality. The second projection gives p and pr_n p; the negative inclusion gives
the signed boundary identity. Step 4 applies the localization functor to these
identities and to the chain isomorphism and its inverse. For gluing interchange n and i,
fixing every coordinate. -/
theorem strict_roos_comparison (i : I) :
    ∃ β : roosF ⋙ complexRestriction.{t, u, v} (j i) R ≅
        towerRestriction.{t, u, v} (j i) R ⋙ roosF,
      ∀ C : Towers.{t, u, v} X R,
        IsIso (productComparison.{t, u, v} (j i) R C) ∧
        (∀ n : ℕ,
          productComparison.{t, u, v} (j i) R C ≫ Pi.π _ n =
            (complexRestriction.{t, u, v} (j i) R).map (Pi.π _ n)) ∧
        ((complexRestriction.{t, u, v} (j i) R).map (roosU C) ≫
            productComparison.{t, u, v} (j i) R C =
          productComparison.{t, u, v} (j i) R C ≫
            roosU ((towerRestriction.{t, u, v} (j i) R).obj C)) ∧
        (∀ p : ℤ,
          (β.hom.app C).f (p + 1) ≫
              (roosχ ((towerRestriction.{t, u, v} (j i) R).obj C) p).hom =
            (restriction.{t, u, v} (j i) R).map (roosχ C p).hom ≫
              Functor.biprodComparison
                (restriction.{t, u, v} (j i) R)
                ((roosP C).X p) ((roosP C).X (p + 1)) ≫
              biprod.map
                ((productComparison.{t, u, v} (j i) R C).f p)
                ((productComparison.{t, u, v} (j i) R C).f (p + 1))) ∧
        ((complexRestriction.{t, u, v} (j i) R).map (roosProj C) ≫
            productComparison.{t, u, v} (j i) R C =
          β.hom.app C ≫ roosProj ((towerRestriction.{t, u, v} (j i) R).obj C)) ∧
        (∀ n : ℕ,
          (complexRestriction.{t, u, v} (j i) R).map (roosEval C n) =
            β.hom.app C ≫ roosEval ((towerRestriction.{t, u, v} (j i) R).obj C) n) ∧
        ((complexRestriction.{t, u, v} (j i) R).map (boundary C) ≫
            ((complexRestriction.{t, u, v} (j i) R).commShiftIso (1 : ℤ)).hom.app _ ≫
              (β.hom.app C)⟦(1 : ℤ)⟧' =
          productComparison.{t, u, v} (j i) R C ≫
              boundary ((towerRestriction.{t, u, v} (j i) R).obj C)) ∧
        (∀ [HasDerivedCategory.{d} (Modules.{t, u, v} (Y i) (restrictedRing (j i) R))],
          (localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)).map
              ((complexRestriction.{t, u, v} (j i) R).map (roosProj C)) ≫
            (localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)).map
              (productComparison.{t, u, v} (j i) R C) =
            ((localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)).mapIso
              (β.app C)).hom ≫
            (localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)).map
              (roosProj ((towerRestriction.{t, u, v} (j i) R).obj C)) ∧
          (∀ n : ℕ,
            (localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)).map
                ((complexRestriction.{t, u, v} (j i) R).map (roosEval C n)) =
              ((localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)).mapIso
                (β.app C)).hom ≫
              (localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)).map
                (roosEval ((towerRestriction.{t, u, v} (j i) R).obj C) n)) ∧
          ((localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)).map
              ((complexRestriction.{t, u, v} (j i) R).map (boundary C) ≫
                ((complexRestriction.{t, u, v} (j i) R).commShiftIso (1 : ℤ)).hom.app _ ≫
                  (β.hom.app C)⟦(1 : ℤ)⟧') =
            (localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)).map
                (productComparison.{t, u, v} (j i) R C) ≫
              (localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)).map
                (boundary ((towerRestriction.{t, u, v} (j i) R).obj C)))) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  set_option backward.defeqAttrib.useBackward true in
    let F := restriction.{t, u, v} (j i) R
    let H := complexRestriction.{t, u, v} (j i) R
    let T := towerRestriction.{t, u, v} (j i) R
    have := complexRestriction_countable_limits.{t, u, v} (j i) R
    have hp (C : Towers.{t, u, v} X R) : IsIso (productComparison (j i) R C) := by
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        unfold productComparison
        infer_instance
    have := restriction_countable_limits.{t, u, v} (j i) R
    let β : roosF ⋙ H ≅ T ⋙ roosF := comparison_iso F
    refine ⟨β, ?_⟩
    intro C
    refine ⟨hp C, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact piComparison_comp_π H _ n
    · exact comparison_transition_generic F C
    · exact comparison_iso_coordinates F C
    · exact comparison_iso_projection F C
    · exact comparison_iso_evaluation F C
    · exact comparison_iso_boundary F C
    · intro _
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      exact comparison_iso_localized F
        (localization.{t, u, v, d} (Y i) (restrictedRing (j i) R)) C

/-- Reindex the sectionwise gluing products without changing any (i,n) coordinate.
Source: Stacks 04TS, 07KC (blueprint: lem-pur-clopen-strict-tower-roos-equivalence). -/
def gluingProductReindex
    (F : ∀ i, Towers.{t, u, v} (Y i) (restrictedRing (j i) R))
    (p : ℤ) (U : X.ProEt) :
    (∀ n : ℕ, ∀ i, (((F i).X p).obj (op n)).val.obj
      (op (clopenTestPiece (j i) U))) ≃
      (∀ i, ∀ n : ℕ, (((F i).X p).obj (op n)).val.obj
        (op (clopenTestPiece (j i) U))) :=
  Equiv.piComm _


variable [HasDerivedCategory.{d} (Modules.{t, u, v} X R)]
  [∀ i, HasDerivedCategory.{d}
    (Modules.{t, u, v} (Y i) (restrictedRing (j i) R))]

/-- The actual localized product cones, with all their projections, are limits.
Source: Stacks 07KC (blueprint: lem-pur-clopen-strict-tower-roos-equivalence).
Proof: step 5 uses exact sectionwise products on every component and on X, supplied
by lem-weil-proetale-countable-products-exact. Apply
lem-weil-derived-countable-products-core to the actual termwise product cone.
Thus the localized transition map has exactly its prescribed projection coordinates. -/
theorem derived_products :
    (∀ C : ℕ → CochainComplex (Modules.{t, u, v} X R) ℤ,
      Nonempty (IsLimit
        ((DerivedCategory.Q.{d} (C := _)).mapCone (limit.cone (Discrete.functor C))))) ∧
    (∀ i (C : ℕ → CochainComplex
        (Modules.{t, u, v} (Y i) (restrictedRing (j i) R)) ℤ),
      Nonempty (IsLimit
        ((DerivedCategory.Q.{d} (C := _)).mapCone (limit.cone (Discrete.functor C))))) := by
  have hX := module_countable_exact.{t, u, v} X R
  have hY (i : I) := module_countable_exact.{t, u, v} (Y i) (restrictedRing (j i) R)
  exact ⟨fun C ↦ derivedCategory_termwiseProduct_isLimit _ ℕ C,
    fun i C ↦ derivedCategory_termwiseProduct_isLimit _ ℕ C⟩



omit hdisjoint hcover hcomm in
private theorem derived_product_preservation
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
    [HasCountableProducts A] [HasCountableProducts B]
    [CountableAB4Star A] [CountableAB4Star B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory := by
  have hQA (K : ℕ → CochainComplex A ℤ) :=
    derivedCategory_termwiseProduct_isLimit A ℕ K
  have hQB (K : ℕ → CochainComplex B ℤ) :=
    derivedCategory_termwiseProduct_isLimit B ℕ K
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := B)) := by
    have h (K : ℕ → CochainComplex B ℤ) :
        PreservesLimit (Discrete.functor K) (DerivedCategory.Q (C := B)) :=
      preservesLimit_of_preserves_limit_cone (limit.isLimit _) (hQB K).some
    exact preservesLimitsOfShape_of_discrete _
  have : PreservesLimitsOfShape (Discrete ℕ)
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := inferInstance
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact preservesProductsOfEssSurj ℕ DerivedCategory.Q F.mapDerivedCategory hQA

omit hdisjoint hcover hcomm


attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

include hdisjoint hcover hcomm

private theorem derived_family_equivalence :
    (Functor.pi' (fun i ↦ derivedRestriction.{t, u, v, d} (j i) R)).IsEquivalence := by
  obtain ⟨G, η, ε, hadd, h₁, h₂, σ, hs, hr, hm, hu, he⟩ :=
    normalized_module_gluing.{t, u, v, w} X I Y j hdisjoint hcover R hcomm
  have := hadd
  let r := fun i ↦ restriction.{t, u, v} (j i) R
  let P := Functor.pi' r
  have : P.IsEquivalence := Functor.IsEquivalence.mk' G η ε
  have hfaith : JointlyReflectIsomorphisms r := by
    constructor
    intro M N f hf
    have : IsIso (P.map f) := (isIso_pi_iff (P.map f)).mpr hf
    exact isIso_of_reflects_iso f P
  exact FiniteClopenTensor.derivedPi_isEquivalence r G (fun M N ↦ G.map_zero M N) η ε hfaith

attribute [local irreducible] PreservesProduct.iso

/-- Distinguishedness of the specified Roos triangle is detected componentwise,
with its actual first map and signed connecting map retained.
Source: Stacks 08TC, 015F, 0CRG (blueprint: lem-pur-clopen-strict-tower-roos-equivalence).
Proof: step 4 localizes the explicit chain isomorphism and inverse; functoriality
retains every map identity. Step 5 identifies the product vertices and transition
endomorphisms by their actual projections. Step 6 applies the triangulated derived
restrictions in one direction. Conversely complete the first arrow by TR1.
The module equivalence lifted degreewise and localized is fully faithful, so the
component triangle isomorphisms lift to a triangle isomorphism. Its commutativity
retains the specified three arrows and shift comparison, proving reflection.
Step 7 treats the empty partition by the empty-cover sheaf axiom. -/
theorem derived_triangle_descent :
    ∀ (K : ℕ → DerivedCategory.{d} (Modules.{t, u, v} X R)) [HasProduct K]
      [∀ i, HasProduct (fun n ↦
        (derivedRestriction.{t, u, v, d} (j i) R).obj (K n))],
      ∃ α : ∀ i,
        (derivedRestriction.{t, u, v, d} (j i) R).obj
          (∏ᶜ K) ≅ ∏ᶜ (fun n ↦
            (derivedRestriction.{t, u, v, d} (j i) R).obj
              (K n)),
        (∀ i, (α i).hom = piComparison
          (derivedRestriction.{t, u, v, d} (j i) R) K) ∧
        ∀ (t : ∀ n, K (n + 1) ⟶ K n)
          (M : DerivedCategory.{d} (Modules.{t, u, v} X R))
          (c : M ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ M⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle t M c δ ↔ ∀ i,
            IsDerivedLimitTriangle
              (fun n ↦ (derivedRestriction.{t, u, v, d} (j i) R).map (t n))
              ((derivedRestriction.{t, u, v, d} (j i) R).obj M)
              ((derivedRestriction.{t, u, v, d} (j i) R).map c ≫ (α i).hom)
              ((α i).inv ≫
                (derivedRestriction.{t, u, v, d} (j i) R).map δ ≫
                ((derivedRestriction.{t, u, v, d} (j i) R).commShiftIso (1 : ℤ)).hom.app M) := by
  classical
  have hX := module_countable_exact.{t, u, v} X R
  have hY (i : I) := module_countable_exact.{t, u, v} (Y i) (restrictedRing (j i) R)
  have hp (i : I) : PreservesLimitsOfShape (Discrete ℕ)
      (derivedRestriction.{t, u, v, d} (j i) R) := by
    have := restriction_countable_limits.{t, u, v} (j i) R
    exact derived_product_preservation (restriction.{t, u, v} (j i) R)
  have := derived_family_equivalence.{t, u, v, w, d} X I Y j hdisjoint hcover R hcomm
  exact limit_triangle_descent
    (fun i ↦ DerivedCategory.{d} (Modules.{t, u, v} (Y i) (restrictedRing (j i) R)))
    (fun i ↦ derivedRestriction.{t, u, v, d} (j i) R)

/-- Empty partitions give zero module, strict-tower and derived categories.
Source: Stacks 04TS, 08TC (blueprint: lem-pur-clopen-strict-tower-roos-equivalence).
Proof: step 7: the cover forces X empty; the empty covering of every site object
forces every section module to be zero. Every tower, complex and derived object
is zero, and the unique triangles are distinguished, including the specified maps. -/
theorem empty_partition (hI : IsEmpty I) :
    IsEmpty X ∧ Nonempty (Modules.{t, u, v} X R ≌ Discrete PUnit) ∧
      Nonempty (Towers.{t, u, v} X R ≌ Discrete PUnit) ∧
      Nonempty (DerivedCategory.{d} (Modules.{t, u, v} X R) ≌ Discrete PUnit) ∧
      (∀ T : Triangle (DerivedCategory.{d} (Modules.{t, u, v} X R)),
        T ∈ distTriang _) := by
  let := hI
  have hX : IsEmpty X := ⟨fun x ↦ by
    obtain ⟨i, _⟩ := hcover x
    exact isEmptyElim i⟩
  let := hX
  have hM := empty_modules_zero.{t, u, v} X R
  have hT (C : Towers.{t, u, v} X R) : IsZero C := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro p
    apply NatTrans.ext
    funext n
    exact (hM ((C.X p).obj n)).eq_of_src _ _
  have hC (C : CochainComplex (Modules.{t, u, v} X R) ℤ) : IsZero C := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro p
    exact (hM (C.X p)).eq_of_src _ _
  have hD (K : DerivedCategory.{d} (Modules.{t, u, v} X R)) : IsZero K := by
    let Q := DerivedCategory.Q.{d} (C := Modules.{t, u, v} X R)
    exact (Q.map_isZero (hC (Q.objPreimage K))).of_iso (Q.objObjPreimageIso K).symm
  refine ⟨hX, zero_category_equivalence _ hM, zero_category_equivalence _ hT,
    zero_category_equivalence _ hD, ?_⟩
  intro T
  apply isomorphic_distinguished _ (contractible_distinguished (0 :
    DerivedCategory.{d} (Modules.{t, u, v} X R))) T
  refine Triangle.isoMk _ _ ((hD _).iso (hD _)) ((hD _).iso (hD _))
    ((hD _).iso (hD _)) ?_ ?_ ?_ <;> apply (hD _).eq_of_src


end ClopenRoos
end AlgebraicGeometry.Scheme.ProEt
