/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenRoos.ClopenStrictTowerRoosCore
public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
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
import all WeilConjectures.AlgebraicGeometry.ClopenRoos.ClopenStrictTowerRoosCore
import all WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
import all WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenTensorCalculus
import all WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement
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
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
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

section GenericComparison

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasCountableProducts A] [HasCountableProducts B] (F : A ⥤ B) [F.Additive]

private def comparison_iso [PreservesLimitsOfShape (Discrete ℕ) F] :
    roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ roosTowerAction F ⋙ roosF := by
  exact comparison_isoCore F

end GenericComparison

attribute [local irreducible] comparison_iso roosF roosAdditiveComparison roosχ
  DerivedCategory.Q

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

attribute [local irreducible] towerUnit towerCounit

attribute [local irreducible] isoTriangleOfIso₁₂

attribute [local irreducible] liftFamilyIso

variable (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
  (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
  (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
  (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
  (R : Sheaf (topology X) RingCat.{u})
  (hcomm : ∀ (U : X.ProEtᵒᵖ) (a b : R.obj.obj U), a * b = b * a)

include hdisjoint hcover hcomm

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
omit hdisjoint hcover hcomm

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

include hdisjoint hcover hcomm

attribute [local irreducible] PreservesProduct.iso

end ClopenRoos
end AlgebraicGeometry.Scheme.ProEt
