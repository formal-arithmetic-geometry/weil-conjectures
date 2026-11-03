/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarModels
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseFlatKFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
public import WeilConjectures.SmoothPurity.ChangeOfRingsKFlatIndependentCoefficients

/-! # Vertices for scalar reindexing computation charts

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-scalar-chart-vertices).

The five comparison maps are explicit counit composites on a specified flat-term
K-flat representative. Their invertibility supplies uniquely determined inverses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.podCompletedRingMap
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

structure ScalarComputationChartVertices {D : Type*} [Category D] {ι : Type*}
    (Good : ι → Prop) (V₀ V₁ V₂ V₃ V₄ : D)
    (f₀ : V₀ ⟶ V₁) (f₁ : V₁ ⟶ V₂) (f₂ : V₂ ⟶ V₃)
    (d : V₃ ⟶ V₄) (u : V₀ ⟶ V₄)
    (W₀ W₁ W₂ W₃ W₄ : ι → D)
    (c₀ : ∀ P, W₀ P ⟶ W₁ P) (c₁ : ∀ P, W₁ P ⟶ W₂ P)
    (c₂ : ∀ P, W₂ P ⟶ W₃ P) (c₃ : ∀ P, W₃ P ⟶ W₄ P)
    (c : ∀ P, W₀ P ⟶ W₄ P) where
  P : ι
  good : Good P
  v₀ : V₀ ≅ W₀ P
  v₁ : V₁ ≅ W₁ P
  v₂ : V₂ ≅ W₂ P
  v₃ : V₃ ≅ W₃ P
  v₄ : V₄ ≅ W₄ P

abbrev IntegralScalarChartVertices (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (be : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcExtend (coefficientMap l X R E))
    (bl : pbcExtend (coefficientMap l Y S L) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcExtend (coefficientMap l X R L))
    (de : pbcDerivedExtend (coefficientMap l Y S E) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcDerivedExtend (coefficientMap l X R E))
    (dl : pbcDerivedExtend (coefficientMap l Y S L) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcDerivedExtend (coefficientMap l X R L))
    (K : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y)) :=
    ScalarComputationChartVertices
      (fun P : CochainComplex (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ ↦
        Nonempty (DerivedCategory.Q.obj P ≅ K))
      ((pbcDerivedExtend (coefficientMap l X R E)).obj ((podCompletedDerivedInverseImage l
      (Coefficient.{u} l (PadicAlgCl l) E) g).obj K))
      ((pbcDerivedExtend (coefficientMap l X R L)).obj
        ((completedDerivedScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u}
      l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X).obj
      ((podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g).obj K)))
      ((pbcDerivedExtend (coefficientMap l X R L)).obj
        ((podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g).obj
      ((completedDerivedScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l
      (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) Y).obj K)))
      ((derivedPull l X g B).obj ((pbcDerivedExtend (coefficientMap l Y S L)).obj
      ((completedDerivedScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l
      (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) Y).obj K)))
      ((derivedPull l X g B).obj ((pbcDerivedExtend (coefficientMap l Y S E)).obj K))
      ((pbcReductionNormalization (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X)
      (coefficientMap l X R L) (coefficientMap l X R E) (R.coefficient_scalar E L h))
      ((podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g).obj K)).inv
      ((pbcDerivedExtend (coefficientMap l X R L)).map
        ((completedScalarReindex l (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l
      (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) g).hom.app K))
      (dl.inv.app ((completedDerivedScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) Y).obj K))
      ((derivedPull l X g B).map ((pbcReductionNormalization (completedCoefficientMap l
      (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) L)
      (coefficientInclusion l (PadicAlgCl l) E L h) Y) (coefficientMap l Y S L) (coefficientMap l
      Y S E) (S.coefficient_scalar E L h)) K).hom) (de.inv.app K)
      (fun P ↦ DerivedCategory.Q.obj
        (((pbcExtend (coefficientMap l X R E)).mapHomologicalComplex (.up ℤ)).obj
          (((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E)
      g).mapHomologicalComplex (.up ℤ)).obj P)))
      (fun P ↦ DerivedCategory.Q.obj
        (((pbcExtend (coefficientMap l X R L)).mapHomologicalComplex (.up ℤ)).obj
          (((completedOrdinaryScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
      X).mapHomologicalComplex (.up ℤ)).obj
            (((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E)
      g).mapHomologicalComplex (.up ℤ)).obj P))))
      (fun P ↦ DerivedCategory.Q.obj
        (((pbcExtend (coefficientMap l X R L)).mapHomologicalComplex (.up ℤ)).obj
          (((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) L)
      g).mapHomologicalComplex (.up ℤ)).obj
            (((completedOrdinaryScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
      Y).mapHomologicalComplex (.up ℤ)).obj P))))
      (fun P ↦ DerivedCategory.Q.obj
        (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).obj
          (((pbcExtend (coefficientMap l Y S L)).mapHomologicalComplex (.up ℤ)).obj
            (((completedOrdinaryScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
      Y).mapHomologicalComplex (.up ℤ)).obj P))))
      (fun P ↦ DerivedCategory.Q.obj
        (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).obj
          (((pbcExtend (coefficientMap l Y S E)).mapHomologicalComplex (.up ℤ)).obj P)))
      (fun P ↦ DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (nativeScalarSheafAssociator l X R E L h) (.up
      ℤ)).inv.app
          (((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E)
      g).mapHomologicalComplex (.up ℤ)).obj P)))
      (fun P ↦ DerivedCategory.Q.map
        (((pbcExtend (coefficientMap l X R L)).mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex (completedScalarSheafReindex l (Coefficient.{u} l
      (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l
      (PadicAlgCl l) E L h) g) (.up ℤ)).hom.app P)))
      (fun P ↦ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex bl (.up ℤ)).inv.app
          (((completedOrdinaryScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
      Y).mapHomologicalComplex (.up ℤ)).obj P)))
      (fun P ↦ DerivedCategory.Q.map
        (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (nativeScalarSheafAssociator l Y S E L h)
          (.up ℤ)).hom.app P)))
      (fun P ↦ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex be (.up ℤ)).inv.app P))

def ScalarComputationChartVertices.scalarEquation {D : Type*} [Category D] {ι : Type*}
    {Good : ι → Prop} {V₀ V₁ V₂ V₃ V₄ : D}
    {f₀ : V₀ ⟶ V₁} {f₁ : V₁ ⟶ V₂} {f₂ : V₂ ⟶ V₃}
    {d : V₃ ⟶ V₄} {u : V₀ ⟶ V₄}
    {W₀ W₁ W₂ W₃ W₄ : ι → D}
    {c₀ : ∀ P, W₀ P ⟶ W₁ P} {c₁ : ∀ P, W₁ P ⟶ W₂ P}
    {c₂ : ∀ P, W₂ P ⟶ W₃ P} {c₃ : ∀ P, W₃ P ⟶ W₄ P}
    {c : ∀ P, W₀ P ⟶ W₄ P}
    (t : ScalarComputationChartVertices Good V₀ V₁ V₂ V₃ V₄ f₀ f₁ f₂ d u
      W₀ W₁ W₂ W₃ W₄ c₀ c₁ c₂ c₃ c) : Prop :=
  f₁ ≫ t.v₂.hom = t.v₁.hom ≫ c₁ t.P

def ScalarComputationChartVertices.associatorEquations {D : Type*} [Category D] {ι : Type*}
    {Good : ι → Prop} {V₀ V₁ V₂ V₃ V₄ : D}
    {f₀ : V₀ ⟶ V₁} {f₁ : V₁ ⟶ V₂} {f₂ : V₂ ⟶ V₃}
    {d : V₃ ⟶ V₄} {u : V₀ ⟶ V₄}
    {W₀ W₁ W₂ W₃ W₄ : ι → D}
    {c₀ : ∀ P, W₀ P ⟶ W₁ P} {c₁ : ∀ P, W₁ P ⟶ W₂ P}
    {c₂ : ∀ P, W₂ P ⟶ W₃ P} {c₃ : ∀ P, W₃ P ⟶ W₄ P}
    {c : ∀ P, W₀ P ⟶ W₄ P}
    (t : ScalarComputationChartVertices Good V₀ V₁ V₂ V₃ V₄ f₀ f₁ f₂ d u
      W₀ W₁ W₂ W₃ W₄ c₀ c₁ c₂ c₃ c) : Prop :=
  (f₀ ≫ t.v₁.hom = t.v₀.hom ≫ c₀ t.P) ∧
    (d ≫ t.v₄.hom = t.v₃.hom ≫ c₃ t.P)

private theorem completed_inverse_good (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [Algebra (Padic l) k] [FiniteDimensional (Padic l) k]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l k Y) ℤ)
    (hP : integralOperationsGoodComplex l k Y P) :
    integralOperationsGoodComplex l k X
      (((podCompletedModuleInverseImage l k g).mapHomologicalComplex (.up ℤ)).obj P) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  have hi : IsIso (podCompletedRingMap l k g) := podCompletedRingMap_isIso l k g
  let ringIso := asIso (podCompletedRingMap l k g)
  let W := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let e : (isoSectionwiseInverseImage g CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l k Y) ≅
        completedIntegralCommRingSheafUnrestricted l k X :=
    W.preimageIso ringIso
  have he : W.map e.hom = podCompletedRingMap l k g := W.map_preimage _
  have hF : podCompletedModuleInverseImage l k g =
      @isoSectionwiseModuleInverseImage.{u, u} X Y g inferInstance _ _
        (W.mapIso e).hom (W.mapIso e).isIso_hom := by
    unfold podCompletedModuleInverseImage
    simp only [Functor.mapIso_hom, he]
    with_unfolding_all rfl
  have h := isoSectionwiseModuleInverseImage_flat_kFlat g
    (completedIntegralCommRingSheafUnrestricted l k Y)
    (completedIntegralCommRingSheafUnrestricted l k X) e
    (podCompletedModuleInverseImage l k g) hF
  exact ⟨h.2 P hP.1, fun n ↦ h.1 (P.X n) (hP.2 n)⟩

private theorem completed_scalar_good (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (W : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P) :
    integralOperationsGoodComplex l L W ((completedOrdinaryScalarComplex l E L i W).obj P) := by
  have hflat (n : ℤ) : CategoryTheory.exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (completedIntegralCommRingSheafUnrestricted l E W))
        (P.X n)) :=
    (CategoryTheory.exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso _ (P.X n)) (hP.2 n)
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (completedCoefficientMap l E L i W) P (completedOrdinaryScalarExtension l E L i W)
    (completedScalarChangeData l E L i W).choose_spec.choose
    (completedScalarChangeData l E L i W).choose_spec.choose_spec.choose hP.1 hflat
  exact ⟨h.1, fun n ↦ (CategoryTheory.exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso _ _).symm (h.2 n)⟩

/-- Read off invertibility at a chosen natural transformation from its specification. -/
private theorem isIso_choose_app {K C D : Type*} [Category K] [Category C] [Category D]
    {F G : C ⥤ D} (q : K ⥤ C) {A B : (F ⟶ G) → Prop} {R : K → Prop}
    (H : ∃ ε : F ⟶ G, A ε ∧ B ε ∧ ∀ P, R P → IsIso (ε.app (q.obj P))) (P : K) (hP : R P) :
    IsIso ((Exists.choose H).app (q.obj P)) :=
  (Exists.choose_spec H).2.2 P hP

private theorem scalar_counit_iso (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (W : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    IsIso (completedScalarCounit l E L i W P) := by
  unfold completedScalarCounit
  exact isIso_choose_app _ _ P hp

private theorem native_counit_iso (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (pbcModules W R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso (pbcComplexCounit a P) := by
  have := pbcExtensionCounit_isIso a P hp
  dsimp only [pbcComplexCounit]
  infer_instance

section ConcreteComparisons

variable (l : ℕ) [Fact l.Prime]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)
  (B : RingReindex l X g R S)
  (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
  (K : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y))
  (P : CochainComplex (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ)
  (e : DerivedCategory.Q.obj P ≅ K)

local notation "A" => Coefficient l (PadicAlgCl l) E
local notation "C" => Coefficient l (PadicAlgCl l) L
local notation "i" => coefficientInclusion l (PadicAlgCl l) E L h
local notation "HE" => podCompletedModuleInverseImage l A g
local notation "HL" => podCompletedModuleInverseImage l C g
local notation "TX" => completedDerivedScalarExtension l A C i X
local notation "TY" => completedDerivedScalarExtension l A C i Y
local notation "tX" => completedOrdinaryScalarComplex l A C i X
local notation "tY" => completedOrdinaryScalarComplex l A C i Y
local notation "rE" => pbcDerivedExtend (coefficientMap l X R E)
local notation "rL" => pbcDerivedExtend (coefficientMap l X R L)
local notation "sE" => pbcDerivedExtend (coefficientMap l Y S E)
local notation "sL" => pbcDerivedExtend (coefficientMap l Y S L)

set_option maxHeartbeats 800000 in
-- Nested scalar and inverse-image functors need extra elaboration heartbeats.
/-- The first vertex comparison: representative transport, exact pullback, counit.
Source: Stacks 06YY (blueprint: lem-sf-adic-reindex-scalar-chart-vertices). -/
def adicScalarChartMap₀ :=
  (rE).map ((podCompletedDerivedInverseImage l A g).map e.inv) ≫
    (rE).map ((HE).mapDerivedCategoryFactors.hom.app P) ≫
    pbcComplexCounit (coefficientMap l X R E)
      (((HE).mapHomologicalComplex (.up ℤ)).obj P)

set_option maxHeartbeats 800000 in
-- Nested scalar and inverse-image functors need extra elaboration heartbeats.
/-- The second comparison uses scalar extension after exact pullback.
Source: Stacks 06YY (blueprint: lem-sf-adic-reindex-scalar-chart-vertices). -/
def adicScalarChartMap₁ :=
  (rL).map ((TX).map ((podCompletedDerivedInverseImage l A g).map e.inv)) ≫
    (rL).map ((TX).map ((HE).mapDerivedCategoryFactors.hom.app P)) ≫
    (rL).map (completedScalarCounit l A C i X
      (((HE).mapHomologicalComplex (.up ℤ)).obj P)) ≫
    pbcComplexCounit (coefficientMap l X R L)
      ((tX).obj (((HE).mapHomologicalComplex (.up ℤ)).obj P))

set_option maxHeartbeats 800000 in
-- Nested scalar and inverse-image functors need extra elaboration heartbeats.
/-- The third comparison uses exact pullback after scalar extension.
Source: Stacks 06YY (blueprint: lem-sf-adic-reindex-scalar-chart-vertices). -/
def adicScalarChartMap₂ :=
  (rL).map ((podCompletedDerivedInverseImage l C g).map ((TY).map e.inv)) ≫
    (rL).map ((podCompletedDerivedInverseImage l C g).map
      (completedScalarCounit l A C i Y P)) ≫
    (rL).map ((HL).mapDerivedCategoryFactors.hom.app ((tY).obj P)) ≫
    pbcComplexCounit (coefficientMap l X R L)
      (((HL).mapHomologicalComplex (.up ℤ)).obj ((tY).obj P))

set_option maxHeartbeats 800000 in
-- Nested scalar and inverse-image functors need extra elaboration heartbeats.
/-- The fourth comparison uses native extension after scalar extension.
Source: Stacks 06YY (blueprint: lem-sf-adic-reindex-scalar-chart-vertices). -/
def adicScalarChartMap₃ :=
  (derivedPull l X g B).map ((sL).map ((TY).map e.inv)) ≫
    (derivedPull l X g B).map ((sL).map (completedScalarCounit l A C i Y P)) ≫
    (derivedPull l X g B).map (pbcComplexCounit (coefficientMap l Y S L) ((tY).obj P)) ≫
    (modulePull l X g B).mapDerivedCategoryFactors.hom.app
      (((pbcExtend (coefficientMap l Y S L)).mapHomologicalComplex (.up ℤ)).obj ((tY).obj P))

set_option maxHeartbeats 800000 in
-- Nested scalar and inverse-image functors need extra elaboration heartbeats.
/-- The fifth comparison uses the native extension counit and exact reindexing.
Source: Stacks 06YY (blueprint: lem-sf-adic-reindex-scalar-chart-vertices). -/
def adicScalarChartMap₄ :=
  (derivedPull l X g B).map ((sE).map e.inv) ≫
    (derivedPull l X g B).map (pbcComplexCounit (coefficientMap l Y S E) P) ≫
    (modulePull l X g B).mapDerivedCategoryFactors.hom.app
      (((pbcExtend (coefficientMap l Y S E)).mapHomologicalComplex (.up ℤ)).obj P)

set_option maxHeartbeats 800000 in
-- Nested scalar and inverse-image functors need extra elaboration heartbeats.
/-- Invertibility of the five specified counit composites, with no edge equations.
Source: Stacks 06YY, 07A4; BS 6.8.14--6.8.15.
(blueprint: lem-sf-adic-reindex-scalar-chart-vertices).

Proof in words: exact inverse image preserves flat-term K-flat complexes. Ordinary
coefficient extension preserves the same class by change of rings. The universal
extension counits on these complexes are isomorphisms. Every other factor displayed
in the five definitions is either an exact-derived factorization isomorphism or the
image of the representative isomorphism. Functors preserve isomorphisms, and the
five composites are consequently isomorphisms. No compatibility equation is used.
-/
theorem adic_scalar_chart_vertices
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l A Y) P)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l A Y) (P.X n)) :
    IsIso (adicScalarChartMap₀ l g R E K P e) ∧
    IsIso (adicScalarChartMap₁ l g R E L h K P e) ∧
    IsIso (adicScalarChartMap₂ l g R E L h K P e) ∧
    IsIso (adicScalarChartMap₃ l g R S B E L h K P e) ∧
    IsIso (adicScalarChartMap₄ l g R S B E K P e) := by
  have hPE := completed_inverse_good l A g P ⟨hp, hf⟩
  have htXP := completed_scalar_good l A C i X _ hPE
  have htYP := completed_scalar_good l A C i Y P ⟨hp, hf⟩
  have hLtYP := completed_inverse_good l C g _ htYP
  have hsX : IsIso (completedScalarCounit l A C i X
      (((HE).mapHomologicalComplex (.up ℤ)).obj P)) :=
    scalar_counit_iso l A C i X _ hPE.1
  have hsY : IsIso (completedScalarCounit l A C i Y P) :=
    scalar_counit_iso l A C i Y P hp
  have hn₀ : IsIso (pbcComplexCounit (coefficientMap l X R E)
      (((HE).mapHomologicalComplex (.up ℤ)).obj P)) :=
    native_counit_iso X (coefficientMap l X R E) _ hPE.1
  have hn₁ : IsIso (pbcComplexCounit (coefficientMap l X R L)
      ((tX).obj (((HE).mapHomologicalComplex (.up ℤ)).obj P))) :=
    native_counit_iso X (coefficientMap l X R L) _ htXP.1
  have hn₂ : IsIso (pbcComplexCounit (coefficientMap l X R L)
      (((HL).mapHomologicalComplex (.up ℤ)).obj ((tY).obj P))) :=
    native_counit_iso X (coefficientMap l X R L) _ hLtYP.1
  have hn₃ : IsIso (pbcComplexCounit (coefficientMap l Y S L) ((tY).obj P)) :=
    native_counit_iso Y (coefficientMap l Y S L) _ htYP.1
  have hn₄ : IsIso (pbcComplexCounit (coefficientMap l Y S E) P) :=
    native_counit_iso Y (coefficientMap l Y S E) P hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change IsIso (((rE).mapIso ((podCompletedDerivedInverseImage l A g).mapIso e.symm) ≪≫
      (rE).mapIso ((HE).mapDerivedCategoryFactors.app P) ≪≫ asIso
        (pbcComplexCounit (coefficientMap l X R E)
          (((HE).mapHomologicalComplex (.up ℤ)).obj P))).hom)
    infer_instance
  · change IsIso (((rL).mapIso ((TX).mapIso
        ((podCompletedDerivedInverseImage l A g).mapIso e.symm)) ≪≫
      (rL).mapIso ((TX).mapIso ((HE).mapDerivedCategoryFactors.app P)) ≪≫
      (rL).mapIso (asIso (completedScalarCounit l A C i X
        (((HE).mapHomologicalComplex (.up ℤ)).obj P))) ≪≫ asIso
        (pbcComplexCounit (coefficientMap l X R L)
          ((tX).obj (((HE).mapHomologicalComplex (.up ℤ)).obj P)))).hom)
    infer_instance
  · change IsIso (((rL).mapIso ((podCompletedDerivedInverseImage l C g).mapIso
        ((TY).mapIso e.symm)) ≪≫
      (rL).mapIso ((podCompletedDerivedInverseImage l C g).mapIso
        (asIso (completedScalarCounit l A C i Y P))) ≪≫
      (rL).mapIso ((HL).mapDerivedCategoryFactors.app ((tY).obj P)) ≪≫ asIso
        (pbcComplexCounit (coefficientMap l X R L)
          (((HL).mapHomologicalComplex (.up ℤ)).obj ((tY).obj P)))).hom)
    infer_instance
  · change IsIso (((derivedPull l X g B).mapIso ((sL).mapIso ((TY).mapIso e.symm)) ≪≫
      (derivedPull l X g B).mapIso ((sL).mapIso
        (asIso (completedScalarCounit l A C i Y P))) ≪≫
      (derivedPull l X g B).mapIso (asIso
        (pbcComplexCounit (coefficientMap l Y S L) ((tY).obj P))) ≪≫
      (modulePull l X g B).mapDerivedCategoryFactors.app
        (((pbcExtend (coefficientMap l Y S L)).mapHomologicalComplex (.up ℤ)).obj
          ((tY).obj P))).hom)
    infer_instance
  · change IsIso (((derivedPull l X g B).mapIso ((sE).mapIso e.symm) ≪≫
      (derivedPull l X g B).mapIso (asIso (pbcComplexCounit (coefficientMap l Y S E) P)) ≪≫
      (modulePull l X g B).mapDerivedCategoryFactors.app
        (((pbcExtend (coefficientMap l Y S E)).mapHomologicalComplex (.up ℤ)).obj P)).hom)
    infer_instance

end ConcreteComparisons

set_option maxHeartbeats 800000 in
-- Nested scalar and inverse-image functors need extra elaboration heartbeats.
/-- The concrete chart vertices. Their hom maps are exactly the five composites
above; only the uniquely determined inverses use the invertibility theorem.
Source: Stacks 06YY (blueprint: lem-sf-adic-reindex-scalar-chart-vertices). -/
def adicScalarChartVertices (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (be : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcExtend (coefficientMap l X R E))
    (bl : pbcExtend (coefficientMap l Y S L) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcExtend (coefficientMap l X R L))
    (de : pbcDerivedExtend (coefficientMap l Y S E) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcDerivedExtend (coefficientMap l X R E))
    (dl : pbcDerivedExtend (coefficientMap l Y S L) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcDerivedExtend (coefficientMap l X R L))
    (K : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y))
    (P : CochainComplex (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l
        (Coefficient.{u} l (PadicAlgCl l) E) Y) P)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l
        (Coefficient.{u} l (PadicAlgCl l) E) Y) (P.X n)) :
    IntegralScalarChartVertices l g R S B E L h be bl de dl K := by
  have q := adic_scalar_chart_vertices l g R S B E L h K P e hp hf
  have hi₀ : IsIso (adicScalarChartMap₀ l g R E K P e) := q.1
  have hi₁ : IsIso (adicScalarChartMap₁ l g R E L h K P e) := q.2.1
  have hi₂ : IsIso (adicScalarChartMap₂ l g R E L h K P e) := q.2.2.1
  have hi₃ : IsIso (adicScalarChartMap₃ l g R S B E L h K P e) := q.2.2.2.1
  have hi₄ : IsIso (adicScalarChartMap₄ l g R S B E K P e) := q.2.2.2.2
  exact
    { P := P
      good := ⟨e⟩
      v₀ := @asIso _ _ _ _ (adicScalarChartMap₀ l g R E K P e) hi₀
      v₁ := @asIso _ _ _ _ (adicScalarChartMap₁ l g R E L h K P e) hi₁
      v₂ := @asIso _ _ _ _ (adicScalarChartMap₂ l g R E L h K P e) hi₂
      v₃ := @asIso _ _ _ _ (adicScalarChartMap₃ l g R S B E L h K P e) hi₃
      v₄ := @asIso _ _ _ _ (adicScalarChartMap₄ l g R S B E K P e) hi₄ }

end WeilConjectures.AdicQbarRealization
