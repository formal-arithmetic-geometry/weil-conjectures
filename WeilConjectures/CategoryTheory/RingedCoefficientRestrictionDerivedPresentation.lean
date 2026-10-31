/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedCoefficientCounitPresentations
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependentSupplement
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.ShrinkYoneda
import all WeilConjectures.CategoryTheory.RingedToposDerivedAdjunctionOfUniverses
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

/-!
# Existence of normalized derived coefficient presentations

Source: Stacks, Tags 07A6 and 0D6E.
(blueprint: lem-pur-ringed-coefficient-derived-presentation-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingedCoefficientCounit

-- A resolving-class left derived functor remains universal after postcomposition.
private theorem postLeftDerived
    {B E T : Type*} [Category B] [Category E] [Category T] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    (L : B ⥤ E) [L.Additive]
    (LF : DerivedCategory B ⥤ DerivedCategory E)
    (εh : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor εh (HomotopyCategory.quasiIso B (.up ℤ)))
    (P : Set (HomotopyCategory B (.up ℤ)))
    (hres : ∀ X, ∃ (Y : HomotopyCategory B (.up ℤ)) (s : Y ⟶ X),
      Y ∈ P ∧ HomotopyCategory.quasiIso B (.up ℤ) s)
    (hinv : ∀ X Y (s : X ⟶ Y), X ∈ P → Y ∈ P →
      HomotopyCategory.quasiIso B (.up ℤ) s →
      IsIso ((L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map s))
    (ε : DerivedCategory.Q ⋙ LF ⟶ onComplex L ⋙ DerivedCategory.Q)
    (hεapp : ∀ K, ε.app K = εh.app ((HomotopyCategory.quotient B (.up ℤ)).obj K))
    (H : DerivedCategory E ⥤ T) :
    (LF ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε H)
      (HomologicalComplex.quasiIso B (.up ℤ)) := by
  let := hLF
  let := CategoryTheory.quasiIso_twoOutOfThree B
  have hc : ∀ X, ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget (HomotopyCategory.quasiIso B (.up ℤ)) ⊤ X ⋙
        Over.forget X ⋙ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) Y := by
    intro X
    obtain ⟨Y, _, hy, _⟩ := Functor.resolvingClass_essentialConstancy
      (HomotopyCategory.quasiIso B (.up ℤ))
      (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) P hres hinv X
    exact ⟨Y, hy⟩
  have : H.PreservesRightKanExtension
      (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) DerivedCategory.Qh :=
    _root_.pro_absolute (HomotopyCategory.quasiIso B (.up ℤ)) DerivedCategory.Qh
      (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) H hc
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension LF εh
    (HomotopyCategory.quasiIso B (.up ℤ))
  have hLHh : (LF ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight εh H)
      (HomotopyCategory.quasiIso B (.up ℤ)) := ⟨inferInstance⟩
  let := hLHh
  obtain ⟨δ, hδ, hδapp⟩ := CategoryTheory.leftDerivedOnComplexes L H (LF ⋙ H)
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight εh H)
  have hδeq : δ = (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε H := by
    apply NatTrans.ext
    funext X
    simp only [hδapp, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp, hεapp]
  rw [hδeq] at hδ
  exact hδ

-- Descend the ordinary adjunction and retain its chain-map Hom normalization.
private theorem normalizedAdjunction
    (T : Type*) [Category T]
    {B E : Type*} [Category B] [Category E] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    [Abelian.HasKInjectiveResolutions E]
    (L : B ⥤ E) [L.Additive] (R : E ⥤ B) [R.Additive] (adj : L ⊣ R)
    (LF : DerivedCategory B ⥤ DerivedCategory E)
    (εh : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor εh (HomotopyCategory.quasiIso B (.up ℤ)))
    (P : Set (HomotopyCategory B (.up ℤ)))
    (hres : ∀ X, ∃ (Y : HomotopyCategory B (.up ℤ)) (s : Y ⟶ X),
      Y ∈ P ∧ HomotopyCategory.quasiIso B (.up ℤ) s)
    (hinv : ∀ X Y (s : X ⟶ Y), X ∈ P → Y ∈ P →
      HomotopyCategory.quasiIso B (.up ℤ) s →
      IsIso ((L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map s)) :
    ∃ d : DerivedAdjunction L R adj, (∀ K,
      IsIso (εh.app ((HomotopyCategory.quotient B (.up ℤ)).obj K)) →
        IsIso (d.epsilon.app K)) ∧
      ∀ H : DerivedCategory E ⥤ T, (d.left ⋙ H).IsLeftDerivedFunctor
        ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight d.epsilon H)
        (HomologicalComplex.quasiIso B (.up ℤ)) := by
  classical
  let := hLF
  obtain ⟨RF, η, hRF, hη⟩ := CategoryTheory.exists_derived R
  let := hRF
  obtain ⟨ε₀, hε₀, hεapp₀⟩ := CategoryTheory.leftDerivedOnComplexes L (𝟭 _) LF εh
  let ε : DerivedCategory.Q ⋙ LF ⟶ onComplex L ⋙ DerivedCategory.Q := ε₀
  have hε : LF.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso B (.up ℤ)) := hε₀
  have hεapp (K) : ε.app K = εh.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) :=
    hεapp₀ K
  let := hε
  have hRFL : (RF ⋙ LF).IsRightDerivedFunctor
      (Functor.whiskerRight η LF ≫ (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso E (.up ℤ)) := by
    have hd : (CochainComplex.KInjectives.localizerMorphism E).Derives
        (onComplex R ⋙ DerivedCategory.Q ⋙ LF) := by
      intro I I' g hg
      have : IsIso (DerivedCategory.Q.map ((onComplex R).map g.hom)) :=
        (CategoryTheory.derives R) g hg
      exact LF.map_isIso (DerivedCategory.Q.map ((onComplex R).map g.hom))
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have : IsIso (η.app I.obj) := hη I.obj I.property
    change IsIso (LF.map (η.app I.obj) ≫ 𝟙 _)
    infer_instance
  let := hRFL
  have hδ := postLeftDerived L LF εh hLF P hres hinv ε hεapp RF
  let := hδ
  let ac := adj.mapHomologicalComplex (.up ℤ)
  let d := ac.derived (HomologicalComplex.quasiIso B (.up ℤ))
    (HomologicalComplex.quasiIso E (.up ℤ)) ε η
  refine ⟨{
    left := LF
    right := RF
    epsilon := ε
    eta := η
    isLeft := hε
    isRight := hRF
    onInjective := hη
    adj := d
    homFormula := ?_
  }, ?_, ?_⟩
  · intro K I _ h
    change LF.map (DerivedCategory.Q.map h ≫ η.app I) ≫
      d.counit.app (DerivedCategory.Q.obj I) = _
    rw [Functor.map_comp, Category.assoc]
    have hd := ac.derivedε_fac_app (HomologicalComplex.quasiIso E (.up ℤ)) ε η I
    change LF.map (η.app I) ≫ d.counit.app (DerivedCategory.Q.obj I) = _ at hd
    rw [hd, ← Category.assoc]
    have hn := ε.naturality h
    dsimp only [Functor.comp_map] at hn
    rw [hn]
    simp only [Category.assoc, ← Functor.map_comp]
    rfl
  · intro K hK
    change IsIso (ε.app K)
    rw [hεapp]
    exact hK
  · intro H
    exact postLeftDerived L LF εh hLF P hres hinv ε hεapp H

private def goodComplex
    {E : Type u} [Category.{v} E] [EssentiallySmall.{r} E]
    {J : GrothendieckTopology E}
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r}) : ObjectProperty (HomotopyCategory (modules R) (.up ℤ)) :=
  fun K ↦ CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) K.as ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (K.as.X n)

private theorem goodComplex_resolutions
    {E : Type u} [Category.{v} E] [EssentiallySmall.{r} E]
    {J : GrothendieckTopology E}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r}) (K : HomotopyCategory (modules R) (.up ℤ)) :
    ∃ (P : HomotopyCategory (modules R) (.up ℤ)) (s : P ⟶ K),
      goodComplex R P ∧ HomotopyCategory.quasiIso (modules R) (.up ℤ) s := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨P, p, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  have hf' (n : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hf n)
  exact ⟨(HomotopyCategory.quotient _ _).obj P, (HomotopyCategory.quotient _ _).map p,
    ⟨hp, hf'⟩, (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hq⟩

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [UnivLE.{max u v, r}] [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
  [JX.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JX.HasSheafCompose (forget AddCommGrpCat.{r})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{r})]
  [HasSheafify JX AddCommGrpCat.{r}] [JX.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify JY AddCommGrpCat.{r}] [JY.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify JX CommRingCat.{r}] [HasWeakSheafify JY CommRingCat.{r}]
  (A : CommRingCat.{r}) (RX RI : Sheaf JX CommRingCat.{r})
  (RY : Sheaf JY CommRingCat.{r})
  (inverse : Sheaf JY (Type r) ⥤ Sheaf JX (Type r))
  (direct : Sheaf JX (Type r) ⥤ Sheaf JY (Type r)) (geom : inverse ⊣ direct)
  [leftExact : PreservesFiniteLimits inverse]
  (IA : SheafOfModules.AlgebraicInverseImage inverse
    (constantRing JY A) (constantRing JX A))
  (IR : SheafOfModules.AlgebraicInverseImage inverse RY RI) (c : RI ⟶ RX)

-- Preserve the original compatibility hypotheses, although the ordinary presentation
-- already supplies all comparison maps needed by this construction.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
-- The construction checks several universal properties and their representative formulas.
include leftExact in
/-- A normalized derived presentation can be chosen from the ordinary one.

Source: Stacks Project, sites-cohomology.tex, Tags 07A6 and 0D6E;
sites-modules.tex, Tag 03D7. The coefficient normalization is an agent consequence.
(blueprint: lem-pur-ringed-coefficient-derived-presentation-exists).

Proof:
1. The ordinary coefficient adjunction theorem gives exactness of both scalar restrictions
`restriction aX` and `restriction aY`. The algebraic inverse-image finite-limit lemma and the
ordinary adjunction `o.adjA` make `IA.modules` exact. The Grothendieck theorem in the coefficient
universe supplies K-injective resolutions for RX-modules and constant-A modules on X.
2. Take the universal homotopy left-derived tensor pullback of `o.pull`, computed on flat-term
K-flat complexes (the independent-universe ringed pullback theorem). Flat-term K-flat
resolutions form a resolving class, so by essential constancy the left-derived comparison stays
absolute under every postcomposition; pass it to complexes. The right derived functor of
`o.pushR` is computed by K-injectives. Mathlib's `Adjunction.derived` descends `o.adjR`; its
counit factorization and naturality give `r.homFormula`. Repeat for `o.adjA` with exact
`IA.modules`, its termwise derived localization and the whole homotopy category as resolving
class; then `a.epsilon` is invertible everywhere, and the resolving class gives
`flatComparison`.
3. Let x and y be the exact derived scalar restrictions with their factorization isomorphisms.
The absolute left-derived counit of the ringed pullback stays universal after postcomposition
by x, and the x factorization moves its target to termwise scalar restriction. Composing the y
factorization, `a.epsilon` and the localized ordinary `scalarUnit`, the left-derived universal
property gives `tau`; its factorization equation is `tauFormula`, on every complex.
4. Restriction of a K-injective RX-complex is pushA-acyclic: apply `isIso_map_of_adjoints` to
the homotopy adjunction of scalar extension along aX and to that of `o.adjA`, with the K-flat
constant-A complexes on X and the flat-term K-flat complexes on Y as resolving classes; scalar
extension preserves quasi-isomorphisms of K-flat complexes, exact `IA.modules` preserves all
quasi-isomorphisms, and inverse image carries flat-term K-flat complexes to K-flat ones. The Hom
bijections into K-injectives show that `o.pushA` sends a K-injective replacement j of
`restriction aX` of I to a quasi-isomorphism, so `a.eta` is invertible there.
5. From the termwise composite `o.pushR ⋙ restriction aY` define two comparisons: the inverse y
factorization followed by y of `r.eta`, and localized `ordinaryKappa` followed by `a.eta` and
`a.right` of the inverse x factorization. Both are invertible on K-injectives (step 4), so both
are right-derived units; right-derived uniqueness gives `kappa` with its factorization equation.
Naturality of `a.eta` along j and cancellation of Q(j) give `kappaFormula`. Assemble the data
into `DerivedPresentation`. No counit square or coefficient-change naturality is asserted
here. -/
theorem exists_derivedPresentation
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (haI : (sheafCompose JX (forget CommRingCat.{r})).map aI =
      IA.ringUnderlying.inv ≫ inverse.map
        ((sheafCompose JY (forget CommRingCat.{r})).map aY) ≫ IR.ringUnderlying.hom)
    (hc : aI ≫ c = aX)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI)
    [IA.modules.Additive]
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (modules (constantRing JX A))]
    [HasDerivedCategory.{w} (modules (constantRing JY A))] :
    Nonempty (DerivedPresentation o) := by
  classical
  -- Exact scalar restriction and inverse image give the constant-coefficient localization.
  obtain ⟨hxL, hxC, _⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction aX
  obtain ⟨hyL, hyC, _⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction aY
  let := hxL
  let := hxC
  let := hyL
  let := hyC
  have hAL : PreservesFiniteLimits IA.modules :=
    SheafOfModules.algebraicInverseImage_finiteLimits inverse IA
  let := hAL
  have : PreservesColimitsOfSize.{0, 0} IA.modules := o.adjA.leftAdjoint_preservesColimits
  have hAC : PreservesFiniteColimits IA.modules := inferInstance
  let := hAC
  have hGX : IsGrothendieckAbelian.{r} (modules RX) :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
  have hGA : IsGrothendieckAbelian.{r} (modules (constantRing JX A)) :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
  let := hGX
  let := hGA
  -- Construct the ringed derived adjunction on the flat-term K-flat resolving class.
  have hpull {M N} (f : M ⟶ N) : o.pull.map f = eqToHom (o.pull_obj M) ≫
      SheafOfModules.changeOfRingsHom c (IR.modules.obj M) (IR.modules.map f) ≫
        eqToHom (o.pull_obj N).symm := by
    apply (cancel_mono (eqToHom (o.pull_obj N))).1
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
      o.pull_map f
  obtain ⟨LF, εh, hLF, _, hinv, hεh, _⟩ :=
    SheafOfModules.ringedTopoiDerivedPullbackIndependent inverse direct geom IR c
      o.pull o.pull_obj hpull
  have hpres : ∀ X Y (s : X ⟶ Y), goodComplex RY X → goodComplex RY Y →
      HomotopyCategory.quasiIso (modules RY) (.up ℤ) s →
      IsIso ((o.pull.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map s) := by
    intro X Y s hX hY hs
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
    have hs' := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have ht := hinv s hX.1 hX.2 hY.1 hY.2 hs'
    change IsIso (DerivedCategory.Qh.map
      ((o.pull.mapHomotopyCategory (.up ℤ)).map ((HomotopyCategory.quotient _ _).map s)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (modules RX) (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨r, hr, hrpost⟩ := normalizedAdjunction
    (DerivedCategory (modules (constantRing JX A))) o.pull o.pushR o.adjR LF εh hLF
    (goodComplex RY) (goodComplex_resolutions RY) hpres
  -- The constant-coefficient inverse image is already exact.
  let LA := IA.modules.mapDerivedCategory
  let εA := IA.modules.mapDerivedCategoryFactorsh.hom
  have hLA : LA.IsLeftDerivedFunctor εA
      (HomotopyCategory.quasiIso (modules (constantRing JY A)) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ IA.modules.mapDerivedCategoryFactorsh
  have hinvA : ∀ X Y (s : X ⟶ Y), X ∈ (Set.univ : Set _) → Y ∈ (Set.univ : Set _) →
      HomotopyCategory.quasiIso (modules (constantRing JY A)) (.up ℤ) s →
      IsIso ((IA.modules.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map s) := by
    intro X Y s _ _ hs
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
    have : QuasiIso s := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have : QuasiIso ((onComplex IA.modules).map s) := inferInstance
    change IsIso (DerivedCategory.Qh.map
      ((IA.modules.mapHomotopyCategory (.up ℤ)).map ((HomotopyCategory.quotient _ _).map s)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (modules (constantRing JX A)) (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 this)
  obtain ⟨a, ha, _⟩ := normalizedAdjunction
    (DerivedCategory (modules (constantRing JX A))) IA.modules o.pushA o.adjA LA εA hLA
    Set.univ (fun X ↦ ⟨X, 𝟙 _, Set.mem_univ _,
      (HomotopyCategory.quasiIso _ _).id_mem X⟩) hinvA
  have hexactA : IsIso a.epsilon := by
    have : ∀ K, IsIso (a.epsilon.app K) := fun K ↦ ha K (by dsimp [εA]; infer_instance)
    exact NatIso.isIso_of_isIso_app _
  have hflat : ∀ P : CochainComplex (modules RY) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := JY) (R := RY) (P.X n)) →
      IsIso (r.epsilon.app P) := fun P hp hf ↦ hr P (hεh P hp hf)
  let x := (restriction aX).mapDerivedCategory
  let y := (restriction aY).mapDerivedCategory
  let xf := (restriction aX).mapDerivedCategoryFactors
  let yf := (restriction aY).mapDerivedCategoryFactors
  -- The absolute left-derived counit lifts the termwise scalar-unit comparison.
  let βr : onComplex o.pull ⋙ DerivedCategory.Q ⋙ x ⟶
      onComplex o.pull ⋙ onComplex (restriction aX) ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft (onComplex o.pull) xf.hom
  let αr₀ := (Functor.associator _ _ _).inv ≫ Functor.whiskerRight r.epsilon x
  let αr : DerivedCategory.Q ⋙ (r.left ⋙ x) ⟶
      onComplex o.pull ⋙ onComplex (restriction aX) ⋙ DerivedCategory.Q := αr₀ ≫ βr
  have hαr : (r.left ⋙ x).IsLeftDerivedFunctor αr
      (HomologicalComplex.quasiIso (modules RY) (.up ℤ)) := by
    have := hrpost x
    have := Functor.IsLeftDerivedFunctor.isRightKanExtension (r.left ⋙ x) αr₀
      (HomologicalComplex.quasiIso (modules RY) (.up ℤ))
    refine ⟨(Functor.isRightKanExtension_iff_of_iso₂ αr₀ αr
      (Functor.isoWhiskerLeft (onComplex o.pull) xf) (Iso.refl _) ?_).1 inferInstance⟩
    ext P
    change 𝟙 _ ≫ αr.app P = _
    rw [Category.id_comp]
    rfl
  let := hαr
  let τ₀ : DerivedCategory.Q ⋙ (y ⋙ a.left) ⟶
      onComplex o.pull ⋙ onComplex (restriction aX) ⋙ DerivedCategory.Q :=
    { app := fun P ↦ a.left.map (yf.hom.app P) ≫
        a.epsilon.app ((onComplex (restriction aY)).obj P) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex o.scalarUnit (.up ℤ)).app P)
      naturality := by
        intro P P' f
        dsimp only [Functor.comp_map]
        have h₁ := yf.hom.naturality f
        have h₂ := a.epsilon.naturality ((onComplex (restriction aY)).map f)
        have h₃ := (NatTrans.mapHomologicalComplex o.scalarUnit (.up ℤ)).naturality f
        dsimp only [Functor.comp_map] at h₁ h₂ h₃
        calc
          _ = a.left.map (yf.hom.app P ≫
              DerivedCategory.Q.map ((onComplex (restriction aY)).map f)) ≫
              a.epsilon.app ((onComplex (restriction aY)).obj P') ≫
                DerivedCategory.Q.map
                  ((NatTrans.mapHomologicalComplex o.scalarUnit (.up ℤ)).app P') := by
            rw [← Functor.map_comp_assoc, h₁]
          _ = _ := by
            simp only [Functor.map_comp, Category.assoc]
            erw [reassoc_of% h₂]
            rw [← DerivedCategory.Q.map_comp]
            erw [h₃]
            rw [DerivedCategory.Q.map_comp]
            rfl
    }
  let τ := (r.left ⋙ x).leftDerivedLift αr
    (HomologicalComplex.quasiIso (modules RY) (.up ℤ)) (y ⋙ a.left) τ₀
  have hτ (P : CochainComplex (modules RY) ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫ x.map (r.epsilon.app P) ≫
          xf.hom.app ((onComplex o.pull).obj P) =
        a.left.map (yf.hom.app P) ≫
          a.epsilon.app ((onComplex (restriction aY)).obj P) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex o.scalarUnit (.up ℤ)).app P) := by
    simpa only [τ, αr, αr₀, βr, τ₀, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.id_comp, Category.assoc] using
        (r.left ⋙ x).leftDerived_fac_app αr
          (HomologicalComplex.quasiIso (modules RY) (.up ℤ)) (y ⋙ a.left) τ₀ P
  -- Restriction of a K-injective need not be K-injective, but is pushA-acyclic.
  have hacyclic (I : CochainComplex (modules RX) ℤ) (hI : I.IsKInjective)
      (T : CochainComplex (modules (constantRing JX A)) ℤ) (hT : T.IsKInjective)
      (j : (onComplex (restriction aX)).obj I ⟶ T) [QuasiIso j] :
      QuasiIso ((onComplex o.pushA).map j) := by
    obtain ⟨EX, heX, hmX, haddX, hinvX, _⟩ :=
      SheafOfModules.derivedChangeOfRingsIndependentCoefficients aX
    let := haddX
    obtain ⟨_, _, hoX⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction aX
    obtain ⟨adjX, _⟩ := hoX EX heX hmX
    let PB : ObjectProperty (HomotopyCategory (modules (constantRing JX A)) (.up ℤ)) :=
      fun K ↦ CochainComplex.IsKFlatIndependentCoefficients
        (J := JX) (R := constantRing JX A) K.as
    let PE := goodComplex (constantRing JY A)
    have hresB (K : HomotopyCategory (modules (constantRing JX A)) (.up ℤ)) :
        ∃ P s, PB P ∧ IsIso (DerivedCategory.Qh.map (s : P ⟶ K)) := by
      obtain ⟨P, s, hp, hs⟩ := goodComplex_resolutions (constantRing JX A) K
      exact ⟨P, s, hp.1, Localization.inverts DerivedCategory.Qh _ _ hs⟩
    have hresE (K : HomotopyCategory (modules (constantRing JY A)) (.up ℤ)) :
        ∃ P s, PE P ∧ IsIso (DerivedCategory.Qh.map (s : P ⟶ K)) := by
      obtain ⟨P, s, hp, hs⟩ := goodComplex_resolutions (constantRing JY A) K
      exact ⟨P, s, hp, Localization.inverts DerivedCategory.Qh _ _ hs⟩
    have hinvf {K K'} (hK : PB K) (hK' : PB K') (s : K ⟶ K')
        (hs : IsIso (DerivedCategory.Qh.map s)) :
        IsIso (DerivedCategory.Qh.map ((EX.mapHomotopyCategory (.up ℤ)).map s)) := by
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      obtain ⟨K', rfl⟩ := HomotopyCategory.quotient_obj_surjective K'
      obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
      have hq : QuasiIso s := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1
        ((DerivedCategory.isIso_Qh_map_iff _).1 hs)
      have ht := hinvX s hK hK' hq
      rw [Functor.mapHomotopyCategory_map]
      exact Localization.inverts DerivedCategory.Qh _ _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
    have hinvg {K K'} (_ : PE K) (_ : PE K') (s : K ⟶ K')
        (hs : IsIso (DerivedCategory.Qh.map s)) :
        IsIso (DerivedCategory.Qh.map ((IA.modules.mapHomotopyCategory (.up ℤ)).map s)) := by
      have hn := IA.modules.mapDerivedCategoryFactorsh.hom.naturality s
      dsimp only [Functor.comp_map] at hn
      have : IsIso (IA.modules.mapDerivedCategory.map (DerivedCategory.Qh.map s)) :=
        IA.modules.mapDerivedCategory.map_isIso _
      have : IsIso (IA.modules.mapDerivedCategoryFactorsh.hom.app K ≫
          DerivedCategory.Qh.map ((IA.modules.mapHomotopyCategory (.up ℤ)).map s)) := by
        rw [← hn]
        infer_instance
      exact IsIso.of_isIso_comp_left
        (IA.modules.mapDerivedCategoryFactorsh.hom.app K) _
    have hgood (K) (hK : PE K) : PB ((IA.modules.mapHomotopyCategory (.up ℤ)).obj K) := by
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      exact SheafOfModules.kFlat_inverseImage_independent inverse direct geom IA K hK.1 hK.2
    let := hI
    let := hT
    have hiso : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map j)) := by
      apply (DerivedCategory.isIso_Qh_map_iff _).2
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (inferInstance : QuasiIso j)
    have hm := CategoryTheory.isIso_map_of_adjoints
      (adjX.mapHomotopyCategory (.up ℤ)) (o.adjA.mapHomotopyCategory (.up ℤ))
      (HomotopyCategory.quasiIso (modules (constantRing JX A)) (.up ℤ))
      (HomotopyCategory.quasiIso (modules (constantRing JY A)) (.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh PB PE hresB hresE
      hinvf hinvg hgood ((HomotopyCategory.quotient _ _).obj I)
      (fun K ↦ CochainComplex.IsKInjective.Qh_map_bijective K I)
      ((HomotopyCategory.quotient _ _).obj T)
      (fun K ↦ CochainComplex.IsKInjective.Qh_map_bijective K T)
      ((HomotopyCategory.quotient _ _).map j)
    have hq := (DerivedCategory.isIso_Qh_map_iff _).1 hm
    rw [Functor.mapHomotopyCategory_map] at hq
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 hq
  have hAη (I : CochainComplex (modules RX) ℤ) (hI : I.IsKInjective) :
      IsIso (a.eta.app ((onComplex (restriction aX)).obj I)) := by
    obtain ⟨T, hT, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      ((onComplex (restriction aX)).obj I)
    have : QuasiIso j := hj
    have : QuasiIso ((onComplex o.pushA).map j) := hacyclic I hI T hT j
    have : IsIso (a.eta.app T) := a.onInjective T hT
    have hn := a.eta.naturality j
    dsimp only [Functor.comp_map] at hn
    have : IsIso (a.eta.app ((onComplex (restriction aX)).obj I) ≫
        a.right.map (DerivedCategory.Q.map j)) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (a.right.map (DerivedCategory.Q.map j))
  -- Compare the two right-derived presentations of the ordinary composite.
  let F := o.pushR ⋙ restriction aY
  let κc := NatTrans.mapHomologicalComplex o.ordinaryKappa.hom (.up ℤ)
  let δr : onComplex F ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ (r.right ⋙ y) :=
    { app := fun K ↦ yf.inv.app ((onComplex o.pushR).obj K) ≫ y.map (r.eta.app K)
      naturality := by
        intro K K' f
        dsimp only [Functor.comp_map]
        have hn := yf.inv.naturality ((onComplex o.pushR).map f)
        have hm := r.eta.naturality f
        dsimp only [Functor.comp_map] at hn hm
        change DerivedCategory.Q.map ((onComplex (restriction aY)).map
            ((onComplex o.pushR).map f)) ≫
            (yf.inv.app ((onComplex o.pushR).obj K') ≫ y.map (r.eta.app K')) = _
        rw [← Category.assoc, hn, Category.assoc, ← y.map_comp, hm, y.map_comp]
        simp only [Category.assoc] }
  let δa : onComplex F ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ (x ⋙ a.right) :=
    { app := fun K ↦ DerivedCategory.Q.map (κc.app K) ≫
        a.eta.app ((onComplex (restriction aX)).obj K) ≫ a.right.map (xf.inv.app K)
      naturality := by
        intro K K' f
        dsimp only [Functor.comp_map]
        have h₁ := κc.naturality f
        have h₂ := a.eta.naturality ((onComplex (restriction aX)).map f)
        have h₃ := xf.inv.naturality f
        dsimp only [Functor.comp_map] at h₁ h₂ h₃
        rw [← Category.assoc, ← Category.assoc, ← DerivedCategory.Q.map_comp, h₁,
          DerivedCategory.Q.map_comp]
        simp only [Category.assoc]
        erw [reassoc_of% h₂]
        have h₃' := a.right.congr_map h₃
        simp only [Functor.map_comp] at h₃'
        exact congrArg (fun t ↦ DerivedCategory.Q.map (κc.app K) ≫
          a.eta.app ((onComplex (restriction aX)).obj K) ≫ t) h₃' }
  have hδr : (r.right ⋙ y).IsRightDerivedFunctor δr
      (HomologicalComplex.quasiIso (modules RX) (.up ℤ)) := by
    apply (CategoryTheory.derives F).isRightDerivedFunctor_of_isIso δr
    intro I
    have : IsIso (r.eta.app I.obj) := r.onInjective I.obj I.property
    change IsIso (yf.inv.app ((onComplex o.pushR).obj I.obj) ≫ y.map (r.eta.app I.obj))
    infer_instance
  have hδa : (x ⋙ a.right).IsRightDerivedFunctor δa
      (HomologicalComplex.quasiIso (modules RX) (.up ℤ)) := by
    apply (CategoryTheory.derives F).isRightDerivedFunctor_of_isIso δa
    intro I
    have : IsIso (a.eta.app ((onComplex (restriction aX)).obj I.obj)) := hAη I.obj I.property
    have : IsIso (κc.app I.obj) := by
      change IsIso ((NatIso.mapHomologicalComplex o.ordinaryKappa (.up ℤ)).hom.app I.obj)
      infer_instance
    change IsIso (DerivedCategory.Q.map (κc.app I.obj) ≫
      a.eta.app ((onComplex (restriction aX)).obj I.obj) ≫ a.right.map (xf.inv.app I.obj))
    infer_instance
  let := hδr
  let := hδa
  let κ := Functor.rightDerivedUnique (r.right ⋙ y) (x ⋙ a.right) δr δa
    (HomologicalComplex.quasiIso (modules RX) (.up ℤ))
  have hκ (K : CochainComplex (modules RX) ℤ) :
      δr.app K ≫ κ.hom.app (DerivedCategory.Q.obj K) = δa.app K := by
    simpa only [κ, Functor.rightDerivedNatIso_hom, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app (r.right ⋙ y) (x ⋙ a.right) δr δa
        (HomologicalComplex.quasiIso (modules RX) (.up ℤ)) (𝟙 _) K
  have hκformula (I : CochainComplex (modules RX) ℤ) (_ : I.IsKInjective)
      (T : CochainComplex (modules (constantRing JX A)) ℤ) (_ : T.IsKInjective)
      (j : (onComplex (restriction aX)).obj I ⟶ T) [QuasiIso j] :
      yf.inv.app ((onComplex o.pushR).obj I) ≫ y.map (r.eta.app I) ≫
          κ.hom.app (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map (κc.app I) ≫
          DerivedCategory.Q.map ((onComplex o.pushA).map j) ≫ a.eta.app T ≫
            a.right.map (inv (DerivedCategory.Q.map j) ≫ xf.inv.app I) := by
    have hn := a.eta.naturality j
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc (yf.inv.app _), hκ]
    change DerivedCategory.Q.map (κc.app I) ≫
      a.eta.app ((onComplex (restriction aX)).obj I) ≫ a.right.map (xf.inv.app I) = _
    rw [a.right.map_comp, ← Category.assoc (DerivedCategory.Q.map ((onComplex o.pushA).map j)),
      hn]
    simp only [Category.assoc, ← a.right.map_comp, IsIso.hom_inv_id_assoc]
  refine ⟨{
    exactness := ⟨hxL, hxC, hyL, hyC⟩
    r := r
    a := a
    exactA := hexactA
    x := x
    y := y
    xFactors := (restriction aX).mapDerivedCategoryFactors
    yFactors := (restriction aY).mapDerivedCategoryFactors
    flatComparison := hflat
    tau := τ
    tauFormula := fun P _ _ ↦ hτ P
    kappa := κ
    kappaFormula := hκformula
  }⟩

end CategoryTheory.RingedCoefficientCounit
