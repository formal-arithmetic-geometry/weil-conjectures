/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSiteLimits
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Comma.Over.Basic
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverExistence
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
import WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverStep
import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtension
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionBase
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Data.Finite.Sigma
import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionConstruction
import WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentComposition
import WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentOperators
import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionSplit
import Mathlib.Data.Finite.Sum
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleQcAffineContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverWeak
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedBelowSectionModel
import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplexSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverQuasiIso
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Algebra.Homology.ComplexExtensionColimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import WeilConjectures.Algebra.Homology.BoundedBelowTotalComparison
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverRowComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverAugmentation
import WeilConjectures.Algebra.Homology.BoundedBelowAugmentation
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.CondensedHypercoverInjectiveRow
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentation
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Exact.Basic
import WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentationRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.CategoryTheory.RingedHypercoverFiniteCones
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Fin.VecNotation
import WeilConjectures.AlgebraicGeometry.ProEtaleHypercoverLocalLifting
import WeilConjectures.AlgebraicGeometry.ProEtaleRepresentableEpiLocalLifting
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardLocalComparison
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.CondensedHypercoverComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuity

/-!
# Continuity of ordinary condensed-coefficient pushforward

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
-/

@[expose] public section

universe u v w x y z

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj


namespace AlgebraicGeometry.ProEtale

/-- Naturality in the strict diagram, including the specified map of truncated colimits.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
Proof: precompose both sides with each colimit inclusion. Functoriality of good
truncation and naturality of its projection identify the resulting maps. The colimit
universal property gives equality. -/
theorem condensedContinuityComparison_naturality
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] (D E : I ⥤ CochainComplex A ℤ) (α : D ⟶ E)
    (a : ℤ) (T : CochainComplex A ℤ ⥤ B)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (E ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] [HasColimit (E ⋙ T)] :
    colimMap (Functor.whiskerRight α T) ≫ condensedContinuityComparison E a T =
      condensedContinuityComparison D a T ≫
        T.map (colimMap (Functor.whiskerRight α
          ((ComplexShape.embeddingUpIntGE a).truncGEFunctor A))) := by
  apply colimit.hom_ext
  intro i
  simp only [condensedContinuityComparison, colimit.ι_desc_assoc]
  rw [colimit.map_desc, colimit.ι_desc]
  dsimp [condensedContinuityCocone]
  rw [← T.map_comp, ← T.map_comp]
  congr 1
  rw [Category.assoc]
  have hnat := ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A).naturality
    (α.app i)
  dsimp at hnat
  rw [← Category.assoc, hnat, Category.assoc]
  congr 1
  exact (ι_colimMap
    (Functor.whiskerRight α ((ComplexShape.embeddingUpIntGE a).truncGEFunctor A)) i).symm

/-- The canonical comparison respects natural transformations of the output functor.
Together with the shifted cocone statements below, this specifies the comparison under
the usual derived shift and cohomology identifications.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
Proof: precompose with every colimit inclusion and use naturality at the corresponding
map to the truncated colimit. The colimit universal property identifies the maps. -/
theorem condensedContinuityComparison_functor_naturality
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (T S : CochainComplex A ℤ ⥤ B) (β : T ⟶ S)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] [HasColimit (D ⋙ S)] :
    colimMap (Functor.whiskerLeft D β) ≫ condensedContinuityComparison D a S =
      condensedContinuityComparison D a T ≫ β.app (condensedContinuityCocone D a).pt := by
  apply colimit.hom_ext
  intro i
  simp only [condensedContinuityComparison, colimit.ι_desc_assoc]
  rw [colimit.map_desc, colimit.ι_desc]
  dsimp [condensedContinuityCocone]
  rw [← β.naturality]

private theorem isIso_of_weaklyContractible_sections (X : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}} (f : M ⟶ N)
    (hf : ∀ (V : X.ProEt), IsAffine V.left →
      (∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (g : F ⟶ G),
        Epi g → Function.Surjective (g.hom.app (Opposite.op V))) →
      IsIso (f.hom.app (Opposite.op V))) : IsIso f := by
  have hinj (V : X.ProEtᵒᵖ) : Function.Injective (f.hom.app V) := by
    intro x y hxy
    obtain ⟨I, W, g, hcov, haff, hweak⟩ :=
      Scheme.ProEt.exists_affine_weaklyContractible_covering_family X V.unop
    have hcover : Sieve.ofArrows W g ∈ Scheme.ProEt.topology X V.unop :=
      Precoverage.generate_mem_toGrothendieck hcov
    apply Sheaf.isSeparated M V.unop _ hcover x y
    rintro Z h ⟨_, b, _, ⟨i⟩, rfl⟩
    have := hf (W i) (haff i) (hweak i)
    have hi : Function.Injective (f.hom.app (Opposite.op (W i))) :=
      (AddCommGrpCat.mono_iff_injective _).1 inferInstance
    have heq : M.obj.map (g i).op x = M.obj.map (g i).op y := by
      apply hi
      rw [f.hom.naturality_apply, f.hom.naturality_apply, hxy]
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, heq]
  have hsurj : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) f.hom := by
    constructor
    intro V x
    obtain ⟨I, W, g, hcov, haff, hweak⟩ :=
      Scheme.ProEt.exists_affine_weaklyContractible_covering_family X V
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hcov)
    rintro Z h ⟨_, b, _, ⟨i⟩, rfl⟩
    have := hf (W i) (haff i) (hweak i)
    have hs : Function.Surjective (f.hom.app (Opposite.op (W i))) :=
      (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
    obtain ⟨y, hy⟩ := hs (N.obj.map (g i).op x)
    refine ⟨M.obj.map b.op y, ?_⟩
    rw [f.hom.naturality_apply, hy, op_comp, Functor.map_comp]
    rfl
  apply (Sheaf.isLocallyBijective_iff_isIso f).1
  exact ⟨(Sheaf.isLocallyInjective_iff_injective f).2 hinj, hsurj⟩


set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
private theorem comparison_isIso_of_bounded_model
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (T H : CochainComplex A ℤ ⥤ B)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] [HasColimitsOfShape I A]
    [PreservesColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A) H]
    (hπ : ∀ i, IsIso (T.map ((D.obj i).πTruncGE a)))
    (e : ∀ (K : CochainComplex A ℤ) (_ : K.IsStrictlyGE a), T.obj K ≅ H.obj K)
    (he : ∀ (K L : CochainComplex A ℤ) (hK : K.IsStrictlyGE a)
      (hL : L.IsStrictlyGE a) (f : K ⟶ L),
      T.map f ≫ (e L hL).hom = (e K hK).hom ≫ H.map f) :
    IsIso (condensedContinuityComparison D a T) := by
  let E : I ⥤ CochainComplex A ℤ :=
    D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A
  let c := colimit.cocone E
  have hE (i : I) : (E.obj i).IsStrictlyGE a := by
    change ((D.obj i).truncGE a).IsStrictlyGE a
    infer_instance
  have hc : CochainComplex.IsStrictlyGE c.pt a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) n)
      (colimit.isColimit E)).isZero_pt
        (Functor.isZero _ fun i ↦ (E.obj i).isZero_of_isStrictlyGE a n hn)
  let η : D ⋙ T ⟶ E ⋙ H :=
    Functor.whiskerRight (Functor.whiskerLeft D
      ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)) T ≫
      { app := fun i ↦ (e (E.obj i) (hE i)).hom
        naturality := fun i j f ↦ by
          change T.map (E.map f) ≫ (e (E.obj j) (hE j)).hom =
            (e (E.obj i) (hE i)).hom ≫ H.map (E.map f)
          exact he (E.obj i) (E.obj j) (hE i) (hE j) (E.map f) }
  have hη (i : I) : IsIso (η.app i) := by
    have := hπ i
    dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    change IsIso (T.map ((D.obj i).πTruncGE a) ≫ (e (E.obj i) (hE i)).hom)
    infer_instance
  have : IsIso η := NatIso.isIso_of_isIso_app η
  have hcolim : IsColimit (H.mapCocone c) :=
    isColimitOfPreserves H (colimit.isColimit E)
  let k := colimit.desc (D ⋙ T)
    ((Cocone.precompose η).obj (H.mapCocone c))
  have hk : IsIso k := by
    have hcolim' : IsColimit ((Cocone.precompose η).obj (H.mapCocone c)) :=
      (IsColimit.precomposeHomEquiv (asIso η) (H.mapCocone c)).symm hcolim
    exact (colimit.isColimit (D ⋙ T)).coconePointUniqueUpToIso hcolim' |>.isIso_hom
  have heq : condensedContinuityComparison D a T ≫ (e c.pt hc).hom = k := by
    apply colimit.hom_ext
    intro i
    simp only [condensedContinuityComparison, colimit.ι_desc_assoc]
    rw [colimit.ι_desc]
    change T.map ((D.obj i).πTruncGE a ≫ c.ι.app i) ≫ (e c.pt hc).hom =
      (T.map ((D.obj i).πTruncGE a) ≫ (e (E.obj i) (hE i)).hom) ≫ H.map (c.ι.app i)
    rw [T.map_comp, Category.assoc, he _ _ (hE i) hc, Category.assoc]
  have : IsIso (condensedContinuityComparison D a T ≫ (e c.pt hc).hom) := by
    rw [heq]
    exact hk
  exact IsIso.of_isIso_comp_right _ (e c.pt hc).hom

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
set_option backward.isDefEq.respectTransparency false in
private theorem condensedContinuityComparison_isIso_of_iso
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] [IsConnected I]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (T S : CochainComplex A ℤ ⥤ B) (e : T ≅ S)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] [HasColimit (D ⋙ S)]
    (h : IsIso (condensedContinuityComparison D a S)) :
    IsIso (colimMap ((T.mapCocone (condensedContinuityCocone D a)).ι)) := by
  have := h
  have hf := condensedContinuityComparison_functor_naturality D a T S e.hom
  have : IsIso (condensedContinuityComparison D a T ≫
      e.hom.app (condensedContinuityCocone D a).pt) := by
    rw [← hf]
    infer_instance
  have ht : IsIso (condensedContinuityComparison D a T) :=
    IsIso.of_isIso_comp_right _ (e.hom.app (condensedContinuityCocone D a).pt)
  have hc : IsColimit (T.mapCocone (condensedContinuityCocone D a)) :=
    IsColimit.ofPointIso (colimit.isColimit (D ⋙ T)) (i := ht)
  exact hc.isIso_colimMap_ι

private noncomputable def condensedContinuityShiftIso
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u} [Category.{z} B] [Abelian B] [HasDerivedCategory.{z} B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] (s q : ℤ) :
    shiftFunctor _ s ⋙ (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q) ≅
      DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B (s + q) :=
  Functor.isoWhiskerRight ((DerivedCategory.Q ⋙ F).commShiftIso s)
      (DerivedCategory.homologyFunctor B q) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Q ⋙ F)
      ((DerivedCategory.homologyFunctor B 0).shiftIso s q (s + q) rfl)

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- Compatibility of pushforward continuity with every integral shift. The shifted
cocone has exactly the shifts of the original cocone legs; its vertex is the shift of
Q(colim τ≥a D). Under the standard shift comparisons its universal colimit map is thus
the shifted original comparison, with lower bound a-s and cohomology degree q+s.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity-shift-colimMap).
Proof: commutation of Q and the right derived functor with shifts, followed by
the homology shift isomorphism, identifies the shifted output functor with the
unshifted output functor in degree s+q. Naturality of the continuity comparison
transports invertibility from the unshifted theorem. Its mapped cocone is therefore
colimiting. Since the filtered indexing category is connected, colimMap of the
cocone legs is an isomorphism. -/
theorem condensed_qcqs_pushforward_continuity_shift_colimMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (s q : ℤ) :
    IsIso (colimMap (((DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((shiftFunctor _ s).mapCocone (condensedContinuityCocone D a))).ι)) := by
  let _ : IsConnected I := IsFiltered.isConnected I
  exact condensedContinuityComparison_isIso_of_iso D a _ _
    (condensedContinuityShiftIso (CondensedRing.lowerStar Λ f).rightDerivedFunctor s q)
    (condensed_qcqs_pushforward_continuity Λ f D a ha (s + q))

set_option synthInstance.maxHeartbeats 100000 in
-- Needed for colimit inference in the internal module category.
set_option synthInstance.maxSize 4096 in
theorem condensed_qcqs_pushforward_continuity_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (s q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((shiftFunctor _ s).mapCocone (condensedContinuityCocone D a)))) := by
  let _ : IsConnected I := IsFiltered.isConnected I
  apply (Cocone.isColimit_iff_isIso_colimMap_ι _).2
  exact condensed_qcqs_pushforward_continuity_shift_colimMap Λ f D a ha s q

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- Compatibility of derived global sections continuity with every integral shift. The shifted
cocone has exactly the shifts of the original cocone legs; its vertex is the shift of
Q(colim τ≥a D). Under the standard shift comparisons its universal colimit map is thus
the shifted original comparison, with lower bound a-s and cohomology degree q+s.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity-global-shift-colimMap).
Proof: commutation of Q and the right derived functor with shifts, followed by
the homology shift isomorphism, identifies the shifted output functor with the
unshifted output functor in degree s+q. Naturality of the continuity comparison
transports invertibility from the unshifted theorem. Its mapped cocone is therefore
colimiting. Since the filtered indexing category is connected, colimMap of the
cocone legs is an isomorphism. -/
theorem condensed_qcqs_globalSections_continuity_shift_colimMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (s q : ℤ) :
    IsIso (colimMap (((DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((shiftFunctor _ s).mapCocone (condensedContinuityCocone D a))).ι)) := by
  let _ : IsConnected I := IsFiltered.isConnected I
  exact condensedContinuityComparison_isIso_of_iso D a _ _
    (condensedContinuityShiftIso (condensedModuleSections Λ X).rightDerivedFunctor s q)
    (condensed_qcqs_globalSections_continuity Λ X D a ha (s + q))

set_option synthInstance.maxHeartbeats 100000 in
-- Needed for colimit inference in the internal module category.
set_option synthInstance.maxSize 4096 in
theorem condensed_qcqs_globalSections_continuity_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (s q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((shiftFunctor _ s).mapCocone (condensedContinuityCocone D a)))) := by
  let _ : IsConnected I := IsFiltered.isConnected I
  apply (Cocone.isColimit_iff_isIso_colimMap_ι _).2
  exact condensed_qcqs_globalSections_continuity_shift_colimMap Λ X D a ha s q

end AlgebraicGeometry.ProEtale
