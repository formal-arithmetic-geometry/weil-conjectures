/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RingedDerivedComparisonData
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModelSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.PullbackTensorCanonicalShiftUnit
public import WeilConjectures.Algebra.Homology.RingedKFlatWordComparisonDescent

import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.AlgebraicGeometry.DerivedResolvingPairRestriction
import WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
import WeilConjectures.AlgebraicGeometry.CochainPullbackTensorShift
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.AlgebraicGeometry.NormalizedCoefficientTensorSquare
import WeilConjectures.AlgebraicGeometry.NormalizedCochainTensorDiagrams
import WeilConjectures.AlgebraicGeometry.FiniteTensorComparisonProofSupport

/-! # Simultaneous normalization of derived tensor pullback and coefficient change

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E;
ordinary balanced chain comparisons and the coefficient square in the DAG proof
(blueprint: lem-pur-finite-derived-comparison-normalization).

The site presentations, signed total tensor, normalized ordinary comparisons and
module categories are existing ones. The helpers below package the universal
left-derived counit and its representative equation. No tensor comparison or coherence equation is
assumed of a derived pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open CategoryTheory.CochainPullback CategoryTheory.RingedDerivedComparisons
open WeilConjectures

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 100000] HomologicalComplex.monoidalCategoryStruct
attribute [local irreducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
  SheafOfModules.instCategory HomologicalComplex.instCategory
  SheafOfModules.monoidalCategory SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.IsFlatOnSite
  SheafOfModules.siteSheafTensorRight
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplex
  HomologicalComplex.mapBifunctorMap
  CategoryTheory.CochainPullback.compositionModule
  CategoryTheory.Functor.mapHomologicalComplexCompIso
  HomologicalComplex₂.total CategoryTheory.CochainPullback.comparison
  HomologicalComplex.single CategoryTheory.CochainPullback.extensionComparison
  SheafOfModules.PullbackTensorCanonical.canonicalDerivedTensor
  SheafOfModules.PullbackTensorCanonical.canonicalRepresentativeIso
  SheafOfModules.siteDerivedTensorIndependentCoefficients

namespace CategoryTheory.FiniteDerivedComparison

open CategoryTheory.FiniteTensorComparisonProofSupport

/-- The given total left-derived functor with its actual universal cochain counit.
Source: Stacks 06YY, 07A4
(blueprint: lem-pur-finite-derived-comparison-normalization). -/
structure Pullback
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
    (f : RingedPullback.{u, u, u, u, u} R S) where
  F : DerivedCategory (Modules.{u, u, u} R) ⥤ DerivedCategory (Modules.{u, u, u} S)
  epsilon : DerivedCategory.Q ⋙ F ⟶ CochainPullback.pull.{u, u, u, u, u} f ⋙ DerivedCategory.Q
  universal : F.IsLeftDerivedFunctor epsilon
    (HomologicalComplex.quasiIso (Modules.{u, u, u} R) (.up ℤ))

/-- The same ringed site in the published finite-word interface.
Source: Stacks 06YY and 0D6D
(blueprint: lem-pur-finite-derived-comparison-normalization). -/
def wordSite (X : Site.{u, w}) : RingedKFlatWord.Site.{u, u, u, w} where
  C := X.C
  J := X.J
  R := X.A

/-- The published flat-term K-flat predicate, on the same module category.
Source: Stacks 0G7E and 07A4
(blueprint: lem-pur-finite-derived-comparison-normalization). -/
abbrev Resolving (X : Site.{u, w}) (P : CochainPullback.Complex.{u, u, u} X.A) : Prop :=
  RingedKFlatWord.Resolving (wordSite X) P

/-- The canonical representative square, using the existing insertion-of-one chain map.
Its inverse is the scalar-contraction map in `comparison`; it is not a freely chosen iso.
Source: Stacks 07A4 and the balanced chain formula of the node
(blueprint: lem-pur-finite-derived-comparison-normalization). -/
def Normalized {X Y : Site.{u, w}} (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k :
  CochainPullback.Comparison.{u, u, u, u, u} f)
    (d : Pullback.{u, w} f) (nu : Y.closed.tensor ⋙ d.F ≅ (d.F.prod d.F) ⋙ X.closed.tensor) :
          Prop :=
  ∀ (P Q : CochainPullback.Complex.{u, u, u} Y.A) (hP : Resolving Y P) (hQ : Resolving Y Q),
    ∃ (hP' : Resolving X ((CochainPullback.pull.{u, u, u, u, u} f).obj P)) (hQ' : Resolving X
      ((CochainPullback.pull.{u, u, u, u, u} f).obj Q)),
      d.F.map (Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1).hom ≫
          nu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          X.closed.tensor.map (Prod.mkHom (d.epsilon.app P) (d.epsilon.app Q)) =
        d.epsilon.app (P ⊗ Q) ≫ DerivedCategory.Q.map (CochainPullback.comparison.{u, u, u, u, u} f
          k P Q).hom ≫
          (X.model.iso X.J X.A X.closed ((CochainPullback.pull.{u, u, u, u, u} f).obj P)
            ((CochainPullback.pull.{u, u, u, u, u} f).obj Q)
            hP'.1 hQ'.1).hom



section PrivateRepresentatives

attribute [local instance high] cachedTensorAdditive cachedTensorAdditiveObj
  cachedTensorLeftZero cachedTensorRightZero cachedGradedTensor cachedGradedFour
  cachedGradedLeft cachedGradedRight totalTensor_exists

private theorem resolving_pull {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (P : CochainPullback.Complex.{u, u, u} Y.A) (hP : Resolving Y P) :
    Resolving X ((CochainPullback.pull.{u, u, u, u, u} f).obj P) := by
  let := f.finiteLimits
  exact SheafOfModules.isKFlat_ringedToposPullback f.uInv f.uPush f.adj f.I
    f.coefficient f.L f.hobj f.hmap P hP.1 hP.2

private theorem resolving_tensor (X : Site.{u, w})
    (P Q : CochainPullback.Complex.{u, u, u} X.A) (hP : Resolving X P) (hQ : Resolving X Q) :
    Resolving X (P ⊗ Q) := by
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    X.A P Q hP.1 hQ.1 hP.2 hQ.2
  exact ⟨h.1, h.2.1⟩

private theorem resolving_resolution (X : Site.{u, w}) (K : CochainPullback.Complex.{u, u, u} X.A) :
    ∃ (P : CochainPullback.Complex.{u, u, u} X.A) (a : P ⟶ K), Resolving X P ∧ QuasiIso a := by
  obtain ⟨P, a, hp, hf, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  refine ⟨P, a, ⟨hp, ?_⟩, ha⟩
  intro n
  unfold SheafOfModules.IsFlatOnSite
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso X.A (P.X n)).symm (hf n)

private theorem resolving_fullyFaithful (X Y : Site.{u, w}) :
    let P : ObjectProperty (CochainPullback.Complex.{u, u, u} X.A) := Resolving X
    Nonempty (((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (X.D × X.D) Y.D).obj
        ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  exact derivedResolvingPairRestriction Y.D (Resolving X) (resolving_resolution X)

private def resolving_model (X : Site.{u, w}) :
    let P : ObjectProperty (CochainPullback.Complex.{u, u, u} X.A) := Resolving X
    (P.ι.prod P.ι) ⋙ coefficientTotalTensor.{u, u, u} X.J X.A ⋙ DerivedCategory.Q ≅
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙ X.closed.tensor :=
  let P : ObjectProperty (CochainPullback.Complex.{u, u, u} X.A) := Resolving X
  let i : P.FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := X.J) (R := X.A)) :=
    { obj := fun K ↦ ⟨K.obj, K.property.1⟩
      map := fun a ↦ ObjectProperty.homMk a.hom }
  isoWhiskerLeft (i.prod i) X.model.comparison


private theorem resolving_model_hom_app (X : Site.{u, w})
    (P Q : CochainPullback.Complex.{u, u, u} X.A)
    (hP : Resolving X P) (hQ : Resolving X Q) :
    (resolving_model X).hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
      (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom := rfl

attribute [local irreducible] resolving_model cochain_comparison

end PrivateRepresentatives

attribute [local irreducible] resolving_model cochain_comparison

/-- Existence and uniqueness of the canonical bifunctorial comparison, together with
closure of the resolving class under the total tensor and its pullback.
Source: Stacks 07A4 and 0G7E
(blueprint: lem-pur-finite-derived-comparison-normalization).

Proof: K-flat total-tensor closure and preservation under pullback give the first
clause. Flat-term K-flat resolutions and fully faithful restriction along their
homotopy localization give fully faithful restriction on bifunctor categories.
The site's existing tensor model restricts to these representatives. Uncurry the
natural cochain comparison and use the universal pullback computation on resolving
complexes and their total tensors. The representative-descent theorem gives a
unique natural isomorphism. Its square is exactly Normalized; proof irrelevance
identifies the possibly different resolving witnesses in its uniqueness clause. -/
theorem finiteDerivedComparisonNormalization {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : CochainPullback.Comparison.{u, u, u, u, u} f)
      (d : Pullback.{u, w} f) :
    (∀ (P Q : CochainPullback.Complex.{u, u, u} Y.A), Resolving Y P → Resolving Y Q →
      Resolving Y (P ⊗ Q) ∧ Resolving X ((CochainPullback.pull.{u, u, u, u, u} f).obj (P ⊗ Q))) ∧
    ∃! nu : Y.closed.tensor ⋙ d.F ≅ (d.F.prod d.F) ⋙ X.closed.tensor,
      Normalized f k d nu := by
  have := cachedTensorAdditive X.A
  have := cachedTensorAdditiveObj X.A
  have := cachedTensorLeftZero X.A
  have := cachedTensorRightZero X.A
  have := cachedGradedTensor X.A
  have := cachedGradedFour X.A
  have := cachedGradedLeft X.A
  have := cachedGradedRight X.A
  have := cachedTensorAdditive Y.A
  have := cachedTensorAdditiveObj Y.A
  have := cachedTensorLeftZero Y.A
  have := cachedTensorRightZero Y.A
  have := cachedGradedTensor Y.A
  have := cachedGradedFour Y.A
  have := cachedGradedLeft Y.A
  have := cachedGradedRight Y.A
  have he (P : CochainPullback.Complex.{u, u, u} Y.A) (hP : Resolving Y P) :
      IsIso (d.epsilon.app P) :=
    SheafOfModules.PullbackTensorResolving.pullback_resolving_computation.{u, u, u, u, u, w, w}
      f d.F d.epsilon d.universal P hP.1 hP.2
  obtain ⟨ff⟩ := resolving_fullyFaithful Y X
  obtain ⟨nu, hn, hu⟩ := tensorComparisonDescent
    (K := CochainPullback.Complex.{u, u, u} Y.A)
    (H := CochainPullback.Complex.{u, u, u} X.A) (D := Y.D) (E := X.D)
    DerivedCategory.Q DerivedCategory.Q
    (CochainPullback.pull.{u, u, u, u, u} f) d.F d.epsilon
    (Resolving Y) (Resolving X) (resolving_pull f) ff
    (coefficientTotalTensor.{u, u, u} Y.J Y.A) (coefficientTotalTensor.{u, u, u} X.J X.A)
    Y.closed.tensor X.closed.tensor (resolving_model Y) (resolving_model X)
    (cochain_comparison f k) he
    (fun P Q hP hQ ↦ he _ (resolving_tensor Y P Q hP hQ))
  refine ⟨fun P Q hP hQ ↦ ⟨resolving_tensor Y P Q hP hQ,
    resolving_pull f _ (resolving_tensor Y P Q hP hQ)⟩, nu, ?_, ?_⟩
  · intro P Q hP hQ
    refine ⟨resolving_pull f P hP, resolving_pull f Q hQ, ?_⟩
    have hh := hn P Q hP hQ
    with_unfolding_all exact hh
  · intro other ho
    apply hu other
    intro P Q hP hQ
    have hh := ho P Q hP hQ
    rcases hh with ⟨hp, hq, h⟩
    with_unfolding_all exact h

/-- The uniquely determined comparison of Tag 07A4, extracted from its representative
characterization. Choice is from unique data, rather than from a bare existence statement.
Source: Stacks 07A4
(blueprint: lem-pur-finite-derived-comparison-normalization). -/
def tensorComparison {X Y : Site.{u, w}} (f : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (k : CochainPullback.Comparison.{u, u, u, u, u} f) (d : Pullback.{u, w} f) :
    Y.closed.tensor ⋙ d.F ≅ (d.F.prod d.F) ⋙ X.closed.tensor :=
  Classical.choose (finiteDerivedComparisonNormalization f k d).2

attribute [local irreducible] tensorComparison
  SheafOfModules.RingedTensorEdge.tensorComparison
  SheafOfModules.ringedTopoiCanonicalDerivedTensorComparison

attribute [local semireducible] SheafOfModules.monoidalCategory

/-- The ordinary action-unit comparison, localized with the actual derived counit.
Source: Stacks 03EL, 07A4
(blueprint: lem-pur-finite-derived-comparison-normalization). -/
def unitMap {X Y : Site.{u, w}} (f : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (k : CochainPullback.Comparison.{u, u, u, u, u} f) (d : Pullback.{u, w} f) :
    d.F.obj Y.closed.monoidal.tensorUnit ⟶ X.closed.monoidal.tensorUnit :=
  d.F.map Y.coherence.unitIso.hom ≫
    d.epsilon.app (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
    DerivedCategory.Q.map (CochainPullback.unit.{u, u, u, u, u} f k).hom ≫
    X.coherence.unitIso.inv

attribute [local irreducible] SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section PrivateTensorSquares

attribute [local instance high] cachedTensorAdditive cachedTensorAdditiveObj
  cachedTensorLeftZero cachedTensorRightZero cachedGradedTensor cachedGradedFour
  cachedGradedLeft cachedGradedRight totalTensor_exists

private theorem pullback_computes {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (d : Pullback.{u, w} f)
    (P : CochainPullback.Complex.{u, u, u} Y.A) (hP : Resolving Y P) :
    IsIso (d.epsilon.app P) :=
  SheafOfModules.PullbackTensorResolving.pullback_resolving_computation
    f d.F d.epsilon d.universal P hP.1 hP.2

private theorem tensorComparison_normalized {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (k : CochainPullback.Comparison.{u, u, u, u, u} f) (d : Pullback.{u, w} f) :
    Normalized f k d (tensorComparison f k d) := by
  unfold tensorComparison
  exact (Classical.choose_spec (finiteDerivedComparisonNormalization f k d).2).1

private theorem tensorComparison_model_square {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (k : CochainPullback.Comparison.{u, u, u, u, u} f) (d : Pullback.{u, w} f)
    (P Q : CochainPullback.Complex.{u, u, u} Y.A) (hP : Resolving Y P) (hQ : Resolving Y Q) :
    d.F.map (Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1).hom ≫
        (tensorComparison f k d).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        X.closed.tensor.map (Prod.mkHom (d.epsilon.app P) (d.epsilon.app Q)) =
      d.epsilon.app (P ⊗ Q) ≫
        DerivedCategory.Q.map (CochainPullback.comparison f k P Q).hom ≫
        (X.model.iso X.J X.A X.closed ((CochainPullback.pull f).obj P)
          ((CochainPullback.pull f).obj Q) (resolving_pull f P hP).1
          (resolving_pull f Q hQ).1).hom := by
  obtain ⟨_, _, hn⟩ := tensorComparison_normalized f k d P Q hP hQ
  exact hn



end PrivateTensorSquares

section CanonicalCoherence

attribute [local semireducible] CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.IsFlatOnSite

open CategoryTheory.FiniteDerivedTensorModels

private theorem normalized_coherence {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : CochainPullback.Comparison.{u, u, u, u, u} f)
      (d : Pullback.{u, w} f) :
    IsIso (unitMap f k d) ∧
    (∀ M N P : Y.D,
      (tensorComparison f k d).hom.app (Y.closed.tensor.obj (M, N), P) ≫
          X.closed.tensor.map (Prod.mkHom ((tensorComparison f k d).hom.app (M, N))
            (𝟙 (d.F.obj P))) ≫
          (X.closed.monoidal.associator (d.F.obj M) (d.F.obj N) (d.F.obj P)).hom =
        d.F.map (Y.closed.monoidal.associator M N P).hom ≫
          (tensorComparison f k d).hom.app (M, Y.closed.tensor.obj (N, P)) ≫
          X.closed.tensor.map (Prod.mkHom (𝟙 (d.F.obj M))
            ((tensorComparison f k d).hom.app (N, P)))) ∧
    (∀ M : Y.D,
      (tensorComparison f k d).hom.app (Y.closed.monoidal.tensorUnit, M) ≫
          X.closed.tensor.map (Prod.mkHom (unitMap f k d) (𝟙 (d.F.obj M))) ≫
          (X.closed.monoidal.leftUnitor (d.F.obj M)).hom =
        d.F.map (Y.closed.monoidal.leftUnitor M).hom) ∧
    (∀ M : Y.D,
      (tensorComparison f k d).hom.app (M, Y.closed.monoidal.tensorUnit) ≫
          X.closed.tensor.map (Prod.mkHom (𝟙 (d.F.obj M)) (unitMap f k d)) ≫
          (X.closed.monoidal.rightUnitor (d.F.obj M)).hom =
        d.F.map (Y.closed.monoidal.rightUnitor M).hom) ∧
    (∀ M N : Y.D,
      (tensorComparison f k d).hom.app (M, N) ≫
          (X.symmetry.toBraidedCategory.braiding (d.F.obj M) (d.F.obj N)).hom =
        d.F.map (Y.symmetry.toBraidedCategory.braiding M N).hom ≫
          (tensorComparison f k d).hom.app (N, M)) := by
  apply normalized_cochain_tensor_diagrams f k d.F d.epsilon
    (tensorComparison f k d) d.universal
  · intro P hP
    exact pullback_computes f d P ((resolving_native Y P).2 hP)
  · intro P Q hP hQ
    obtain ⟨hp, hq, h⟩ := tensorComparison_normalized f k d P Q
      ((resolving_native Y P).2 hP) ((resolving_native Y Q).2 hQ)
    exact ⟨(resolving_native X _).1 hp, (resolving_native X _).1 hq, h⟩

end CanonicalCoherence

/-- Associativity component of the normalized derived tensor coherence.
Source: Stacks 07A4 and 0G7E; extracted from the finite normalization argument.
(blueprint: lem-pur-finite-derived-comparison-normalization-associator).

Proof: specialize the normalized cochain tensor diagram theorem to the existing
representative square and pullback computation, then project associativity.
-/
theorem tensorComparison_coherence_associator {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (k : CochainPullback.Comparison.{u, u, u, u, u} f)
    (d : Pullback.{u, w} f) :
    (∀ M N P : Y.D,
      (tensorComparison f k d).hom.app (Y.closed.tensor.obj (M, N), P) ≫
          X.closed.tensor.map (Prod.mkHom ((tensorComparison f k d).hom.app (M, N))
            (𝟙 (d.F.obj P))) ≫
          (X.closed.monoidal.associator (d.F.obj M) (d.F.obj N) (d.F.obj P)).hom =
        d.F.map (Y.closed.monoidal.associator M N P).hom ≫
          (tensorComparison f k d).hom.app (M, Y.closed.tensor.obj (N, P)) ≫
          X.closed.tensor.map (Prod.mkHom (𝟙 (d.F.obj M))
            ((tensorComparison f k d).hom.app (N, P)))) := by
  exact (normalized_coherence f k d).2.1

/-- Unit and symmetry components of the normalized derived tensor coherence.
Source: Stacks 03EL, 07A4 and 0G7E; extracted from the finite normalization argument.
(blueprint: lem-pur-finite-derived-comparison-normalization-unit-symmetry).

Proof: specialize the normalized cochain tensor diagram theorem to the existing
representative square and pullback computation. Its unit map is the same unitMap;
project the unit isomorphism, both unit equations and signed symmetry.
-/
theorem tensorComparison_coherence_unit_symmetry {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (k : CochainPullback.Comparison.{u, u, u, u, u} f)
    (d : Pullback.{u, w} f) :
    IsIso (unitMap f k d) ∧
    (∀ M : Y.D,
      (tensorComparison f k d).hom.app (Y.closed.monoidal.tensorUnit, M) ≫
          X.closed.tensor.map (Prod.mkHom (unitMap f k d) (𝟙 (d.F.obj M))) ≫
          (X.closed.monoidal.leftUnitor (d.F.obj M)).hom =
        d.F.map (Y.closed.monoidal.leftUnitor M).hom) ∧
    (∀ M : Y.D,
      (tensorComparison f k d).hom.app (M, Y.closed.monoidal.tensorUnit) ≫
          X.closed.tensor.map (Prod.mkHom (𝟙 (d.F.obj M)) (unitMap f k d)) ≫
          (X.closed.monoidal.rightUnitor (d.F.obj M)).hom =
        d.F.map (Y.closed.monoidal.rightUnitor M).hom) ∧
    (∀ M N : Y.D,
      (tensorComparison f k d).hom.app (M, N) ≫
          (X.symmetry.toBraidedCategory.braiding (d.F.obj M) (d.F.obj N)).hom =
        d.F.map (Y.symmetry.toBraidedCategory.braiding M N).hom ≫
          (tensorComparison f k d).hom.app (N, M)) := by
  have h := normalized_coherence f k d
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Associativity, both action-unit equations and signed symmetry for the canonical nu.
Source: Stacks 07A4, 03EL and the node's balanced cochain computations
(blueprint: lem-pur-finite-derived-comparison-normalization).

Proof: combine the separately named associativity and unit/symmetry components.
-/
theorem tensorComparison_coherence {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : CochainPullback.Comparison.{u, u, u, u, u} f)
      (d : Pullback.{u, w} f) :
    IsIso (unitMap f k d) ∧
    (∀ M N P : Y.D,
      (tensorComparison f k d).hom.app (Y.closed.tensor.obj (M, N), P) ≫
          X.closed.tensor.map (Prod.mkHom ((tensorComparison f k d).hom.app (M, N))
            (𝟙 (d.F.obj P))) ≫
          (X.closed.monoidal.associator (d.F.obj M) (d.F.obj N) (d.F.obj P)).hom =
        d.F.map (Y.closed.monoidal.associator M N P).hom ≫
          (tensorComparison f k d).hom.app (M, Y.closed.tensor.obj (N, P)) ≫
          X.closed.tensor.map (Prod.mkHom (𝟙 (d.F.obj M))
            ((tensorComparison f k d).hom.app (N, P)))) ∧
    (∀ M : Y.D,
      (tensorComparison f k d).hom.app (Y.closed.monoidal.tensorUnit, M) ≫
          X.closed.tensor.map (Prod.mkHom (unitMap f k d) (𝟙 (d.F.obj M))) ≫
          (X.closed.monoidal.leftUnitor (d.F.obj M)).hom =
        d.F.map (Y.closed.monoidal.leftUnitor M).hom) ∧
    (∀ M : Y.D,
      (tensorComparison f k d).hom.app (M, Y.closed.monoidal.tensorUnit) ≫
          X.closed.tensor.map (Prod.mkHom (𝟙 (d.F.obj M)) (unitMap f k d)) ≫
          (X.closed.monoidal.rightUnitor (d.F.obj M)).hom =
        d.F.map (Y.closed.monoidal.rightUnitor M).hom) ∧
    (∀ M N : Y.D,
      (tensorComparison f k d).hom.app (M, N) ≫
          (X.symmetry.toBraidedCategory.braiding (d.F.obj M) (d.F.obj N)).hom =
        d.F.map (Y.symmetry.toBraidedCategory.braiding M N).hom ≫
          (tensorComparison f k d).hom.app (N, M)) := by
  obtain ⟨hu, hl, hr, hs⟩ := tensorComparison_coherence_unit_symmetry f k d
  exact ⟨hu, tensorComparison_coherence_associator f k d, hl, hr, hs⟩

/-- Descent component of the canonical pullback compositor.
Source: Stacks 0D6D and 07A4; extracted from normalized word comparison descent.
(blueprint: lem-pur-finite-derived-comparison-normalization).

Proof: descend the ordinary compositor from its normalized representative equation
on resolving complexes.
-/
theorem tensorComparison_composition_descent {X Y Z : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Z.A Y.A)
    (g : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (h : RingedPullback.{u, u, u, u, u} Z.A X.A)
    (kf : CochainPullback.Comparison.{u, u, u, u, u} f) (kg : CochainPullback.Comparison.{u, u, u,
      u, u} g) (kh : CochainPullback.Comparison.{u, u, u, u, u} h)
    (a : CochainPullback.CompositePresentation.{u, u, u, u, u, u, u} f g h kf kg kh)
    (df : Pullback.{u, w} f) (dg : Pullback.{u, w} g) (dh : Pullback.{u, w} h) :
        ∃! c : dh.F ≅ df.F ⋙ dg.F,
      (∀ (P : CochainPullback.Complex.{u, u, u} Z.A), Resolving Z P →
        c.hom.app (DerivedCategory.Q.obj P) ≫ dg.F.map (df.epsilon.app P) ≫
            dg.epsilon.app ((CochainPullback.pull.{u, u, u, u, u} f).obj P) =
          dh.epsilon.app P ≫ DerivedCategory.Q.map (CochainPullback.composition.{u, u, u, u, u, u,
            u} f g h a P).hom) := by
  let U := CochainPullback.pull.{u, u, u, u, u} f
  let V := CochainPullback.pull.{u, u, u, u, u} g
  let W := CochainPullback.pull.{u, u, u, u, u} h
  let e : DerivedCategory.Q ⋙ (df.F ⋙ dg.F) ⟶ (U ⋙ V) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight df.epsilon dg.F ≫ Functor.whiskerLeft U dg.epsilon
  let b : W ≅ U ⋙ V :=
    cochain_compositor f g h a
  have he (P : CochainPullback.Complex.{u, u, u} Z.A) (hP : Resolving Z P) :
      IsIso (e.app P) := by
    have := pullback_computes f df P hP
    have := pullback_computes g dg (U.obj P) (resolving_pull f P hP)
    change IsIso (dg.F.map (df.epsilon.app P) ≫ dg.epsilon.app (U.obj P))
    infer_instance
  exact RingedKFlatWord.comparison_descent_iso
    (Resolving Z) (fun K ↦ by
      obtain ⟨P, p, hP, hp⟩ := resolving_resolution Z K
      exact ⟨P, p, hp, hP⟩)
    dh.F (df.F ⋙ dg.F) (W ⋙ DerivedCategory.Q) ((U ⋙ V) ⋙ DerivedCategory.Q)
    dh.epsilon e (pullback_computes h dh) he (isoWhiskerRight b DerivedCategory.Q)

set_option maxHeartbeats 800000 in
-- The concrete specialization checks the native tensor models at three sites.
/-- Tensor component of the canonical pullback compositor.
Source: Stacks 07A4 and the balanced cochain composition equation; extracted from
normalized tensor descent.
(blueprint: lem-pur-finite-derived-comparison-normalization).

Proof: paste the normalized tensor representative squares and descend the resulting
tensor equation.
-/
theorem tensorComparison_composition_tensor {X Y Z : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Z.A Y.A)
    (g : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (h : RingedPullback.{u, u, u, u, u} Z.A X.A)
    (kf : CochainPullback.Comparison.{u, u, u, u, u} f) (kg : CochainPullback.Comparison.{u, u, u,
      u, u} g) (kh : CochainPullback.Comparison.{u, u, u, u, u} h)
    (a : CochainPullback.CompositePresentation.{u, u, u, u, u, u, u} f g h kf kg kh)
    (df : Pullback.{u, w} f) (dg : Pullback.{u, w} g) (dh : Pullback.{u, w} h)
    (c : dh.F ≅ df.F ⋙ dg.F)
    (hc : (∀ (P : CochainPullback.Complex.{u, u, u} Z.A), Resolving Z P →
        c.hom.app (DerivedCategory.Q.obj P) ≫ dg.F.map (df.epsilon.app P) ≫
            dg.epsilon.app ((CochainPullback.pull.{u, u, u, u, u} f).obj P) =
          dh.epsilon.app P ≫ DerivedCategory.Q.map (CochainPullback.composition.{u, u, u, u, u, u,
            u} f g h a P).hom)) :
      (∀ M N : Z.D,
        (tensorComparison h kh dh).hom.app (M, N) ≫
            X.closed.tensor.map (Prod.mkHom (c.hom.app M) (c.hom.app N)) =
          c.hom.app (Z.closed.tensor.obj (M, N)) ≫
            dg.F.map ((tensorComparison f kf df).hom.app (M, N)) ≫
            (tensorComparison g kg dg).hom.app (df.F.obj M, df.F.obj N)) := by
  have := cachedTensorAdditive X.A
  have := cachedTensorAdditiveObj X.A
  have := cachedTensorLeftZero X.A
  have := cachedTensorRightZero X.A
  have := cachedGradedTensor X.A
  have := cachedGradedFour X.A
  have := cachedGradedLeft X.A
  have := cachedGradedRight X.A
  have := cachedTensorAdditive Y.A
  have := cachedTensorAdditiveObj Y.A
  have := cachedTensorLeftZero Y.A
  have := cachedTensorRightZero Y.A
  have := cachedGradedTensor Y.A
  have := cachedGradedFour Y.A
  have := cachedGradedLeft Y.A
  have := cachedGradedRight Y.A
  have := cachedTensorAdditive Z.A
  have := cachedTensorAdditiveObj Z.A
  have := cachedTensorLeftZero Z.A
  have := cachedTensorRightZero Z.A
  have := cachedGradedTensor Z.A
  have := cachedGradedFour Z.A
  have := cachedGradedLeft Z.A
  have := cachedGradedRight Z.A
  have : ∀ P Q : CochainPullback.Complex.{u, u, u} Z.A,
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules Z.A)) (.up ℤ) :=
    totalTensor_exists Z.A
  have : ∀ P Q : CochainPullback.Complex.{u, u, u} Y.A,
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules Y.A)) (.up ℤ) :=
    totalTensor_exists Y.A
  have : ∀ P Q : CochainPullback.Complex.{u, u, u} X.A,
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules X.A)) (.up ℤ) :=
    totalTensor_exists X.A
  let U := CochainPullback.pull.{u, u, u, u, u} f
  let V := CochainPullback.pull.{u, u, u, u, u} g
  let W := CochainPullback.pull.{u, u, u, u, u} h
  let b : W ≅ U ⋙ V :=
    cochain_compositor f g h a
  obtain ⟨ff⟩ := resolving_fullyFaithful Z X
  apply comparison_tensor_descends DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (fun P Q ↦ HomologicalComplex.tensorObj P Q)
    (fun P Q ↦ HomologicalComplex.tensorObj P Q)
    (fun P Q ↦ HomologicalComplex.tensorObj P Q)
    Z.closed.tensor Y.closed.tensor X.closed.tensor U V W df.F dg.F dh.F
    df.epsilon dg.epsilon dh.epsilon (tensorComparison f kf df).hom
    (tensorComparison g kg dg).hom (tensorComparison h kh dh).hom
    (Resolving Z) (Resolving Y) (Resolving X)
    (resolving_pull f) (resolving_pull g) (resolving_pull h) (resolving_tensor Z) ff
    (fun P Q hP hQ ↦ Z.model.iso Z.J Z.A Z.closed P Q hP.1 hQ.1)
    (fun P Q hP hQ ↦ Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1)
    (fun P Q hP hQ ↦ X.model.iso X.J X.A X.closed P Q hP.1 hQ.1)
    (fun P Q ↦ (CochainPullback.comparison f kf P Q).hom)
    (fun P Q ↦ (CochainPullback.comparison g kg P Q).hom)
    (fun P Q ↦ (CochainPullback.comparison h kh P Q).hom)
    (tensorComparison_model_square f kf df)
    (tensorComparison_model_square g kg dg)
    (tensorComparison_model_square h kh dh)
    (pullback_computes f df) (pullback_computes g dg) c b
    (fun P hP ↦ by
      simpa only [b, cochain_compositor_hom_app] using hc P hP)
    (fun P Q ↦ HomologicalComplex.tensorHom (b.hom.app P) (b.hom.app Q)) ?_ ?_
  · intro P Q
    exact cochain_composition_tensor f g h kf kg kh a P Q
  · intro P Q hP hQ
    exact tensor_model_naturality X
      (resolving_pull h P hP).1 (resolving_pull h Q hQ).1
      (resolving_pull g _ (resolving_pull f P hP)).1
      (resolving_pull g _ (resolving_pull f Q hQ)).1 (b.hom.app P) (b.hom.app Q)

theorem tensorComparison_composition {X Y Z : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Z.A Y.A)
    (g : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (h : RingedPullback.{u, u, u, u, u} Z.A X.A)
    (kf : CochainPullback.Comparison.{u, u, u, u, u} f) (kg : CochainPullback.Comparison.{u, u, u,
      u, u} g) (kh : CochainPullback.Comparison.{u, u, u, u, u} h)
    (a : CochainPullback.CompositePresentation.{u, u, u, u, u, u, u} f g h kf kg kh)
    (df : Pullback.{u, w} f) (dg : Pullback.{u, w} g) (dh : Pullback.{u, w} h) :
        ∃! c : dh.F ≅ df.F ⋙ dg.F,
      (∀ (P : CochainPullback.Complex.{u, u, u} Z.A), Resolving Z P →
        c.hom.app (DerivedCategory.Q.obj P) ≫ dg.F.map (df.epsilon.app P) ≫
            dg.epsilon.app ((CochainPullback.pull.{u, u, u, u, u} f).obj P) =
          dh.epsilon.app P ≫ DerivedCategory.Q.map (CochainPullback.composition.{u, u, u, u, u, u,
            u} f g h a P).hom) ∧
      (∀ M N : Z.D,
        (tensorComparison h kh dh).hom.app (M, N) ≫
            X.closed.tensor.map (Prod.mkHom (c.hom.app M) (c.hom.app N)) =
          c.hom.app (Z.closed.tensor.obj (M, N)) ≫
            dg.F.map ((tensorComparison f kf df).hom.app (M, N)) ≫
            (tensorComparison g kg dg).hom.app (df.F.obj M, df.F.obj N)) := by
  obtain ⟨c, hc, hu⟩ := tensorComparison_composition_descent f g h kf kg kh a df dg dh
  refine ⟨c, ⟨hc, tensorComparison_composition_tensor f g h kf kg kh a df dg dh c hc⟩, ?_⟩
  intro c' hc'
  exact hu c' hc'.1

attribute [local irreducible]
  CategoryTheory.CochainPullback.extensionPullback
  CategoryTheory.CochainPullback.extensionFunctor
  CategoryTheory.CochainPullback.changed
  SheafOfModules.PullbackTensorCanonical.IsNormalized
  CategoryTheory.CochainPullback.kappa

section Coefficients

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
  [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} S)]

open SheafOfModules.PullbackTensorCanonical

/-- Simultaneous coefficient square, normalized by all four tensor representative
squares and by the ordinary balanced scalar-association map. The four tensors here
are the fixed published tensors `canonicalDerivedTensor`, an equivalent presentation
of the site tensor used above. No coefficient map is required to be flat.
Source: Stacks 07A4, 0G7E, and the balanced coefficient square of the DAG
(blueprint: lem-pur-finite-derived-comparison-normalization).

Proof: regard both coefficient extensions as identity-topos ringed pullbacks.
By lem-trf-ringed-kflat-word-comparison-descent, a single flat-term K-flat
representative computes every intermediate scalar and pullback word, including
nonflat quotient changes. Descend the specified scalarAssociation, which is
uniquely fixed on generalized scalar-extension generators. Its normalization is
the displayed counit equation. Apply the representative normalization to the
four edges. On a common pair P,Q, the two routes are the first coefficient
equation of lem-pur-cochain-pullback-tensor-coherence: starting with
s' tensor ((x tensor y) tensor r), both give
((1 tensor x) tensor s' phi'(r)) tensor ((1 tensor y) tensor 1).
Insert all four representative maps and cancel adjacent computation inverses.
Fully faithful two-variable tensor descent proves the square on all unbounded
derived inputs. Unary descent gives uniqueness of kappa from its normalization;
the four tensor comparisons are likewise the uniquely normalized comparisons. -/
theorem tensorComparison_coefficients
    (f : RingedPullback.{u, u, u, u, u} R S) (k : CochainPullback.Comparison.{u, u, u, u, u} f)
    (a : CochainPullback.CoefficientSquare.{u, u, u, u, u} f) (k' : CochainPullback.Comparison.{u,
      u, u, u, u} (CochainPullback.changed.{u, u, u, u, u} f a))
    [HasDerivedCategory.{w} (Modules.{u, u, u} a.R')]
    [HasDerivedCategory.{w} (Modules.{u, u, u} a.S')]
    (df : Pullback.{u, w} f) (df' : Pullback.{u, w} (CochainPullback.changed.{u, u, u, u, u} f a))
    (dR : Pullback.{u, w} (extensionPullback.{u, u, u} a.sourceMap))
    (dS : Pullback.{u, w} (extensionPullback.{u, u, u} a.targetMap)) :
    ∃ (nu : Phi.{u, u, u, u, u, w, w} (R := R) (S := S) df.F ≅ Psi.{u, u, u, u, u, w, w} (R := R)
        (S := S) df.F)
      (nu' : Phi.{u, u, u, u, u, w, w} (R := a.R') (S := a.S') df'.F ≅ Psi.{u, u, u, u, u, w, w}
        (R := a.R') (S := a.S') df'.F)
      (epsR : Phi.{u, u, u, u, u, w, w} (R := R) (S := a.R') dR.F ≅ Psi.{u, u, u, u, u, w, w} (R
        := R) (S := a.R') dR.F)
      (epsS : Phi.{u, u, u, u, u, w, w} (R := S) (S := a.S') dS.F ≅ Psi.{u, u, u, u, u, w, w} (R
        := S) (S := a.S') dS.F)
      (b : dR.F ⋙ df'.F ≅ df.F ⋙ dS.F),
      IsNormalized.{u, u, u, u, u, w, w} (R := R) (S := S) f k df.F df.epsilon nu.hom ∧
      IsNormalized.{u, u, u, u, u, w, w} (R := a.R') (S := a.S')
        (CochainPullback.changed.{u, u, u, u, u} f a) k' df'.F df'.epsilon nu'.hom ∧
      IsNormalized.{u, u, u, u, u, w, w} (R := R) (S := a.R') (extensionPullback.{u, u, u}
          a.sourceMap)
        (extensionComparison.{u, u, u} a.sourceMap)
        dR.F dR.epsilon epsR.hom ∧
      IsNormalized.{u, u, u, u, u, w, w} (R := S) (S := a.S') (extensionPullback.{u, u, u}
          a.targetMap)
        (extensionComparison.{u, u, u} a.targetMap)
        dS.F dS.epsilon epsS.hom ∧
      (∀ (P : CochainPullback.Complex.{u, u, u} R), P.IsKFlatIndependentCoefficients →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) →
        b.hom.app ((DerivedCategory.Q.{w} (C := Modules.{u, u, u} R)).obj P) ≫ dS.F.map
        (df.epsilon.app P) ≫
            dS.epsilon.app ((CochainPullback.pull.{u, u, u, u, u} f).obj P) =
          df'.F.map (dR.epsilon.app P) ≫ df'.epsilon.app ((extend.{u, u, u} a.sourceMap).obj P) ≫
            (DerivedCategory.Q.{w} (C := Modules.{u, u, u} a.S')).map (CochainPullback.kappa.{u,
          u, u,
        u, u} f k a k' P).hom) ∧
      (∀ M N : DerivedCategory (Modules.{u, u, u} R),
        df'.F.map (epsR.hom.app (M, N)) ≫
            nu'.hom.app (dR.F.obj M, dR.F.obj N) ≫
            (Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} a.S')).map
              (Prod.mkHom (b.hom.app M) (b.hom.app N)) =
          b.hom.app (((canonicalDerivedTensor.{u, u, u, w} R).obj M).obj N) ≫
            dS.F.map (nu.hom.app (M, N)) ≫
            epsS.hom.app (df.F.obj M, df.F.obj N)) ∧
      (∀ b' : dR.F ⋙ df'.F ≅ df.F ⋙ dS.F,
        (∀ (P : CochainPullback.Complex.{u, u, u} R), P.IsKFlatIndependentCoefficients →
          (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) →
          b'.hom.app ((DerivedCategory.Q.{w} (C := Modules.{u, u, u} R)).obj P) ≫ dS.F.map
        (df.epsilon.app P) ≫
              dS.epsilon.app ((CochainPullback.pull.{u, u, u, u, u} f).obj P) =
            df'.F.map (dR.epsilon.app P) ≫ df'.epsilon.app ((extend.{u, u, u} a.sourceMap).obj P) ≫
              (DerivedCategory.Q.{w} (C := Modules.{u, u, u} a.S')).map
          (CochainPullback.kappa.{u, u,
        u, u, u} f k a k' P).hom) → b' =
                b) := by
  exact NormalizedCoefficientTensor.normalizedCoefficientTensorSquare.{u, w} f k a k'
    df.F df'.F dR.F dS.F df.epsilon df'.epsilon dR.epsilon dS.epsilon
    df.universal df'.universal dR.universal dS.universal

end Coefficients

/-- Identity and successive coefficient comparisons respect identities and pasting.
The paths retain their actual parenthesizations and universal composite counits.
Specializing the edges to the four pullbacks of a coefficient square, or to two
successive coefficient squares, gives precisely identity and successive changes.
Source: Stacks 0D6D, 03EL, and DAG proof step 6
(blueprint: lem-pur-finite-derived-comparison-normalization).

Proof: on flat-term K-flat representatives conjugate the ordinary cell by the
word computation isomorphisms. For the identity these cancel. For successive
changes the middle computation cancels, leaving the composite ordinary scalar
association; both scalar routes multiply s'' times the image of s'. The normalized
unary descent uniqueness in lem-trf-ringed-kflat-word-comparison-descent extends
these equalities to all derived inputs. Since the tensor squares above are natural
and normalized on the same pairs, their pasted equations agree as well. -/
theorem coefficientComparison_identity_successive
    {I : Type u} [Finite I] (B : I → RingedKFlatWord.Site.{u, u, u, w})
    (E : I → I → Type u)
    (A : ∀ {i j : I}, E i j → RingedKFlatWord.Edge (B i) (B j)) :
    (∀ {i j : I} (p : RingedKFlatWord.Word E i j),
      RingedKFlatWord.Word.cell B E A (𝟙 (p.ordinary B E A)) =
        𝟙 (p.derived B E A)) ∧
    (∀ {i j : I} (p q r : RingedKFlatWord.Word E i j)
      (a : p.ordinary B E A ⟶ q.ordinary B E A)
      (b : q.ordinary B E A ⟶ r.ordinary B E A),
      RingedKFlatWord.Word.cell B E A (a ≫ b) =
        RingedKFlatWord.Word.cell B E A a ≫ RingedKFlatWord.Word.cell B E A b) := by
  constructor
  · intro i j p
    exact ((RingedKFlatWord.word_comparison_descent B E A).1
      (RingedKFlatWord.Expression.id p)).symm
  · intro i j p q r a b
    exact ((RingedKFlatWord.word_comparison_descent B E A).1
      (RingedKFlatWord.Expression.comp (RingedKFlatWord.Expression.cell a)
        (RingedKFlatWord.Expression.cell b))).symm

end CategoryTheory.FiniteDerivedComparison

attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
