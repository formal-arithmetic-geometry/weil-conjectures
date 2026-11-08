/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Submission.WeilConjectures.SmoothPurity.IntegralAmbient.NormalizedIntegralPullbackTower
import all Submission.WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import Submission.WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import Submission.WeilConjectures.Algebra.Homology.RingedPresentationOnSites.RingedPullbackPresentationOnSitesSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Submission.WeilConjectures.Algebra.Homology.Ringed.RingedPullbackCochainPresentation
import Submission.WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralTensorTower
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Submission.WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all Submission.WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Ambient completion presentations of integral operations

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E, 07A4 and 0941;
sites-modules.tex, Tags 03D7 and 03EL
(blueprint: lem-pur-integral-ambient-operation-models).

All towers and finite operations below are the recorded constructions. The completed
coefficient map is specified by its projections, not by an identification of rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a₁ b₁ c₁ d₁
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.IntegralAmbient
open AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLocalizationIsMonoidal
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits
attribute [local instance 2000] integralOperationsFiniteHasMap

attribute [local irreducible] constantSheaf

attribute [local irreducible] HasDerivedCategory.standard

/-- The source tensor tower uses the direct-sum total tensor complex.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorTower (W : Scheme.{t}) :
    (CochainComplex (integralTowerModules l E W) ℤ ×
      CochainComplex (integralTowerModules l E W) ℤ) ⥤
        (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) :=
  coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) ⋙ IntegralOnSlice.tower l E W none

set_option maxHeartbeats 60000

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local irreducible] coefficientTotalTensor SheafOfModules.monoidalCategory
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence
  SheafOfModules.changeOfRings PresheafOfModules.sheafification

private theorem tensorLevel_hom_ext (W : Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (k : ℤ)
    (H : integralTowerModules l E W)
    {f g : (((tensorTower l E W).obj (P, Q)).obj (op n)).X k ⟶ H}
    (h : ∀ (p q : ℤ) (hpq : p + q = k) (V : W.ProEtᵒᵖ)
      (s : (integralCoefficientCommRingSheaf l E W n).obj.obj V)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      f.val.app V (IntegralOnSlice.generator l E W none n _ V s
        (coefficientTensorGenerator.{u, t + 1, t} (ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq V x y)) =
      g.val.app V (IntegralOnSlice.generator l E W none n _ V s
        (coefficientTensorGenerator.{u, t + 1, t} (ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq V x y))) :
    f = g := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  dsimp only [tensorTower, Functor.comp_obj, IntegralOnSlice.tower,
    Functor.flip_obj_obj, Functor.ofOpSequence_obj] at f g ⊢
  let F := IntegralOnSlice.reduction l E W none n
  let hF := IntegralOnSlice.reduction_obj l E W none n
  let hmF {M N : integralTowerModules l E W} (f : M ⟶ N) :
      F.map f = eqToHom (hF M) ≫
        SheafOfModules.changeOfRingsHom
          (IntegralOnSlice.projection l E W none n) M f ≫
          eqToHom (hF N).symm :=
    IntegralOnSlice.unrestrictedReduction_map l E W none n f
  letI := extension_preserves_small_colimits.{t + 1, t, u}
    (IntegralOnSlice.projection l E W none n) F hF hmF
  apply total_extension_hom_ext.{t + 1, t, u}
    (IntegralOnSlice.projection l E W none n) F hF hmF P Q k H
  intro p q hpq V s x y
  convert h p q hpq V s x y using 1 <;> rfl

/-- The normalized balanced-tensor isomorphism of whole strict tensor towers.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: in bidegree (p,q) send (x tensor y) tensor a to
(x tensor a) tensor (y tensor 1); the inverse multiplies the two coefficients.
The tensor universal property and direct sums extend these inverse maps. Both
sides have differential dx tensor y + (-1)^p x tensor dy, with unchanged a.
The formulas commute with all quotient transitions and with both input chain maps. -/
theorem tensorTowerModel (W : Scheme.{t}) :
    ∃! d : tensorTower l E W ≅ integralOperationsTensorTowerFunctor l E W,
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (p q : ℤ)
        (V : W.ProEtᵒᵖ) (a : (integralCoefficientCommRingSheaf l E W n).obj.obj V)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (((d.hom.app (P, Q)).app (op n)).f (p + q)).val.app V
          (IntegralOnSlice.generator l E W none n _ V a
            (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl V x y)) =
          integralOperationsTotalTensorSection l E W n P Q p q V
            (unrestrictedIntegralTensorSection l E W n (P.X p) V a x)
            (unrestrictedIntegralTensorSection l E W n (Q.X q) V 1 y) := by
  classical
  obtain ⟨d, hd⟩ := normalizedIntegralTensorTower l E W
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext Z
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro k
  apply tensorLevel_hom_ext l E W Z.1 Z.2 n.unop k
  intro p q hpq V s x y
  subst k
  exact (hd' Z.1 Z.2 n.unop p q V s x y).trans
    (hd Z.1 Z.2 n.unop p q V s x y).symm

/-- The uniquely normalized strict pullback comparison.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def pullTowerIso {X Y : Scheme.{t}} (f : X ⟶ Y) :
    pullTower l E f ≅ integralOperationsPullbackTowerFunctor l E f :=
  (pullTowerModel l E f).exists.choose

/-- The uniquely normalized strict tensor comparison.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorTowerIso (W : Scheme.{t}) :
    tensorTower l E W ≅ integralOperationsTensorTowerFunctor l E W :=
  (tensorTowerModel l E W).exists.choose

attribute [local irreducible] coefficientMap push pull pullTowerIso tensorTowerIso
  IntegralOnSlice.duality IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit IntegralOnSlice.roosUnit

/-- Ordinary pullback carries flat-term K-flat representatives to such representatives.
Source: Stacks 0G7E (blueprint: lem-pur-integral-ambient-operation-models).
Proof: the module inverse image is the geometric inverse image followed by scalar
extension along coefficientMap. Apply ringed-topos K-flat pullback to this presentation;
flatness of its terms follows from the same ringed pullback theorem. -/
theorem pull_good {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :
    IntegralOnSlice.Good l E X none ((pullComplex l E f).obj P) := by
  letI : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  letI : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  letI : HasSheafify (ProEt.topology Y) (Type (max u (t + 1))) :=
    hasSheafifyEssentiallySmallSite _ _
  letI : HasSheafify (ProEt.topology X) (Type (max u (t + 1))) :=
    hasSheafifyEssentiallySmallSite _ _
  let G := Scheme.proEtaleBaseChange f
  let L := G.sheafPullback (Type (max u (t + 1))) (ProEt.topology Y) (ProEt.topology X)
  let a := G.sheafAdjunctionContinuous (Type (max u (t + 1)))
    (ProEt.topology Y) (ProEt.topology X)
  letI : ReflectsLimits (forget (Type (max u (t + 1)))) :=
    reflectsLimits_of_reflectsIsomorphisms
  letI : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  letI : PreservesFiniteLimits (G.op.lan : (Y.ProEtᵒᵖ ⥤ Type (max u (t + 1))) ⥤
      X.ProEtᵒᵖ ⥤ Type (max u (t + 1))) :=
    by
      letI : AB5OfSize.{t, t + 1} (Type (max u (t + 1))) :=
        AB5OfSize_shrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
      exact preservesFiniteLimits_op_lan_of_flat G
  letI : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits G
      (Type (max u (t + 1))) (ProEt.topology Y) (ProEt.topology X)
  obtain ⟨RI, I, c, T, hT, hobj, hmap, ⟨am⟩⟩ :=
    SheafOfModules.RingedPresentationOnSites.continuous_ringed_pullback_presentation
      G L a (completedIntegralCommRingSheafUnrestricted l E X)
      (completedIntegralCommRingSheafUnrestricted l E Y) (coefficientMap l E f)
  letI := hT
  have am' : T ⊣ push l E f := by
    unfold push
    let q := ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
      (coefficientMap l E f))
    have hq : q = (⟨Functor.whiskerRight (coefficientMap l E f).hom
        (forget₂ CommRingCat RingCat)⟩) := rfl
    change T ⊣ SheafOfModules.pushforward q at am
    rw [hq] at am
    exact am
  let e : T ≅ pull l E f := am'.leftAdjointUniq (adjunction l E f)
  obtain ⟨hK, hflat⟩ := SheafOfModules.isKFlat_ringedToposPullback
    L _ a I c T hobj hmap P hP.1 hP.2
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  exact ⟨SheafOfModules.kFlat_iso_independent
    (completedIntegralCommRingSheafUnrestricted l E X) ec hK,
    fun i ↦ SheafOfModules.flatOnSite_of_iso
      (completedIntegralCommRingSheafUnrestricted l E X)
      ((HomologicalComplex.eval _ _ i).mapIso ec) (hflat i)⟩

attribute [local semireducible] coefficientTotalTensor

/-- The direct-sum total tensor of two good representatives is good.
Source: Stacks 07A2, 07A4 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: the total tensor of K-flat complexes is K-flat. Its terms are direct sums
of tensor products of flat module sheaves and are therefore flat. No boundedness
or product totalization is involved. -/
theorem tensor_good (W : Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P)
    (hQ : integralOperationsGoodComplex l E W Q) :
    IntegralOnSlice.Good l E W none
      ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (completedIntegralCommRingSheafUnrestricted l E W) P Q hP.1 hQ.1 hP.2 hQ.2
  exact ⟨h.1, h.2.1⟩

attribute [local irreducible] IntegralOnSlice.tower Functor.mapHomologicalComplex
  DerivedCategory.Q integralOperationsRoos integralOperationsRoosMap

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 200000

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Shared category and functor data of the recorded tensor comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
structure AmbientTensorPresentation where
  Cx : Type a₁
  [cxCategory : Category.{b₁} Cx]
  D : Type c₁
  [dCategory : Category.{d₁} D]
  Flat : ObjectProperty Cx
  Good : ObjectProperty Cx
  good_flat : ∀ X, Good X → Flat X
  totalTensor : Cx × Cx ⥤ Cx
  Q : Cx ⥤ D
  tensor : D × D ⥤ D
  comparison : Flat.ι.prod Flat.ι ⋙ totalTensor ⋙ Q ≅
    (Flat.ι ⋙ Q).prod (Flat.ι ⋙ Q) ⋙ tensor
/-- Capture the categories, functors and comparison in one record.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def AmbientTensorPresentation.ofComparison
    {C : Type a₁} [cc : Category.{b₁} C]
    {D : Type c₁} [dd : Category.{d₁} D]
    {K : ObjectProperty C}
    {T : C × C ⥤ C} {Q : C ⥤ D} {S : D × D ⥤ D}
    (cmp : K.ι.prod K.ι ⋙ T ⋙ Q ≅ (K.ι ⋙ Q).prod (K.ι ⋙ Q) ⋙ S)
    (G : ObjectProperty C) (hG : ∀ X, G X → K X) : AmbientTensorPresentation :=
  { Cx := C, cxCategory := cc, D := D, dCategory := dd,
    Flat := K, Good := G, good_flat := hG,
    totalTensor := T, Q := Q, tensor := S, comparison := cmp }
/-- Capture the actual data used by the existing tensor model once.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorPresentation (W : Scheme.{t}) :=
  AmbientTensorPresentation.ofComparison
    (IntegralOnSlice.duality l E W none).models.comparison
    (IntegralOnSlice.Good l E W none) (fun _ h ↦ h.1)

/-- The recorded ambient cochain category.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientCx (W : Scheme.{t}) := (ambientTensorPresentation l E W).Cx

set_option warn.classDefReducibility false in
@[irreducible] def ambientCxCategory (W : Scheme.{t}) : Category (ambientCx l E W) :=
  (ambientTensorPresentation l E W).cxCategory

attribute [instance 5000] ambientCxCategory

/-- Good complexes in the recorded ambient cochain category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientGood (W : Scheme.{t}) : ObjectProperty (ambientCx l E W) :=
  (ambientTensorPresentation l E W).Good

/-- K-flat complexes in the recorded ambient cochain category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
abbrev ambientFlat (W : Scheme.{t}) : ObjectProperty (ambientCx l E W) :=
  (ambientTensorPresentation l E W).Flat

/-- Every good representative belongs to the recorded K-flat class.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem ambientGoodFlat (W : Scheme.{t}) (P : ambientCx l E W)
    (h : ambientGood l E W P) : ambientFlat l E W P :=
  (ambientTensorPresentation l E W).good_flat P h

/-- The recorded ambient derived category.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientD (W : Scheme.{t}) := (ambientTensorPresentation l E W).D

set_option warn.classDefReducibility false in
/-- Share its recorded category structure throughout the comparisons.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientDCategory (W : Scheme.{t}) : Category (ambientD l E W) :=
  (ambientTensorPresentation l E W).dCategory

attribute [instance 5000] ambientDCategory

/-- The localization functor of the recorded ambient derived category.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientQ (W : Scheme.{t}) : ambientCx l E W ⥤ ambientD l E W :=
  by with_unfolding_all exact (ambientTensorPresentation l E W).Q

/-- Its class of quasi-isomorphisms, taken from the same localization data.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientQuasiIso (W : Scheme.{t}) : MorphismProperty (ambientCx l E W) := by
  with_unfolding_all exact ((fun {C : Type _} [c : Category C] (V : MorphismProperty C)
    (_ : MorphismProperty.HasLocalization V) => V) _
      (IntegralOnSlice.hasDerived l E W none))

/-- The recorded ambient functor is a localization.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
@[instance] theorem ambientQ_isLocalization (W : Scheme.{t}) :
    (ambientQ l E W).IsLocalization (ambientQuasiIso l E W) := by
  with_unfolding_all exact
    @MorphismProperty.HasLocalization.hL _ _ _ (IntegralOnSlice.hasDerived l E W none)

/-- Ordinary pullback in the recorded ambient cochain presentation.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ ambientCx l E X := by
  with_unfolding_all exact pullComplex l E f

/-- The ordinary total tensor of the recorded slice coefficient presentation.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTotalTensor (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ ambientCx l E W :=
  by with_unfolding_all exact (ambientTensorPresentation l E W).totalTensor

/-- Pullback preserves the recorded good complexes.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem ambientPullGood {X Y : Scheme.{t}} (f : X ⟶ Y) (P : ambientCx l E Y)
    (hP : ambientGood l E Y P) : ambientGood l E X ((ambientPullComplex l E f).obj P) := by
  with_unfolding_all exact pull_good l E f P hP

/-- Ordinary total tensor preserves the recorded good complexes.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem ambientTensorGood (W : Scheme.{t}) (P Q : ambientCx l E W)
    (hP : ambientGood l E W P) (hQ : ambientGood l E W Q) :
    ambientGood l E W ((ambientTotalTensor l E W).obj (P, Q)) := by
  with_unfolding_all exact tensor_good l E W P Q hP hQ

/-- The Roos functor on the same ambient cochain category.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientRoos (W : Scheme.{t}) :
    (ℕᵒᵖ ⥤ ambientCx l E W) ⥤ ambientCx l E W := by
  with_unfolding_all exact
    integralOperationsRoosFunctor (A := IntegralOnSlice.Mod l E W none)

/-- The ordinary quotient tower in the captured cochain category.
Source: Stacks 0941 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientQuotientTower (W : Scheme.{t}) :
    ambientCx l E W ⥤ (ℕᵒᵖ ⥤ ambientCx l E W) := by
  with_unfolding_all exact IntegralOnSlice.tower l E W none

/-- Its Roos complex functor, with the captured category data.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientRoosComplex (W : Scheme.{t}) : ambientCx l E W ⥤ ambientCx l E W :=
  ambientQuotientTower l E W ⋙ ambientRoos l E W

/-- The quotient augmentation into this Roos complex.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientRoosUnit (W : Scheme.{t}) (P : ambientCx l E W) :
    P ⟶ (ambientRoosComplex l E W).obj P := by
  with_unfolding_all exact IntegralOnSlice.roosUnit l E W none P

/-- The recorded finite pullback tower in this cochain presentation.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientRecordedPullTower {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ (ℕᵒᵖ ⥤ ambientCx l E X) := by
  with_unfolding_all exact integralOperationsPullbackTowerFunctor l E f

/-- The recorded finite tensor tower in this cochain presentation.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientRecordedTensorTower (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ (ℕᵒᵖ ⥤ ambientCx l E W) := by
  with_unfolding_all exact integralOperationsTensorTowerFunctor l E W

/-- The recorded finite pullback Roos complex.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientRecordedPullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ ambientCx l E X :=
  ambientRecordedPullTower l E f ⋙ ambientRoos l E X

/-- The recorded finite tensor Roos complex.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientRecordedTensorComplex (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ ambientCx l E W :=
  ambientRecordedTensorTower l E W ⋙ ambientRoos l E W

/-- The specified pullback tower comparison, sharing its source category data.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPullTowerIso {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientPullComplex l E f ⋙ ambientQuotientTower l E X ≅
      ambientRecordedPullTower l E f := by
  with_unfolding_all exact pullTowerIso l E f

/-- The specified tensor tower comparison, sharing its source category data.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorTowerIso (W : Scheme.{t}) :
    ambientTotalTensor l E W ⋙ ambientQuotientTower l E W ≅
      ambientRecordedTensorTower l E W := by
  with_unfolding_all exact tensorTowerIso l E W

/-- The recorded derived pullback in this derived category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPull {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientD l E Y ⥤ ambientD l E X := by
  with_unfolding_all exact integralDerivedPullback l E f

/-- The recorded completed tensor in this derived category.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletedTensor (W : Scheme.{t}) :
    ambientD l E W × ambientD l E W ⥤ ambientD l E W := by
  with_unfolding_all exact integralCompletedTensor l E W

/-- Localization restricted to the good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientGoodLocalization (W : Scheme.{t}) :
    (ambientGood l E W).FullSubcategory ⥤
      ambientD l E W :=
  (ambientGood l E W).ι ⋙ (ambientQ l E W)

/-- The finite pullback operation on good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientPullOnGood {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (ambientGood l E Y).FullSubcategory ⥤
      ambientD l E X :=
  (ambientGood l E Y).ι ⋙
    ambientRecordedPullComplex l E f ⋙ (ambientQ l E X)

/-- The finite tensor operation on pairs of good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientTensorOnGood (W : Scheme.{t}) :
    (ambientGood l E W).FullSubcategory ×
      (ambientGood l E W).FullSubcategory ⥤
        ambientD l E W :=
  ((ambientGood l E W).ι.prod
    (ambientGood l E W).ι) ⋙
      ambientRecordedTensorComplex l E W ⋙ (ambientQ l E W)

/-- The Roos completion on good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientCompletionOnGood (W : Scheme.{t}) :
    (ambientGood l E W).FullSubcategory ⥤ ambientD l E W :=
  (ambientGood l E W).ι ⋙ ambientRoosComplex l E W ⋙ ambientQ l E W

/-- The recorded pullback comparison on good representatives.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPullComparison {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientGoodLocalization l E Y ⋙ ambientPull l E f ≅ ambientPullOnGood l E f := by
  with_unfolding_all exact integralDerivedPullbackComparison l E f

/-- The recorded tensor comparison on good representatives.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorComparison (W : Scheme.{t}) :
    (ambientGoodLocalization l E W).prod (ambientGoodLocalization l E W) ⋙
      ambientCompletedTensor l E W ≅ ambientTensorOnGood l E W := by
  with_unfolding_all exact integralCompletedTensorComparison l E W

/-- Completion in the recorded ambient derived category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletion (W : Scheme.{t}) : ambientD l E W ⥤ ambientD l E W := by
  with_unfolding_all exact IntegralOnSlice.completion l E W none

/-- The recorded completion comparison.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletionComparison (W : Scheme.{t}) :
    ambientGoodLocalization l E W ⋙ ambientCompletion l E W ≅
      ambientCompletionOnGood l E W := by
  with_unfolding_all exact IntegralOnSlice.completionComparison l E W none

/-- The recorded completion unit.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletionUnit (W : Scheme.{t}) :
    𝟭 (ambientD l E W) ⟶ ambientCompletion l E W :=
  by with_unfolding_all exact IntegralOnSlice.completionUnit l E W none

/-- Ordinary derived tensor in the recorded ambient category.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientOrdinaryTensor (W : Scheme.{t}) :
    ambientD l E W × ambientD l E W ⥤ ambientD l E W :=
  by with_unfolding_all exact (ambientTensorPresentation l E W).tensor

/-- The whole ordinary tensor model comparison, with its category data shared once.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorModelComparison (W : Scheme.{t}) :
    ((ambientFlat l E W).ι.prod (ambientFlat l E W).ι) ⋙
      ambientTotalTensor l E W ⋙ ambientQ l E W ≅
        (((ambientFlat l E W).ι ⋙ ambientQ l E W).prod
          ((ambientFlat l E W).ι ⋙ ambientQ l E W)) ⋙ ambientOrdinaryTensor l E W := by
  unfold ambientTotalTensor ambientQ ambientOrdinaryTensor
  with_unfolding_all exact (ambientTensorPresentation l E W).comparison

attribute [local irreducible] integralOperationsLevelPullback
  Scheme.coefficientProEtaleModulePullback unrestrictedIntegralReductionFunctor
  IntegralOnSlice.reduction IntegralOnSlice.reductionWitness

/-- Construct the universal ambient pullback counit.
Source: Stacks 06YY and 0G7E
(blueprint: lem-pur-integral-ambient-operation-models).

Proof: present pullback using independent-universe inverse image and scalar extension.
Uniqueness of left adjoints identifies it with the recorded pullback. Apply the
ringed derived-pullback theorem, transport its universal counit from homotopy
representatives to cochains, then transport along that left-adjoint isomorphism.
Good complexes remain good under pullback, so the counit is an isomorphism there. -/
theorem rawAmbientDerivedData {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃ (F : ambientD l E Y ⥤
        ambientD l E X)
      (ε : ambientQ l E Y ⋙ F ⟶ ambientPullComplex l E f ⋙ ambientQ l E X),
      F.IsLeftDerivedFunctor ε
        (ambientQuasiIso l E Y) ∧
      ∀ P : (ambientGood l E Y).FullSubcategory,
        IsIso (ε.app P.obj) := by
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : HasSheafify (ProEt.topology Y) (Type (max u (t + 1))) :=
    hasSheafifyEssentiallySmallSite _ _
  let : HasSheafify (ProEt.topology X) (Type (max u (t + 1))) :=
    hasSheafifyEssentiallySmallSite _ _
  let G := Scheme.proEtaleBaseChange f
  let L := G.sheafPullback (Type (max u (t + 1))) (ProEt.topology Y) (ProEt.topology X)
  let a := G.sheafAdjunctionContinuous (Type (max u (t + 1)))
    (ProEt.topology Y) (ProEt.topology X)
  let : ReflectsLimits (forget (Type (max u (t + 1)))) :=
    reflectsLimits_of_reflectsIsomorphisms
  let : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  let : PreservesFiniteLimits (G.op.lan : (Y.ProEtᵒᵖ ⥤ Type (max u (t + 1))) ⥤
      X.ProEtᵒᵖ ⥤ Type (max u (t + 1))) :=
    by
      let : AB5OfSize.{t, t + 1} (Type (max u (t + 1))) :=
        AB5OfSize_shrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
      exact preservesFiniteLimits_op_lan_of_flat G
  let : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits G
      (Type (max u (t + 1))) (ProEt.topology Y) (ProEt.topology X)
  obtain ⟨RI, I, c, T, hT, hobj, hmap, ⟨am⟩⟩ :=
    SheafOfModules.RingedPresentationOnSites.continuous_ringed_pullback_presentation
      G L a (completedIntegralCommRingSheafUnrestricted l E X)
      (completedIntegralCommRingSheafUnrestricted l E Y) (coefficientMap l E f)
  let := hT
  have am' : T ⊣ push l E f := by
    unfold push
    let q := ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
      (coefficientMap l E f))
    have hq : q = (⟨Functor.whiskerRight (coefficientMap l E f).hom
        (forget₂ CommRingCat RingCat)⟩) := rfl
    change T ⊣ SheafOfModules.pushforward q at am
    rw [hq] at am
    exact am
  let e : T ≅ pull l E f := am'.leftAdjointUniq (adjunction l E f)
  obtain ⟨F, ε, hkan, hε⟩ :=
    SheafOfModules.ringedPullbackCochainPresentation L _ a I c T hobj hmap
  letI := (fun {A B : Type _} [Category.{_} A] [d : Category.{_} B] (_ : A ⥤ B) ↦ d) F
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  let d := Functor.isoWhiskerRight ec
    (DerivedCategory.Q (C := integralTowerModules l E X))
  let εc := ε ≫ d.hom
  have hεc (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
      IsIso (εc.app P.obj) := by
    have hp : integralOperationsGoodComplex l E Y P.obj := by
      with_unfolding_all exact P.property
    unfold integralOperationsGoodComplex at hp
    letI := hε P.obj hp.1 hp.2
    change IsIso (ε.app P.obj ≫ d.hom.app P.obj)
    infer_instance
  with_unfolding_all refine ⟨F, εc, ⟨?_⟩, ?_⟩
  · with_unfolding_all exact (Functor.isRightKanExtension_iff_of_iso₂
      ε εc d (Iso.refl _) (by simp [εc])).mp hkan
  · intro P
    with_unfolding_all exact hεc P

/-- The defining augmentation law of the recorded completion unit.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
theorem rawAmbientCompletionUnit_app (W : Scheme.{t})
    (P : (ambientGood l E W).FullSubcategory) :
    (ambientCompletionUnit l E W).app ((ambientGoodLocalization l E W).obj P) ≫
      (ambientCompletionComparison l E W).hom.app P =
        (ambientQ l E W).map (ambientRoosUnit l E W P.obj) := by
  unfold ambientCompletionUnit ambientCompletionComparison ambientCompletion ambientQ
  with_unfolding_all exact
    ((IntegralOnSlice.completionUnit_existsUnique l E W none).exists.choose_spec
      (show (IntegralOnSlice.Good l E W none).FullSubcategory from P))

/-- Good representatives localize to the ambient derived category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem rawAmbientGoodLocalization (W : Scheme.{t}) :
    (ambientGoodLocalization l E W).IsLocalization
      ((ambientQuasiIso l E W).inverseImage (ambientGood l E W).ι) := by
  unfold ambientGoodLocalization ambientQ ambientQuasiIso
  with_unfolding_all exact IntegralOnSlice.goodLocalization l E W none

universe a₂ b₂ c₂ d₂ e₂ f₂

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The operation constructions with their compatibility laws. Carrier categories
and good objects are fixed parameters, so the laws share exactly the same functors.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
structure AmbientOperationData
    (I : Type a₂) [Category.{b₂} I]
    (C : I → Type c₂) [cc : ∀ W, Category.{d₂} (C W)]
    (D : I → Type e₂) [dd : ∀ W, Category.{f₂} (D W)]
    (P K : ∀ W, ObjectProperty (C W))
    (V : ∀ W, MorphismProperty (C W)) where
  Q (W : I) : C W ⥤ D W
  totalTensor (W : I) : C W × C W ⥤ C W
  ordinaryTensor (W : I) : D W × D W ⥤ D W
  roos (W : I) : (ℕᵒᵖ ⥤ C W) ⥤ C W
  quotientTower (W : I) : C W ⥤ (ℕᵒᵖ ⥤ C W)
  pullComplex {X Y : I} (f : X ⟶ Y) : C Y ⥤ C X
  recordedPullTower {X Y : I} (f : X ⟶ Y) : C Y ⥤ (ℕᵒᵖ ⥤ C X)
  recordedTensorTower (W : I) : C W × C W ⥤ (ℕᵒᵖ ⥤ C W)
  completion (W : I) : D W ⥤ D W
  completionUnit (W : I) : 𝟭 (D W) ⟶ completion W
  derivedPull {X Y : I} (f : X ⟶ Y) : D Y ⥤ D X
  completedTensor (W : I) : D W × D W ⥤ D W
  qLocalization (W : I) : (Q W).IsLocalization (V W)
  pullGood {X Y : I} (f : X ⟶ Y) (Z : C Y) : P Y Z → P X ((pullComplex f).obj Z)
  tensorGood (W : I) (Z Z' : C W) : P W Z → P W Z' →
    P W ((totalTensor W).obj (Z, Z'))
  pullTowerIso {X Y : I} (f : X ⟶ Y) :
    pullComplex f ⋙ quotientTower X ≅ recordedPullTower f
  tensorTowerIso (W : I) : totalTensor W ⋙ quotientTower W ≅ recordedTensorTower W
  tensorModelComparison (W : I) :
    (K W).ι.prod (K W).ι ⋙ totalTensor W ⋙ Q W ≅
      ((K W).ι ⋙ Q W).prod ((K W).ι ⋙ Q W) ⋙ ordinaryTensor W
  pullComparison {X Y : I} (f : X ⟶ Y) :
    ((P Y).ι ⋙ Q Y) ⋙ derivedPull f ≅ (P Y).ι ⋙ (recordedPullTower f ⋙ roos X) ⋙ Q X
  tensorComparison (W : I) :
    ((P W).ι ⋙ Q W).prod ((P W).ι ⋙ Q W) ⋙ completedTensor W ≅
      (P W).ι.prod (P W).ι ⋙ (recordedTensorTower W ⋙ roos W) ⋙ Q W
  completionComparison (W : I) :
    ((P W).ι ⋙ Q W) ⋙ completion W ≅ (P W).ι ⋙ (quotientTower W ⋙ roos W) ⋙ Q W
  roosUnit (W : I) (Z : C W) : Z ⟶ (quotientTower W ⋙ roos W).obj Z
  unitLaw (W : I) (Z : (P W).FullSubcategory) :
    (completionUnit W).app (((P W).ι ⋙ Q W).obj Z) ≫
      (completionComparison W).hom.app Z = (Q W).map (roosUnit W Z.obj)
  goodLocalization (W : I) : ((P W).ι ⋙ Q W).IsLocalization ((V W).inverseImage (P W).ι)
  derivedData {X Y : I} (f : X ⟶ Y) :
    ∃ (F : D Y ⥤ D X) (ε : Q Y ⋙ F ⟶ pullComplex f ⋙ Q X),
      F.IsRightKanExtension ε ∧ ∀ Z : (P Y).FullSubcategory, IsIso (ε.app Z.obj)

/-- Equality to a constructed value specifies it uniquely.
Source: equality reflexivity (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem operationDataCopy_existsUnique {A : Type*} (a : A) : ∃! b : A, b = a :=
  ⟨a, rfl, fun _ h ↦ h⟩

/-- Share a constructed value through its proved specification.
Source: the preceding unique construction
(blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def operationDataCopy {A : Type*} (a : A) : A :=
  (operationDataCopy_existsUnique a).exists.choose

/-- Package the recorded constructions and their already proved compatibility laws.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def rawAmbientPackage : AmbientOperationData Scheme
    (ambientCx l E) (ambientD l E) (ambientGood l E) (ambientFlat l E)
      (ambientQuasiIso l E) where
  Q := ambientQ l E
  totalTensor := ambientTotalTensor l E
  ordinaryTensor := ambientOrdinaryTensor l E
  roos := ambientRoos l E
  quotientTower := ambientQuotientTower l E
  pullComplex := ambientPullComplex l E
  recordedPullTower := ambientRecordedPullTower l E
  recordedTensorTower := ambientRecordedTensorTower l E
  completion := ambientCompletion l E
  completionUnit := ambientCompletionUnit l E
  derivedPull := ambientPull l E
  completedTensor := ambientCompletedTensor l E
  qLocalization := ambientQ_isLocalization l E
  pullGood := ambientPullGood l E
  tensorGood := ambientTensorGood l E
  pullTowerIso := ambientPullTowerIso l E
  tensorTowerIso := ambientTensorTowerIso l E
  tensorModelComparison := ambientTensorModelComparison l E
  pullComparison := ambientPullComparison l E
  tensorComparison := ambientTensorComparison l E
  completionComparison := ambientCompletionComparison l E
  roosUnit := ambientRoosUnit l E
  unitLaw := rawAmbientCompletionUnit_app l E
  goodLocalization := rawAmbientGoodLocalization l E
  derivedData f := by
    obtain ⟨F, ε, hF, hε⟩ := rawAmbientDerivedData l E f
    exact ⟨F, ε, hF.isRightKanExtension, hε⟩

/-- The same recorded operations, shared as one specified record.
Source: the preceding constructed package
(blueprint: lem-pur-integral-ambient-operation-models).

The specifying theorem is proved by reflexivity. It determines the entire record by
literal equality to rawAmbientPackage, rather than selecting unspecified operation data. -/
@[irreducible] def ambientPackage := operationDataCopy (rawAmbientPackage l E)

/-- The localization functor of the recorded ambient derived category.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelQ (W : Scheme.{t}) : ambientCx l E W ⥤ ambientD l E W :=
  (ambientPackage l E).Q W

/-- Ordinary pullback in the recorded ambient cochain presentation.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelPullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ ambientCx l E X :=
  (ambientPackage l E).pullComplex f

/-- The ordinary total tensor of the recorded slice coefficient presentation.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelTotalTensor (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ ambientCx l E W :=
  (ambientPackage l E).totalTensor W

/-- Ordinary derived tensor in the recorded ambient category.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelOrdinaryTensor (W : Scheme.{t}) :
    ambientD l E W × ambientD l E W ⥤ ambientD l E W :=
  (ambientPackage l E).ordinaryTensor W

/-- The whole ordinary tensor model comparison, with its category data shared once.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelTensorModelComparison (W : Scheme.{t}) :
    ((ambientFlat l E W).ι.prod (ambientFlat l E W).ι) ⋙
      modelTotalTensor l E W ⋙ modelQ l E W ≅
        (((ambientFlat l E W).ι ⋙ modelQ l E W).prod
          ((ambientFlat l E W).ι ⋙ modelQ l E W)) ⋙ modelOrdinaryTensor l E W :=
  (ambientPackage l E).tensorModelComparison W

/-- Localization for the shared ambient operation record.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
@[instance] theorem modelQ_isLocalization (W : Scheme.{t}) :
    (modelQ l E W).IsLocalization (ambientQuasiIso l E W) :=
  (ambientPackage l E).qLocalization W

/-- The recorded ordinary tensor comparison on good representatives.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorRepresentative (W : Scheme.{t})
    (P Q : (ambientGood l E W).FullSubcategory) :
    (modelQ l E W).obj ((modelTotalTensor l E W).obj (P.obj, Q.obj)) ≅
      (modelOrdinaryTensor l E W).obj
        ((modelQ l E W).obj P.obj, (modelQ l E W).obj Q.obj) :=
  (modelTensorModelComparison l E W).app
    (⟨P.obj, ambientGoodFlat l E W P.obj P.property⟩,
      ⟨Q.obj, ambientGoodFlat l E W Q.obj Q.property⟩)

attribute [local irreducible] tensorRepresentative

set_option genSizeOfSpec false in
set_option genInjectivity false in
private structure DescendedCompletion
    {R S A D : Type*} [Category* R] [Category* S] [Category* A] [Category* D]
    (L : R ⥤ S) {F G : S ⥤ D} {H : R ⥤ A} {Q V : A ⥤ D} {T : R ⥤ D}
    (C : D ⥤ D) (η : 𝟭 D ⟶ C)
    (e : L ⋙ F ≅ H ⋙ Q) (c : Q ⋙ C ≅ V) (b : H ⋙ V ≅ T) (g : L ⋙ G ≅ T)
    (u : ∀ P : A, Q.obj P ⟶ V.obj P) where
  comparison : F ⋙ C ≅ G
  normalization : ∀ P : R,
    comparison.hom.app (L.obj P) ≫ g.hom.app P =
      C.map (e.hom.app P) ≫ c.hom.app (H.obj P) ≫ b.hom.app P
  augmentation : ∀ P : R,
    η.app (F.obj (L.obj P)) ≫ comparison.hom.app (L.obj P) ≫ g.hom.app P =
      e.hom.app P ≫ u (H.obj P) ≫ b.hom.app P

set_option genSizeOfSpec false in
set_option genInjectivity false in
private structure DerivedPresentation (X Y : Scheme.{t}) (f : X ⟶ Y) where
  F : ambientD l E Y ⥤
    ambientD l E X
  ε : modelQ l E Y ⋙ F ⟶ modelPullComplex l E f ⋙ modelQ l E X
  derived : F.IsLeftDerivedFunctor ε
    (ambientQuasiIso l E Y)
  good : ∀ P : (ambientGood l E Y).FullSubcategory,
    IsIso (ε.app P.obj)

set_option maxHeartbeats 200000

end WeilConjectures.IntegralAmbient
