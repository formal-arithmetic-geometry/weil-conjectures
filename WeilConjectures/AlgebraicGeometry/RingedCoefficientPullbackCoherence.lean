/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedCoefficientProjectionDataSupplement
import all WeilConjectures.AlgebraicGeometry.RingedCoefficientPullbackComparisonSupplement
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData

/-! # Normalized coefficient comparisons for inverse image

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E and 07A6
(blueprint: lem-pur-coefficient-pullback-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := K) pX)
  (e : Comparisons g nY nX)

/-- The balanced comparison square and scalar unit equation for inverse image.
These involve only left functors, before taking any direct-image mates.
Source: Stacks 0D6D (blueprint: lem-pur-coefficient-pullback-coherence). -/
structure PullbackCoherence (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX)) : Prop where
  composition : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (N : D J R),
    (g.left T).map ((nY.derived a b).hom.app N) ≫ (e.derived (a ≫ b)).hom.app N =
      (e.derived b).hom.app ((pY a).derived.obj N) ≫
        (pX (g.rings.map b)).derived.map ((e.derived a).hom.app N) ≫
        (targetAssociator g nX a b).hom.app ((g.left R).obj N)
  unit : ∀ (R : Sheaf J CommRingCat.{r}) (N : D J R),
    (e.derived (𝟙 R)).hom.app N ≫
        (eqToIso (congrArg (fun f ↦ (pX f).derived) (g.rings.map_id R)) ≪≫
          uX.derived (g.rings.obj R)).hom.app ((g.left R).obj N) =
      (g.left R).map ((uY.derived R).hom.app N)

/-- Counit-normalized scalar shifts and shift compatibility of the inverse-image
comparisons, balanced associators, and scalar units, before taking mates.
Source: Stacks 07A6; signed cochain calculation for degree-zero scalar factors
(blueprint: lem-pur-coefficient-pullback-coherence). -/
structure PullbackShifts (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX)) where
  [scalarY : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (pY a).derived.CommShift ℤ]
  [scalarX : ∀ {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S), (pX a).derived.CommShift ℤ]
  canonicalY : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (pY a).counit ℤ
  canonicalX : ∀ {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (pX a).counit ℤ
  inverseScalar : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (e.derived a).hom ℤ
  associatorY : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    NatTrans.CommShift (nY.derived a b).hom ℤ
  associatorX : ∀ {R S T : Sheaf K CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    NatTrans.CommShift (nX.derived a b).hom ℤ
  unitY : ∀ R : Sheaf J CommRingCat.{r}, NatTrans.CommShift (uY.derived R).hom ℤ
  unitX : ∀ R : Sheaf K CommRingCat.{r}, NatTrans.CommShift (uX.derived R).hom ℤ

variable (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX))

private theorem insertion_ext {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : Mod J R) (N : Mod K (g.rings.obj S))
    (f h : (g.inverse S).modules.obj ((pY a).ordinary.obj M) ⟶ N)
    (he : uInv.map (insertion nY a M) ≫
        (g.inverse S).moduleUnderlying.inv.app ((pY a).ordinary.obj M) ≫
        (underlying (g.rings.obj S)).map f =
      uInv.map (insertion nY a M) ≫
        (g.inverse S).moduleUnderlying.inv.app ((pY a).ordinary.obj M) ≫
        (underlying (g.rings.obj S)).map h) : f = h := by
  apply (((nY.ordinaryAdjunction a).comp (g.ordinaryAdjunction S)).homEquiv M N).injective
  apply (underlying R).map_injective
  apply (cancel_mono ((g.pushUnderlying S).hom.app N)).1
  change insertion nY a M ≫
      (underlying S).map ((g.ordinaryAdjunction S).homEquiv _ _ f) ≫ _ =
    insertion nY a M ≫
      (underlying S).map ((g.ordinaryAdjunction S).homEquiv _ _ h) ≫ _
  rw [adjunction_underlying, adjunction_underlying]
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
  exact congrArg (adj.homEquiv _ _) he

private theorem insertion_comp {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Mod J R) :
    insertion nY a M ≫ insertion nY b ((pY a).ordinary.obj M) ≫
      (underlying T).map ((nY.ordinary a b).hom.app M) = insertion nY (a ≫ b) M := by
  ext U x
  change ((nY.ordinary a b).hom.app M).val.app U
      (((nY.ordinaryAdjunction b).unit.app ((pY a).ordinary.obj M)).val.app U
        (((nY.ordinaryAdjunction a).unit.app M).val.app U x)) =
    ((nY.ordinaryAdjunction (a ≫ b)).unit.app M).val.app U x
  rw [nY.ordinary_unit, nY.ordinary_unit, nY.ordinary_hom, nY.ordinary_unit]
  simp only [map_one, one_mul]

private theorem insertion_ext_double {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Mod J R) (N : Mod K (g.rings.obj T))
    (f h : (g.inverse T).modules.obj ((pY b).ordinary.obj ((pY a).ordinary.obj M)) ⟶ N)
    (he : uInv.map (insertion nY a M) ≫
        uInv.map (insertion nY b ((pY a).ordinary.obj M)) ≫
        (g.inverse T).moduleUnderlying.inv.app _ ≫ (underlying (g.rings.obj T)).map f =
      uInv.map (insertion nY a M) ≫
        uInv.map (insertion nY b ((pY a).ordinary.obj M)) ≫
        (g.inverse T).moduleUnderlying.inv.app _ ≫ (underlying (g.rings.obj T)).map h) :
    f = h := by
  apply ((((nY.ordinaryAdjunction a).comp (nY.ordinaryAdjunction b)).comp
    (g.ordinaryAdjunction T)).homEquiv M N).injective
  apply (underlying R).map_injective
  apply (cancel_mono ((g.pushUnderlying T).hom.app N)).1
  change insertion nY a M ≫ insertion nY b ((pY a).ordinary.obj M) ≫
      (underlying T).map ((g.ordinaryAdjunction T).homEquiv _ _ f) ≫ _ =
    insertion nY a M ≫ insertion nY b ((pY a).ordinary.obj M) ≫
      (underlying T).map ((g.ordinaryAdjunction T).homEquiv _ _ h) ≫ _
  rw [adjunction_underlying, adjunction_underlying]
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv _ _)
  simpa only [Functor.map_comp, Category.assoc] using he

private def targetOrdinaryAssociator {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) :
    (pX (g.rings.map a)).ordinary ⋙ (pX (g.rings.map b)).ordinary ≅
      (pX (g.rings.map (a ≫ b))).ordinary :=
  nX.ordinary (g.rings.map a) (g.rings.map b) ≪≫
    eqToIso (congrArg (fun f ↦ (pX f).ordinary) (g.rings.map_comp a b).symm)

private theorem insertion_congr {R S : Sheaf J CommRingCat.{r}}
    (a b : R ⟶ S) (h : a = b) (M : Mod J R) :
    insertion nY a M ≫ (underlying S).map
      ((eqToIso (congrArg (fun f ↦ (pY f).ordinary) h)).hom.app M) =
      insertion nY b M := by
  subst b
  simp

private theorem insertion_target_comp {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Mod K (g.rings.obj R)) :
    insertion nX (g.rings.map a) M ≫
      insertion nX (g.rings.map b) ((pX (g.rings.map a)).ordinary.obj M) ≫
      (underlying (g.rings.obj T)).map ((targetOrdinaryAssociator g nX a b).hom.app M) =
      insertion nX (g.rings.map (a ≫ b)) M := by
  dsimp only [targetOrdinaryAssociator, Iso.trans_hom, NatTrans.comp_app]
  simp only [Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc, Category.assoc
    (insertion nX (g.rings.map a) M)]
  rw [insertion_comp]
  exact insertion_congr nX _ _ (g.rings.map_comp a b).symm M

private theorem ordinary_composition {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Mod J R) :
    (g.inverse T).modules.map ((nY.ordinary a b).hom.app M) ≫
      (e.ordinary (a ≫ b)).hom.app M =
    (e.ordinary b).hom.app ((pY a).ordinary.obj M) ≫
      (pX (g.rings.map b)).ordinary.map ((e.ordinary a).hom.app M) ≫
      (targetOrdinaryAssociator g nX a b).hom.app ((g.inverse R).modules.obj M) := by
  apply insertion_ext_double g nY a b M
  have hn := (g.inverse T).moduleUnderlying.inv.naturality
    ((nY.ordinary a b).hom.app M)
  have ha := e.ordinary_insertion a M
  have hb := e.ordinary_insertion b ((pY a).ordinary.obj M)
  have hab := e.ordinary_insertion (a ≫ b) M
  have hi := congrArg (fun f ↦ (underlying (g.rings.obj S)).map f)
    ((nX.ordinaryAdjunction (g.rings.map b)).unit.naturality ((e.ordinary a).hom.app M))
  change (underlying (g.rings.obj S)).map ((e.ordinary a).hom.app M) ≫
      insertion nX (g.rings.map b) _ =
    insertion nX (g.rings.map b) _ ≫ (underlying (g.rings.obj T)).map
      ((pX (g.rings.map b)).ordinary.map ((e.ordinary a).hom.app M)) at hi
  have hy := insertion_comp nY a b M
  have hx := insertion_target_comp g nX a b ((g.inverse R).modules.obj M)
  dsimp only [underlying, Functor.comp_map] at hn ha hb hab hi hy hx ⊢
  simp only [Functor.map_comp]
  rw [← reassoc_of% hn, ← uInv.map_comp_assoc, ← uInv.map_comp_assoc]
  rw [Category.assoc (insertion nY a M), hy, hab]
  rw [reassoc_of% hb, ← reassoc_of% hi, reassoc_of% ha]
  rw [hx]

private theorem insertion_unit (R : Sheaf J CommRingCat.{r}) (M : Mod J R) :
    insertion nY (𝟙 R) M ≫ (underlying R).map ((uY.ordinary R).hom.app M) = 𝟙 _ := by
  ext U x
  change ((uY.ordinary R).hom.app M).val.app U
    (((nY.ordinaryAdjunction (𝟙 R)).unit.app M).val.app U x) = x
  rw [nY.ordinary_unit, uY.multiplication, one_smul]

private theorem ordinary_unit (R : Sheaf J CommRingCat.{r}) (M : Mod J R) :
    (e.ordinary (𝟙 R)).hom.app M ≫
      (eqToIso (congrArg (fun f ↦ (pX f).ordinary) (g.rings.map_id R)) ≪≫
        uX.ordinary (g.rings.obj R)).hom.app ((g.inverse R).modules.obj M) =
    (g.inverse R).modules.map ((uY.ordinary R).hom.app M) := by
  apply insertion_ext g nY (𝟙 R) M
  have hn := (g.inverse R).moduleUnderlying.inv.naturality ((uY.ordinary R).hom.app M)
  have he := e.ordinary_insertion (𝟙 R) M
  have hy := insertion_unit nY uY R M
  have hc := insertion_congr nX _ _ (g.rings.map_id R) ((g.inverse R).modules.obj M)
  have hx := insertion_unit nX uX (g.rings.obj R) ((g.inverse R).modules.obj M)
  dsimp only [underlying, Functor.comp_map] at hn he hy hc hx ⊢
  simp only [Functor.map_comp, Iso.trans_hom, NatTrans.comp_app]
  rw [reassoc_of% he, ← hn, ← uInv.map_comp_assoc, hy]
  erw [uInv.map_id, Category.id_comp]
  rw [reassoc_of% hc, hx]
  erw [Category.comp_id]
  rfl

private theorem computation_counit {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Mod J R) ℤ) :
    computation (pY a) P = (pY a).counit.app ((HomotopyCategory.quotient _ _).obj P) := by
  dsimp only [computation, derivedPullbackComplexComparison, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
    CategoryTheory.Quotient.lift.isLift_hom, CategoryTheory.Quotient.lift.isLift_inv]
  change (pY a).derived.map (𝟙 _) ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  erw [(pY a).derived.map_id, DerivedCategory.Qh.map_id]
  simp only [Category.id_comp, Category.comp_id]

private theorem composition_representative {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (P : CochainComplex (Mod J R) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    (nY.derived a b).hom.app (DerivedCategory.Q.obj P) ≫ computation (pY (a ≫ b)) P =
      (pY b).derived.map (computation (pY a) P) ≫
        computation (pY b) (((pY a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (nY.ordinary a b).hom (.up ℤ)).app P) := by
  simp only [computation_counit]
  exact nY.representative a b P hk hf

private theorem scalar_preserves_flat {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (P : CochainComplex (Mod J R) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((pY a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ i : ℤ, IsFlatOnSite (J := J) (R := S)
        ((((pY a).ordinary.mapHomologicalComplex (.up ℤ)).obj P).X i) := by
  exact isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
    (SuccessiveDerivedQuotient.identityInverse R) a (pY a).ordinary
    (pY a).obj_eq (pY a).map_eq P hk hf

private theorem composition_representative_transport
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) (d : R ⟶ T)
    (h : a ≫ b = d) (P : CochainComplex (Mod J R) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    (nY.derived a b ≪≫ eqToIso (congrArg (fun f ↦ (pY f).derived) h)).hom.app
        (DerivedCategory.Q.obj P) ≫ computation (pY d) P =
      (pY b).derived.map (computation (pY a) P) ≫
        computation (pY b) (((pY a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (nY.ordinary a b ≪≫ eqToIso (congrArg (fun f ↦ (pY f).ordinary) h)).hom
            (.up ℤ)).app P) := by
  subst d
  simpa using composition_representative nY a b P hk hf

private theorem unit_representative_transport
    (R : Sheaf J CommRingCat.{r}) (a : R ⟶ R) (h : a = 𝟙 R)
    (P : CochainComplex (Mod J R) ℤ) (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    (eqToIso (congrArg (fun f ↦ (pY f).derived) h) ≪≫ uY.derived R).hom.app
        (DerivedCategory.Q.obj P) =
      computation (pY a) P ≫ DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (eqToIso (congrArg (fun f ↦ (pY f).ordinary) h) ≪≫ uY.ordinary R).hom
          (.up ℤ)).app P) := by
  subst a
  simpa using uY.representative R P hk hf

private theorem hom_ext_flat {R : Sheaf J CommRingCat.{r}}
    {E : Type*} [Category E] {F G : D J R ⥤ E} (α β : F ⟶ G)
    (h : ∀ (P : CochainComplex (Mod J R) ℤ), P.IsKFlatIndependentCoefficients →
      (∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) →
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) : α = β := by
  ext N
  obtain ⟨P, q, hk, hf, hq, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
    (J := J) (R := R) (DerivedCategory.Q.objPreimage N)
  let := hq
  let i : DerivedCategory.Q.obj P ≅ N :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso N
  apply (cancel_epi (F.map i.hom)).1
  rw [α.naturality, β.naturality]
  rw [h P hk (fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso R (P.X n)).symm (hf n))]

attribute [local irreducible] derivedPullbackComplexComparison

private theorem composition_on_flat [PreservesFiniteLimits uInv]
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Mod J R) ℤ) (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    (g.left T).map ((nY.derived a b).hom.app (DerivedCategory.Q.obj P)) ≫
        (e.derived (a ≫ b)).hom.app (DerivedCategory.Q.obj P) =
      (e.derived b).hom.app ((pY a).derived.obj (DerivedCategory.Q.obj P)) ≫
        (pX (g.rings.map b)).derived.map ((e.derived a).hom.app (DerivedCategory.Q.obj P)) ≫
        (targetAssociator g nX a b).hom.app ((g.left R).obj (DerivedCategory.Q.obj P)) := by
  let I := (g.inverse R).modules.mapHomologicalComplex (.up ℤ)
  have hI := inverse_preserves_flat g nX R P hk hf
  have : IsIso (computation (pX (g.rings.map (a ≫ b))) (I.obj P)) :=
    by simpa only [computationNat_app] using
      computation_isIso nX (g.rings.map (a ≫ b)) (I.obj P) hI.1 hI.2
  apply (cancel_mono ((pX (g.rings.map (a ≫ b))).derived.map
    ((g.inverse R).modules.mapDerivedCategoryFactors.hom.app P) ≫
      computation (pX (g.rings.map (a ≫ b))) (I.obj P))).1
  simp only [Category.assoc]
  have hab := e.representative (a ≫ b) P hk hf
  have ha := e.representative a P hk hf
  erw [hab]
  have hn := (targetAssociator g nX a b).hom.naturality
    ((g.inverse R).modules.mapDerivedCategoryFactors.hom.app P)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  erw [composition_representative_transport nX
    (g.rings.map a) (g.rings.map b) (g.rings.map (a ≫ b))
    (g.rings.map_comp a b).symm (I.obj P) hI.1 hI.2]
  have hma := congrArg (fun f ↦ (pX (g.rings.map b)).derived.map f) ha
  simp only [Functor.map_comp] at hma
  erw [reassoc_of% hma]
  have hc := (computationNat (pY := pX) (g.rings.map b)).naturality
    ((NatTrans.mapHomologicalComplex (e.ordinary a).hom (.up ℤ)).app P)
  dsimp only [Functor.comp_map] at hc
  simp only [computationNat_app] at hc
  change (pX (g.rings.map b)).derived.map (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (e.ordinary a).hom (.up ℤ)).app P)) ≫
      computation (pX (g.rings.map b))
        (((pX (g.rings.map a)).ordinary.mapHomologicalComplex (.up ℤ)).obj (I.obj P)) =
    computation (pX (g.rings.map b))
      (((g.inverse S).modules.mapHomologicalComplex (.up ℤ)).obj
        (((pY a).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map (((pX (g.rings.map b)).ordinary.mapHomologicalComplex
        (.up ℤ)).map ((NatTrans.mapHomologicalComplex (e.ordinary a).hom (.up ℤ)).app P))
    at hc
  conv_rhs =>
    arg 2; arg 2; arg 2
    rw [reassoc_of% hc]
  have hb := scalar_preserves_flat (pY := pY) a P hk hf
  have hnb := (e.derived b).hom.naturality (computation (pY a) P)
  dsimp only [Functor.comp_map] at hnb
  conv_rhs => rw [← reassoc_of% hnb]
  have heb := e.representative b
    (((pY a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) hb.1 hb.2
  conv_rhs =>
    arg 2
    erw [reassoc_of% heb]
  have hy := congrArg (fun f ↦ (g.left T).map f)
    (composition_representative nY a b P hk hf)
  simp only [Functor.map_comp] at hy
  conv_lhs => rw [reassoc_of% hy]
  conv_lhs =>
    arg 2; arg 2
    erw [(g.inverse T).modules.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [← DerivedCategory.Q.map_comp]
  congr 3
  apply congrArg DerivedCategory.Q.map
  ext i : 1
  exact ordinary_composition g nY nX e a b (P.X i)

private theorem unit_on_flat [PreservesFiniteLimits uInv]
    (R : Sheaf J CommRingCat.{r}) (P : CochainComplex (Mod J R) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    (e.derived (𝟙 R)).hom.app (DerivedCategory.Q.obj P) ≫
        (eqToIso (congrArg (fun f ↦ (pX f).derived) (g.rings.map_id R)) ≪≫
          uX.derived (g.rings.obj R)).hom.app ((g.left R).obj (DerivedCategory.Q.obj P)) =
      (g.left R).map ((uY.derived R).hom.app (DerivedCategory.Q.obj P)) := by
  let I := (g.inverse R).modules.mapHomologicalComplex (.up ℤ)
  have hI := inverse_preserves_flat g nX R P hk hf
  apply (cancel_mono ((g.inverse R).modules.mapDerivedCategoryFactors.hom.app P)).1
  have hn := (eqToIso (congrArg (fun f ↦ (pX f).derived) (g.rings.map_id R)) ≪≫
    uX.derived (g.rings.obj R)).hom.naturality
      ((g.inverse R).modules.mapDerivedCategoryFactors.hom.app P)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Category.assoc]
  erw [← hn]
  erw [unit_representative_transport uX _ _ (g.rings.map_id R) (I.obj P) hI.1 hI.2]
  have he := e.representative (𝟙 R) P hk hf
  have he' := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex
      (eqToIso (congrArg (fun f ↦ (pX f).ordinary) (g.rings.map_id R)) ≪≫
        uX.ordinary (g.rings.obj R)).hom (.up ℤ)).app (I.obj P))) he
  simp only [Category.assoc] at he'
  have ho : (NatTrans.mapHomologicalComplex (e.ordinary (𝟙 R)).hom (.up ℤ)).app P ≫
      (NatTrans.mapHomologicalComplex
        (eqToIso (congrArg (fun f ↦ (pX f).ordinary) (g.rings.map_id R)) ≪≫
          uX.ordinary (g.rings.obj R)).hom (.up ℤ)).app (I.obj P) =
      I.map ((NatTrans.mapHomologicalComplex (uY.ordinary R).hom (.up ℤ)).app P) := by
    ext i : 1
    exact ordinary_unit g nY nX e uY uX R (P.X i)
  have hnu := (g.inverse R).modules.mapDerivedCategoryFactors_hom_naturality
    ((NatTrans.mapHomologicalComplex (uY.ordinary R).hom (.up ℤ)).app P)
  have hu := congrArg (fun f ↦ (g.left R).map f) (uY.representative R P hk hf)
  simp only [Functor.map_comp] at hu
  apply he'.trans
  erw [← DerivedCategory.Q.map_comp, ho]
  calc
    _ = (g.left R).map (computation (pY (𝟙 R)) P) ≫
        (g.inverse R).modules.mapDerivedCategory.map
          (DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (uY.ordinary R).hom (.up ℤ)).app P)) ≫
        (g.inverse R).modules.mapDerivedCategoryFactors.hom.app P :=
      congrArg (fun f ↦ (g.left R).map (computation (pY (𝟙 R)) P) ≫ f) hnu.symm
    _ = _ := by rw [← Category.assoc, ← hu]

/-- The canonical pullback comparisons respect scalar composition and multiplication
units. This is a coherence assertion about already constructed tensor comparisons;
it asserts no projection mate law.

Source: Stacks Project, Cohomology on Sites, Tag 0D6D
(lemma-derived-pullback-composition); the explicit balanced tensor calculation
in its proof
(blueprint: lem-pur-coefficient-pullback-coherence).

Proof:
1. Compute all functors on a common flat-term K-flat representative P. The
canonical computation maps in the two coefficient normalizations are invertible
there. Pullback preserves K-flat flat-term representatives, so its computation
may use the same P and its inverse-image complex.
2. The ordinary comparison is pinned by scalar insertion: the composite scalar
extension and inverse-image adjunctions detect equality after insertion. The
normalized associators take double insertion to composite insertion. Their
naturality and the insertion equations therefore give equal ordinary maps and
equal chain maps. The representative equations for e and n identify this equality with the
composition equation. Cancel the invertible computation maps and use a K-flat
resolution of each derived object to obtain PullbackCoherence.composition.
3. The two ordinary scalar unitors are multiplication, by ScalarUnits.multiplication.
The insertion-normalized comparison for an identity coefficient map has the
same multiplication equation. Transport this equality through the representative
formulas of e and the units and cancel the computation maps. This proves
PullbackCoherence.unit, including the rings.map_id transport.
The source and target unit identifications are multiplication, rather than
arbitrary choices of an equivalence with the identity. No projection-mate law
is included in this left tensor square. -/
theorem coefficientPullbackCoherence [PreservesFiniteLimits uInv] :
    PullbackCoherence g nY nX e uY uX := by
  constructor
  · intro R S T a b N
    let α : ((pY a).derived ⋙ (pY b).derived) ⋙ g.left T ⟶
        g.left R ⋙ (pX (g.rings.map (a ≫ b))).derived :=
      Functor.whiskerRight (nY.derived a b).hom (g.left T) ≫ (e.derived (a ≫ b)).hom
    let β : ((pY a).derived ⋙ (pY b).derived) ⋙ g.left T ⟶
        g.left R ⋙ (pX (g.rings.map (a ≫ b))).derived :=
      Functor.whiskerLeft (pY a).derived (e.derived b).hom ≫
        Functor.whiskerRight (e.derived a).hom (pX (g.rings.map b)).derived ≫
        Functor.whiskerLeft (g.left R) (targetAssociator g nX a b).hom
    exact NatTrans.congr_app (hom_ext_flat α β (composition_on_flat g nY nX e a b)) N
  · intro R N
    let α : (pY (𝟙 R)).derived ⋙ g.left R ⟶ g.left R :=
      (e.derived (𝟙 R)).hom ≫ Functor.whiskerLeft (g.left R)
        (eqToIso (congrArg (fun f ↦ (pX f).derived) (g.rings.map_id R)) ≪≫
          uX.derived (g.rings.obj R)).hom
    let β : (pY (𝟙 R)).derived ⋙ g.left R ⟶ g.left R :=
      Functor.whiskerRight (uY.derived R).hom (g.left R)
    exact NatTrans.congr_app (hom_ext_flat α β (unit_on_flat g nY nX e uY uX R)) N

end SheafOfModules.RingedCoefficientProjection

end
