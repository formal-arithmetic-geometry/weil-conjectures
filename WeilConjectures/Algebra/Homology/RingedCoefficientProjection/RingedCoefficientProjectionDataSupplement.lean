/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

public import WeilConjectures.AlgebraicGeometry.RingedCoefficientProjectionData
public import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteModuleEquivalence
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
/-!
# Interfaces for coefficient projection cocycles

Source: Stacks Project, Cohomology on Sites, Tags 07A7 and 0E47; Tags 0D6D,
0D6E and 07A6 for the canonical comparisons and adjunctions
(blueprint: def-pur-ringed-coefficient-projection-data).

The auxiliary records present the specified geometric operations, comparison and
unit maps. Ordinary insertion and K-flat computation fix all comparisons; the
cocycle is a conclusion, never part of the input. The same assertion is stated
on the actual vertical sequence sites, before evaluation or derived inverse limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r

open CategoryTheory CategoryTheory.Limits
open SheafOfModules
open scoped ChangeOfRings

namespace SheafOfModules.RingedCoefficientProjection

open WeilConjectures.SemilinearSections (Mod D)

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(blueprint: def-pur-ringed-coefficient-projection-data). -/
instance (priority := 100000) cachedSheafifyModules (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{r} := inferInstance

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(blueprint: def-pur-ringed-coefficient-projection-data). -/
instance (priority := 100000) cachedWeakSheafifyModules (J : GrothendieckTopology C) :
    HasWeakSheafify J AddCommGrpCat.{r} := inferInstance

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(blueprint: def-pur-ringed-coefficient-projection-data). -/
instance (priority := 100000) cachedLocalEquivalences (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{r} := inferInstance

attribute [instance] Geometry.inverseAdditive Geometry.inverseLimits Geometry.inverseColimits
  Geometry.pushAdditive Geometry.kInjective

variable {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)

/-- The actual K-injective derived module direct image.
Source: Stacks 0D6E (blueprint: def-pur-ringed-coefficient-projection-data). -/
abbrev Geometry.right (R : Sheaf J CommRingCat.{r}) := (g.push R).rightDerivedFunctor

/-- The canonical derived adjunction, with no independently chosen unit or counit.
Source: Stacks 07A6 (blueprint: def-pur-ringed-coefficient-projection-data). -/
abbrev Geometry.adjunction (R : Sheaf J CommRingCat.{r}) :=
  (g.ordinaryAdjunction R).mapDerivedCategoryRightDerivedAdjunction

/-- Scalar multiplication is the coefficient-unit identification, on sheaves and
on K-flat representatives, rather than an arbitrary self-equivalence.
Source: Stacks 03EL, 0D6D (blueprint: def-pur-ringed-coefficient-projection-data). -/
structure ScalarUnits {p : Scalars.{c, v, r} J} where
  ordinary : ∀ R : Sheaf J CommRingCat.{r}, (p (𝟙 R)).ordinary ≅ 𝟭 (Mod J R)
  multiplication : ∀ (R : Sheaf J CommRingCat.{r}) (M : Mod J R) (U : Cᵒᵖ)
    (s : R.obj.obj U) (x : M.val.obj U),
    ((ordinary R).hom.app M).val.app U
      (_root_.SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (p (𝟙 R)) M U s x) = s • x
  derived : ∀ R : Sheaf J CommRingCat.{r}, (p (𝟙 R)).derived ≅ 𝟭 (D J R)
  representative : ∀ (R : Sheaf J CommRingCat.{r}) (P : CochainComplex (Mod J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    (∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) →
    (derived R).hom.app (DerivedCategory.Q.obj P) =
      computation (p (𝟙 R)) P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ordinary R).hom (.up ℤ)).app P)

variable {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r, max c v (r + 1)}
      (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r, max c v (r + 1)}
      (J := K) pX)

variable (e : Comparisons g nY nX)

/-- The specified coefficient projection is exactly the mate under the B-adjunction.
It is not assumed invertible. The mate formula gives the unit--comparison--counit
word, whose transpose is S_a applied to the A-counit after the comparison.
Source: Stacks 07A7 (blueprint: def-pur-ringed-coefficient-projection-data). -/
def comparison {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    g.right R ⋙ (pY a).derived ⟶ (pX (g.rings.map a)).derived ⋙ g.right S :=
  (mateEquiv (g.adjunction R) (g.adjunction S)
    (TwoSquare.mk _ _ _ _ (e.derived a).hom)).natTrans

/-- Balanced associativity on X, including the functorial equality of inverse-image
ring maps. Source: Stacks 0D6D
(blueprint: def-pur-ringed-coefficient-projection-data). -/
def targetAssociator {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) :
    (pX (g.rings.map a)).derived ⋙ (pX (g.rings.map b)).derived ≅
      (pX (g.rings.map (a ≫ b))).derived :=
  nX.derived (g.rings.map a) (g.rings.map b) ≪≫
    eqToIso (congrArg (fun f ↦ (pX f).derived) (g.rings.map_comp a b).symm)

/-- The successive comparison with both balanced identifications inserted.
Source: Stacks 0E47 (blueprint: def-pur-ringed-coefficient-projection-data). -/
def successive {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : D K (g.rings.obj R)) :
    (pY (a ≫ b)).derived.obj ((g.right R).obj M) ⟶
      (g.right T).obj ((pX (g.rings.map (a ≫ b))).derived.obj M) :=
  (nY.derived a b).inv.app ((g.right R).obj M) ≫
    (pY b).derived.map ((comparison g nY nX e a).app M) ≫
    (comparison g nY nX e b).app ((pX (g.rings.map a)).derived.obj M) ≫
    (g.right T).map ((targetAssociator g nX a b).hom.app M)

/-- All equalities are in the changed coefficient category, with arbitrary derived
inputs. The commuting-square formula is also coefficient-map naturality of the
family, and explicitly retains the equality of the two composite ring maps.
Source: Stacks 0E47, 07A7 (blueprint: def-pur-ringed-coefficient-projection-data). -/
structure Laws (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX)) : Prop where
  cocycle : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : D K (g.rings.obj R)),
    (nY.derived a b).hom.app ((g.right R).obj M) ≫
        (comparison g nY nX e (a ≫ b)).app M =
      (pY b).derived.map ((comparison g nY nX e a).app M) ≫
        (comparison g nY nX e b).app ((pX (g.rings.map a)).derived.obj M) ≫
        (g.right T).map ((targetAssociator g nX a b).hom.app M)
  identity : ∀ (R : Sheaf J CommRingCat.{r}) (M : D K (g.rings.obj R)),
    (comparison g nY nX e (𝟙 R)).app M ≫
        (g.right R).map
          ((eqToIso (congrArg (fun f ↦ (pX f).derived) (g.rings.map_id R)) ≪≫
            uX.derived (g.rings.obj R)).hom.app M) =
      (uY.derived R).hom.app ((g.right R).obj M)
  square : ∀ {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ V) (a' : R ⟶ T) (b' : T ⟶ V)
    (h : a ≫ b = a' ≫ b') (M : D K (g.rings.obj R)),
    successive g nY nX e a b M ≫
        (g.right V).map (eqToHom
          (congrArg (fun f ↦ (pX (g.rings.map f)).derived.obj M) h)) =
      eqToHom (congrArg (fun f ↦ (pY f).derived.obj ((g.right R).obj M)) h) ≫
        successive g nY nX e a' b' M

end SheafOfModules.RingedCoefficientProjection
