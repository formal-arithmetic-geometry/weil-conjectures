/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantFiniteComplexRealization
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import WeilConjectures.Algebra.Homology.Scalar.ScalarHomExtensionKFlat
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantFiniteComplexRealization
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumCompleted
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.SmoothPurity.ChangeOfRingsKFlatIndependentCoefficients

/-!
# Completed adic coefficient datum and its strict reduction tower

Source: blueprint, proper base change, order 1239; Stacks Tags 099L and 099M
(blueprint: def-weil-pbc-adic-coefficient-datum).

The site has object universe t+1 and morphism universe t. Coefficients and modules
are in t+1. The ambient ring is the actual inverse limit of the finite constant
quotient sheaves, not the constant sheaf associated to the original ring.

## Main definitions

* `ProEtaleAdicCoefficientDatum`: coefficient hypotheses.
* `adicDatumRing`: the actual completed coefficient sheaf.
* `adicDatumAdjunction`: normalized derived scalar adjunction.
* `adicDatumDerivedTower`: universal strict quotient tower.
* `adicDatumModelTower`: its explicit K-flat computation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t r u v uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory

attribute [local irreducible] Functor.mapHomotopyCategory
  Functor.mapHomotopyCategoryFactors

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

section FiniteCoefficientComparison
variable (P : Type (t + 1)) [CommRing P] [Finite P]
variable [TopologicalSpace P] [DiscreteTopology P]

end FiniteCoefficientComparison

/-- The ambient unbounded derived category, with the standard localization.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumDerived := completedConstantDerived (adicDatumModules T d)

/-- Strict inverse sequences of completed-coefficient module sheaves; index n is n+1.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumTowers := ℕᵒᵖ ⥤ adicDatumModules T d

/-- One K-flat representative, without restricting the derived object.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
structure AdicDatumModel (K : adicDatumDerived T d) where
  complex : CochainComplex (adicDatumModules T d) ℤ
  isKFlat : CochainComplex.IsAcyclicTensorKFlat (R := adicDatumRing T d) complex
  realization : (completedConstantQ _).obj complex ≅ K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section ScalarChange

variable {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)

/-- The two presentations select the same ordinary tensor functor.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: both are the ordinary functor in the same independent-coefficient witness,
with the same standard derived-category instances. -/
theorem adicDatumOrdinaryExtension_eq :
    completedConstantExtension T φ = reductionChange T φ := by
  rfl

/-- The homotopy localization with the same standard derived-category instance.
Source: Tag 05RU (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumQh (B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  @DerivedCategory.Qh (completedConstantModules T B) _ _ (HasDerivedCategory.standard _)

/-- The scalar derived pair with its specification stated in this coefficient presentation.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: take the universal pair in derivedChangeOfRingsIndependentCoefficients, using
its specified ordinary extension functor and the standard localizations. -/
theorem adicDatumScalarDerived_exists :
    ∃ (F : completedConstantDerived (completedConstantModules T R) ⥤
        completedConstantDerived (completedConstantModules T S))
      (ε : adicDatumQh T R ⋙ F ⟶
        (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ adicDatumQh T S),
      F.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (completedConstantModules T R) (.up ℤ)) ∧
        (∃ (_ : F.CommShift ℤ), F.IsTriangulated) ∧
        ∀ C : CochainComplex (completedConstantModules T R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := R) C →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) := by
  change ∃ F, reductionDerivedSpec T φ F
  exact reductionDerivedExistence T φ

/-- The universal scalar pair as data, retaining its counit and K-flat computation.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
structure AdicDatumScalarPair where
  functor : completedConstantDerived (completedConstantModules T R) ⥤
    completedConstantDerived (completedConstantModules T S)
  counit : adicDatumQh T R ⋙ functor ⟶
    (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ adicDatumQh T S
  universal : functor.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (completedConstantModules T R) (.up ℤ))
  triangulated : ∃ (_ : functor.CommShift ℤ), functor.IsTriangulated
  computation (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients (R := R) C) :
    IsIso (counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C))

/-- The specified universal pair, packaged once so its fields have a stable interface.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
@[irreducible]
def adicDatumScalarPair : AdicDatumScalarPair T φ where
  functor := (adicDatumScalarDerived_exists T φ).choose
  counit := (adicDatumScalarDerived_exists T φ).choose_spec.choose
  universal := (adicDatumScalarDerived_exists T φ).choose_spec.choose_spec.1
  triangulated := (adicDatumScalarDerived_exists T φ).choose_spec.choose_spec.2.1
  computation := (adicDatumScalarDerived_exists T φ).choose_spec.choose_spec.2.2

/-- Derived extension from the existing universal K-flat derived pair.
Its comparison counit is retained below, so no unrelated functor is chosen.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumExtension :
    completedConstantDerived (completedConstantModules T R) ⥤
      completedConstantDerived (completedConstantModules T S) :=
  (adicDatumScalarPair T φ).functor

/-- The universal derived counit on homotopy complexes.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumExtensionCounit :
    adicDatumQh T R ⋙ adicDatumExtension T φ ⟶
      (reductionChange T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        adicDatumQh T S :=
  (adicDatumScalarPair T φ).counit

/-- Restriction changes only the scalar action and is exact.
Source: order 1239; Tag 03D3 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the underlying abelian sheaves, kernels and sheafified cokernels are unchanged
by restriction. Their universal maps remain linear for the restricted action. -/
theorem adicDatumRestriction_exact :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)) ∧
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)) := by
  exact SheafOfModules.restrictScalars_exact_kflat ((adicLisseForget T).map φ)

/-- Exact derived restriction of scalars.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumRestriction :
    completedConstantDerived (completedConstantModules T S) ⥤
      completedConstantDerived (completedConstantModules T R) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  letI := (adicDatumRestriction_exact T φ).1
  letI := (adicDatumRestriction_exact T φ).2
  (SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ)).mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completedExtension_obj (M : completedConstantModules T R) :
    (reductionChange T φ).obj M = SheafOfModules.changeOfRings φ M :=
  reductionChange_obj_eq T φ M

private theorem completedExtension_map {M N : completedConstantModules T R} (a : M ⟶ N) :
    (reductionChange T φ).map a =
      eqToHom (completedExtension_obj T φ M) ≫ SheafOfModules.changeOfRingsHom φ M a ≫
        eqToHom (completedExtension_obj T φ N).symm :=
  reductionChange_map_eq T φ a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicDatumOrdinaryAdjunction_formula :
    ∃ a : reductionChange T φ ⊣
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ),
      ∀ (M : completedConstantModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = adicDatumTensorSection T φ M U 1 x := by
  refine ⟨(ordinaryAdjunction_exists T φ).choose, ?_⟩
  intro M U x
  exact reductionUnit_apply T φ M U x

/-- The exact restriction comparison, retaining its specified localization maps.
Source: Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumRestrictionComparison :
    adicDatumQh T S ⋙ adicDatumRestriction T φ ≅
      (SheafOfModules.restrictScalars.{t + 1}
        ((adicLisseForget T).map φ)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ adicDatumQh T R :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  letI := (adicDatumRestriction_exact T φ).1
  letI := (adicDatumRestriction_exact T φ).2
  (SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ)).mapDerivedCategoryFactorsh

/-- The derived adjunction is fixed by compatibility with the ordinary normalized
adjunction and the universal derived counit, rather than by bare existence.
Source: order 1239; Tags 06YY and 09T5 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: derive the ordinary tensor/restriction adjunction, whose unit is 1 tensor m.
Restriction is exact. Identify its derived functor with exact restriction using its
localization comparison, and identify its left adjoint with the universal left-derived
pair already chosen above. The universal property fixes the displayed hom-equivalence
formula on homotopy representatives, which determines the adjunction after localization. -/
theorem adicDatumAdjunction_exists :
    ∃ adj : adicDatumExtension T φ ⊣ adicDatumRestriction T φ,
      ∀ (C : HomotopyCategory (completedConstantModules T R) (ComplexShape.up ℤ))
        (D : HomotopyCategory (completedConstantModules T S) (ComplexShape.up ℤ))
        (f : ((reductionChange T φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj C ⟶ D),
        adj.homEquiv ((adicDatumQh T R).obj C) ((adicDatumQh T S).obj D)
          ((adicDatumExtensionCounit T φ).app C ≫ (adicDatumQh T S).map f) =
        (adicDatumQh T R).map
          ((adicDatumOrdinaryAdjunction T φ).mapHomotopyCategory (ComplexShape.up ℤ)
            |>.homEquiv C D f) ≫ (adicDatumRestrictionComparison T φ).inv.app D := by
  let := HasDerivedCategory.standard (completedConstantModules T R)
  let := HasDerivedCategory.standard (completedConstantModules T S)
  let := (adicDatumRestriction_exact T φ).1
  let := (adicDatumRestriction_exact T φ).2
  apply SheafOfModules.sheafRingDerivedHomComparison φ
    (reductionChange T φ) (completedExtension_obj T φ)
    (completedExtension_map T φ) (adicDatumOrdinaryAdjunction T φ)
    (adicDatumExtension T φ) (adicDatumExtensionCounit T φ)
  exact (adicDatumScalarPair T φ).universal

/-- The normalized derived scalar adjunction.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumAdjunction : adicDatumExtension T φ ⊣ adicDatumRestriction T φ :=
  (adicDatumAdjunction_exists T φ).choose

/-- The universal scalar-extension comparison, now on complexes rather than homotopy
classes, using precisely the two localization comparison isomorphisms.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumComplexCounit (C : CochainComplex (completedConstantModules T R) ℤ) :
    (adicDatumExtension T φ).obj ((completedConstantQ _).obj C) ⟶
      (completedConstantQ _).obj
        (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  (adicDatumExtension T φ).map ((DerivedCategory.quotientCompQhIso _).inv.app C) ≫
    (adicDatumExtensionCounit T φ).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≫
    (adicDatumQh T S).map
      (((reductionChange T φ).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app C) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)

/-- The specified comparison is invertible on every K-flat complex.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the universal derived counit is invertible on K-flat homotopy representatives
by derivedChangeOfRingsIndependentCoefficients. The two changes between homotopy
and complex localization above are isomorphisms, as is their image under a functor. -/
theorem adicDatumComplexCounit_isIso
    (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := R) C) :
    IsIso (adicDatumComplexCounit T φ C) := by
  let := HasDerivedCategory.standard (completedConstantModules T R)
  let := HasDerivedCategory.standard (completedConstantModules T S)
  have : IsIso ((adicDatumExtensionCounit T φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) :=
    (adicDatumScalarPair T φ).computation C
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat C).2 hC)
  unfold adicDatumComplexCounit
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end ScalarChange

/-- The actual limit projection to the positive quotient level n+1.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumProjection (n : ℕ) :
    adicDatumRing T d ⟶ (adicLisseRingSystem T d.ideal).obj (op n) :=
  limit.π (adicLisseRingSystem T d.ideal) (op n)

/-- Compatibility of the completed-ring projections with every quotient transition.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: this is the naturality equation of the actual limit cone. -/
theorem adicDatumProjection_comp (m n : ℕᵒᵖ) (g : m ⟶ n) :
    adicDatumProjection T d m.unop ≫ (adicLisseRingSystem T d.ideal).map g =
      adicDatumProjection T d n.unop := by
  exact limit.w (adicLisseRingSystem T d.ideal) g

attribute [local irreducible] adicDatumRing adicLisseRingSystem

attribute [local instance 20000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- The existing module-sheaf Abelian structure with a variable site.
Keeping the site variable retains the coefficient-universe proof arguments directly.
Source: Stacks 03DA (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumSiteModulesAbelian {B : Type (t + 1)} [Category.{t} B]
    [EssentiallySmall.{t + 1} B] (J : GrothendieckTopology B)
    (R : Sheaf J RingCat.{t + 1}) : Abelian (SheafOfModules.{t + 1} R) := inferInstance

/-- The existing Abelian structure with the geometric coefficient-universe instance.
This fixed data interface prevents implicit instance choices from unfolding the
large sheafification construction in derived comparison types.
Source: Stacks 03DA (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumModulesAbelian (U : Scheme.{t})
    (R : Sheaf (ProEt.topology U) CommRingCat.{t + 1}) :
    Abelian (proEtaleRingModules U R) :=
  adicDatumSiteModulesAbelian (ProEt.topology U)
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)

/-- Finite reduction as a functor to the quotient-coefficient derived category.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumReduction (n : ℕ) :
    DerivedCategory (proEtaleRingModules T (adicDatumRing T d)) ⥤
      DerivedCategory (proEtaleRingModules T
        ((adicLisseRingSystem T d.ideal).obj (op n))) :=
  adicDatumExtension T (adicDatumProjection T d n)

/-- Ordinary reduction, retaining the A_T action.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryReduction (n : ℕ) : adicDatumModules T d ⥤ adicDatumModules T d :=
  reductionChange T (adicDatumProjection T d n) ⋙
    SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map (adicDatumProjection T d n))

/-- Quotient transition on actual tensor sections, natural in the module.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the quotient map on the scalar factor respects the balancing relation because
its composite with the completion projection is the earlier projection. It respects
restrictions, addition and scalar action. Sheafification gives the map. Tensor
sections locally generate, proving uniqueness and naturality in the module. -/
theorem adicDatumOrdinaryTransition_exists (m n : ℕᵒᵖ) (g : m ⟶ n) :
    ∃! τ : adicDatumOrdinaryReduction T d m.unop ⟶ adicDatumOrdinaryReduction T d n.unop,
      ∀ (M : adicDatumModules T d) (U : T.ProEtᵒᵖ)
        (s : ((adicLisseRingSystem T d.ideal).obj m).obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (adicDatumTensorSection T
          (adicDatumProjection T d m.unop) M U s x) =
        adicDatumTensorSection T (adicDatumProjection T d n.unop) M U
          (((adicLisseRingSystem T d.ideal).map g).hom.app U s) x := by
  exact scalarTransition_exists T (adicDatumProjection T d m.unop)
    (adicDatumProjection T d n.unop) ((adicLisseRingSystem T d.ideal).map g)
    (adicDatumProjection_comp T d m n g)

/-- The specified quotient map on the scalar factor.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryTransition (m n : ℕᵒᵖ) (g : m ⟶ n) :
    adicDatumOrdinaryReduction T d m.unop ⟶ adicDatumOrdinaryReduction T d n.unop :=
  (adicDatumOrdinaryTransition_exists T d m n g).exists.choose

/-- Identity law for the quotient transitions.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the identity quotient fixes every scalar, hence every pure tensor. The unique
section formula identifies the sheaf map with the identity, naturally in M. -/
theorem adicDatumOrdinaryTransition_id (n : ℕᵒᵖ) :
    adicDatumOrdinaryTransition T d n n (𝟙 n) = 𝟙 _ := by
  apply (adicDatumOrdinaryTransition_exists T d n n (𝟙 n)).unique
    (adicDatumOrdinaryTransition_exists T d n n (𝟙 n)).exists.choose_spec
  intro M U s x
  rw [(adicLisseRingSystem T d.ideal).map_id]
  rfl

/-- Composition law for the quotient transitions.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: either composite sends s tensor x to q(s) tensor x. Composition of the ring
quotient diagram gives the same q, and uniqueness identifies the transformations. -/
theorem adicDatumOrdinaryTransition_comp (l m n : ℕᵒᵖ) (g : l ⟶ m) (h : m ⟶ n) :
    adicDatumOrdinaryTransition T d l n (g ≫ h) =
      adicDatumOrdinaryTransition T d l m g ≫ adicDatumOrdinaryTransition T d m n h := by
  apply (adicDatumOrdinaryTransition_exists T d l n (g ≫ h)).unique
    (adicDatumOrdinaryTransition_exists T d l n (g ≫ h)).exists.choose_spec
  intro M U s x
  change ((adicDatumOrdinaryTransition T d m n h).app M).val.app U
    (((adicDatumOrdinaryTransition T d l m g).app M).val.app U
      (adicDatumTensorSection T (adicDatumProjection T d l.unop) M U s x)) = _
  erw [(adicDatumOrdinaryTransition_exists T d l m g).exists.choose_spec M U s x,
    (adicDatumOrdinaryTransition_exists T d m n h).exists.choose_spec M U _ x,
    (adicLisseRingSystem T d.ideal).map_comp g h]
  rfl

/-- The strict diagram of ordinary reduction endofunctors, with genuine quotient maps.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryTower : ℕᵒᵖ ⥤ (adicDatumModules T d ⥤ adicDatumModules T d) where
  obj n := adicDatumOrdinaryReduction T d n.unop
  map {m n} g := adicDatumOrdinaryTransition T d m n g
  map_id n := adicDatumOrdinaryTransition_id T d n
  map_comp {l m n} g h := adicDatumOrdinaryTransition_comp T d l m n g h

/-- Actual strict tensor tower as a complex in Tow(Mod(A_T)).
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumTowerFunctor : CochainComplex (adicDatumModules T d) ℤ ⥤
    CochainComplex (adicDatumTowers T d) ℤ :=
  (adicDatumOrdinaryTower T d).flip.mapHomologicalComplex (ComplexShape.up ℤ)

/-- Derived finite reduction at a model, with its quotient-coefficient action retained.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelReduction {K : adicDatumDerived T d} (M : AdicDatumModel T d K) (n : ℕ) :=
  (completedConstantQ _).obj
    (((reductionChange T (adicDatumProjection T d n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)

/-- The same strict model, with all transitions, in the one ambient derived category.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelTower {K : adicDatumDerived T d} (M : AdicDatumModel T d K) :
    ℕᵒᵖ ⥤ adicDatumDerived T d :=
  (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
    ((adicDatumTowerFunctor T d).obj M.complex)) ⋙ completedConstantQ _

/-- Identity on every degree identifies evaluation of the strict tower complex
with successive termwise extension and restriction.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: both terms in every degree are the same restricted tensor module and both
differentials are obtained by applying extension then restriction to the original
differential. Identity components commute with these differentials and form the
required isomorphism; the component equation determines its hom, hence its inverse. -/
theorem adicDatumModelComplexRestrictionIso_exists {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    ∃! e : (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
        ((adicDatumTowerFunctor T d).obj M.complex)).obj (op n) ≅
      ((SheafOfModules.restrictScalars.{t + 1}
        ((adicLisseForget T).map (adicDatumProjection T d n))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((reductionChange T (adicDatumProjection T d n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M.complex),
      ∀ i : ℤ, e.hom.f i = 𝟙 _ := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) ?_, ?_, ?_⟩
  · intro i j hij
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · intro i
    rfl
  · intro e he
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro i
    exact he i

/-- The degreewise identity comparison, fixed by its component equations.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelComplexRestrictionIso {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :=
  (adicDatumModelComplexRestrictionIso_exists T d M n).exists.choose

/-- Canonical exact scalar-restriction comparison for a finite quotient complex.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelRestriction {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    (adicDatumModelTower T d M).obj (op n) ≅
      (adicDatumRestriction T (adicDatumProjection T d n)).obj
        (adicDatumModelReduction T d M n) :=
  letI := HasDerivedCategory.standard (adicDatumModules T d)
  letI := HasDerivedCategory.standard
    (completedConstantModules T ((adicLisseRingSystem T d.ideal).obj (op n)))
  letI := (adicDatumRestriction_exact T (adicDatumProjection T d n)).1
  letI := (adicDatumRestriction_exact T (adicDatumProjection T d n)).2
  (completedConstantQ _).mapIso (adicDatumModelComplexRestrictionIso T d M n) ≪≫
    ((SheafOfModules.restrictScalars.{t + 1}
    ((adicLisseForget T).map (adicDatumProjection T d n))).mapDerivedCategoryFactors.app
      (((reductionChange T (adicDatumProjection T d n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M.complex)).symm

/-- Comparison from derived scalar extension of K to its specified K-flat computation.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelReductionComparison {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    (adicDatumReduction T d n).obj K ⟶ adicDatumModelReduction T d M n :=
  (adicDatumReduction T d n).map M.realization.inv ≫
    adicDatumComplexCounit T (adicDatumProjection T d n) M.complex

/-- The canonical comparison with a K-flat computation is invertible.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the model realization is an isomorphism and its functor image is invertible.
The remaining factor is the universal K-flat comparison just described. -/
theorem adicDatumModelReductionComparison_isIso {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    IsIso (adicDatumModelReductionComparison T d M n) := by
  have := adicDatumComplexCounit_isIso T (adicDatumProjection T d n) M.complex M.isKFlat
  unfold adicDatumModelReductionComparison
  infer_instance

/-- The canonical K-flat comparison as an isomorphism.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelReductionIso {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    (adicDatumReduction T d n).obj K ≅ adicDatumModelReduction T d M n :=
  letI := adicDatumModelReductionComparison_isIso T d M n
  asIso (adicDatumModelReductionComparison T d M n)

attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [instance] adicDatumOrdinaryTower_additive

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section Balancing
variable {R S B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
variable (φ : R ⟶ S) (ψ : S ⟶ B)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section GenericKFlatTransport

open SheafOfModules

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Transport K-flat preservation from an existing normalized scalar pair.
Source: Stacks Tag 0G7E (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the scalar pair exists by the universal derived scalar adjunction. Its
ordinary object and map formulas identify its extension functor with E by functor
extensionality. Apply scalarExtension_preservesKFlat to that functor. -/
private theorem adicDatumExtension_kflat_site
    {D : Type u} [Category.{v} D] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (ρ : R ⟶ S)
    (E : SheafOfModules.{r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    [E.Additive] (h : ∀ M, E.obj M = changeOfRings ρ M)
    (hm : ∀ {M N} (g : M ⟶ N), E.map g =
      eqToHom (h M) ≫ changeOfRingsHom ρ M g ≫ eqToHom (h N).symm)
    (K : CochainComplex (SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((E.mapHomologicalComplex (.up ℤ)).obj K) := by
  let := HasDerivedCategory.standard (scalarModules J R)
  let := HasDerivedCategory.standard (scalarModules J S)
  obtain ⟨s⟩ := scalarDerivedPair_exists ρ
  have hE : s.extension = E := by
    refine CategoryTheory.Functor.ext
      (fun M ↦ (s.extension_obj M).trans (h M).symm) ?_
    intro M N f
    rw [s.extension_map, hm]
    simp
  cases hE
  exact scalarExtension_preservesKFlat ρ s K hK

end GenericKFlatTransport

open SheafOfModules MonoidalCategory in
/-- K-flatness survives ordinary extension, with no flatness hypothesis on the ring map.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: tensor an acyclic S-complex N with the extended R-complex. Balancing identifies
it with the tensor of the original K-flat complex and the restricted N. Restriction
is exact, so the latter is acyclic. This is exactly the K-flatness criterion over S. -/
theorem adicDatumExtension_kflat (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := R) C) :
    CochainComplex.IsAcyclicTensorKFlat (R := S)
      (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) := by
  apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1
  exact adicDatumExtension_kflat_site φ (reductionChange T φ)
    (completedExtension_obj T φ) (completedExtension_map T φ) C
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat C).2 hC)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end Balancing

end AlgebraicGeometry.Scheme
