module

public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
import Sheaf.Paper.FiniteScalarCoordinateData
import all Sheaf.Paper.CompletedIntegralFiniteFree
import all Sheaf.CategoryTheory.ConstantFiniteFreeSectionBasis

/-! # The constant integral scalar adjunction on strict towers

Source: Stacks Project, Tags 07A6, 0B56, 0940 and 0E8I; auxiliary extracted from
compact-support coefficient comparison, Steps 3--4.
(blueprint: def-pur-constant-scalar-tower-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b va vb
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The canonical constant integral coefficient map, induced by inclusion of integers.
Source: Stacks 03CO (blueprint: def-pur-constant-scalar-tower-adjunction). -/
def constantMap (W : Scheme.{u}) :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (integralScalarIntegerInclusion l E F i).ulift.{u + 1, u + 1})

/-- Tensor by B on strict constant-A towers, before passage to complexes.
Source: Stacks 0940 (blueprint: def-pur-constant-scalar-tower-adjunction). -/
abbrev tensor (W : Scheme.{u}) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend (constantMap l E F i W))

/-- Exact coefficient restriction on strict towers.
Source: Stacks 03DA (blueprint: def-pur-constant-scalar-tower-adjunction). -/
abbrev restrict (W : Scheme.{u}) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict (constantMap l E F i W))

/-- Finite freeness makes ordinary constant scalar extension exact on whole towers.
Source: Stacks 03CY, 0940; coefficient-model argument, Step 1
(blueprint: def-pur-constant-scalar-tower-adjunction).
Proof: choose one finite A-basis of B. The same constant sections identify restricted
scalar extension with a finite biproduct on every site object. Kernels and cokernels
of strict diagrams are computed pointwise; restriction is exact and conservative.
Thus tensor preserves finite limits and colimits, including zero towers. -/
theorem tensor_exact (W : Scheme.{u}) :
    PreservesFiniteLimits (tensor l E F i W) ∧
      PreservesFiniteColimits (tensor l E F i W) := by
  classical
  let := i.toAlgebra
  let := (integralScalarIntegerInclusion l E F i).toAlgebra
  obtain ⟨b⟩ := WeilConjectures.integral_basis l E F i
  let : Algebra (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (Padic.coefficientExtensionIntegers l F) :=
    ULift.algebra' (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l F)
  let A : CommRingCat.{u + 1} :=
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
  let B : CommRingCat.{u + 1} :=
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F))
  let J := ProEt.topology W
  let e := @CategoryTheory.basisSheafIso.{u + 1, u, u + 1} W.ProEt inferInstance J
    (integralCoefficientRingSheafify.{u, u} W)
    (inferInstance : J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    (integralCoefficientAbSheafify.{u, u} W)
    (integralCoefficientAbLocallyBijective.{u, u} W)
    A B inferInstance (Module.finrank E F) (WeilConjectures.liftedBasis.{u, u} b)
  exact scalarTowerExtension_exact W (constantMap l E F i W) (Module.finrank E F) e.symm

/-- Exact descent of tensor by B on strict towers.
Source: Stacks 0940 (blueprint: def-pur-constant-scalar-tower-adjunction). -/
def T (W : Scheme.{u}) :
    Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤
      Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W :=
  haveI := (tensor_exact l E F i W).1
  haveI := (tensor_exact l E F i W).2
  (tensor l E F i W).mapDerivedCategory

/-- Exact descent of restriction of scalars on strict towers.
Source: Stacks 03DA (blueprint: def-pur-constant-scalar-tower-adjunction). -/
instance restrict_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (restrict l E F i W) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- Exact scalar restriction preserves finite colimits pointwise.
Source: Stacks 03DA (blueprint: def-pur-constant-scalar-tower-adjunction). -/
instance restrict_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (restrict l E F i W) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- The localization of pointwise coefficient restriction.
Source: Stacks 03DA (blueprint: def-pur-constant-scalar-tower-adjunction). -/
def U (W : Scheme.{u}) := (restrict l E F i W).mapDerivedCategory

/-- The tower scalar adjunction is the descent of the tensor-unit normalized
ordinary scalar adjunction, without any independently selected unit.
Source: Stacks 07A6 (blueprint: def-pur-constant-scalar-tower-adjunction). -/
def scalarAdj (W : Scheme.{u}) : T l E F i W ⊣ U l E F i W :=
  haveI := (tensor_exact l E F i W).1
  haveI := (tensor_exact l E F i W).2
  Adjunction.ofNatIsoRight
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      ((pbcScalarAdjunction (constantMap l E F i W)).whiskerRight ℕᵒᵖ))
    (restrict l E F i W).rightDerivedFunctorIsoMapDerivedCategory

/-- Constant integral coefficients with their canonical inverse-image identifications.
Source: Stacks 03CO (blueprint: def-pur-constant-scalar-tower-adjunction). -/
def constants : PurCompactSupport.Coefficients.{u} where
  ring W := coefficients (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W
  pull g := constantRingIso (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g

/-- The constant coefficient square commutes on the generating constant sections.
Source: Stacks 03CO (blueprint: def-pur-constant-scalar-tower-adjunction). -/
def change : PurCompactSupport.Change (constants l E) (constants l F) where
  map := constantMap l E F i
  square g := (proEtaleConstantInverseImageMap_naturality g
    (CommRingCat.ofHom (integralScalarIntegerInclusion l E F i).ulift)).symm


end WeilConjectures.PurStrictScalar
