/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Constructible
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.CategoryTheory.Abelian.FunctorCategory

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.ConstructibleFlatCohomologyTorBound
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.ResidueLisseProjectiveModels
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
/-!
# Ordinary tensor and completed tensor of constructible integral complexes

Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50, Definition 3.4.10 and
Lemma 3.4.12(4), pp. 22--23 (blueprint: lem-fix-constructible-tensor-completion).
The existential tensor presentation retains its natural K-flat comparison, and the
completion comparison retains both coordinates of the actual product mapping fiber.
The index n denotes the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : AlgebraicGeometry.Scheme.{u})

/-- The existing small-model size at exactly the completed-coefficient universe.
Source: Stacks 098K (blueprint: lem-fix-constructible-tensor-completion). -/
instance (priority := 3100) constructibleTensorSiteSmall :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- The existing sheaf tensor on completed coefficients, with no completion applied.
Source: Stacks 03EK; Bhatt--Scholze Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion). -/
abbrev constructibleTensorOrdinary :=
  @MonoidalCategory.curriedTensor (integralTowerModules l E W) _
    (SheafOfModules.monoidalCategory (completedIntegralCommRingSheafUnrestricted l E W))

/-- Zero preservation of the existing tensor in its first argument.
Source: Stacks 03EK (blueprint: lem-fix-constructible-tensor-completion). -/
instance constructibleTensorZero :
    (constructibleTensorOrdinary l E W).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients.{u + 1, u, u + 1}
    (completedIntegralCommRingSheafUnrestricted l E W)

/-- Zero preservation of the existing tensor in its second argument.
Source: Stacks 03EK (blueprint: lem-fix-constructible-tensor-completion). -/
instance constructibleTensorObjZero (M : integralTowerModules l E W) :
    ((constructibleTensorOrdinary l E W).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients.{u + 1, u, u + 1}
    (completedIntegralCommRingSheafUnrestricted l E W) M

/-- Mathlib's signed direct-sum total tensor, specialized to the completed ring sheaf.
Source: Stacks 06YL (blueprint: lem-fix-constructible-tensor-completion). -/
abbrev constructibleTensorTotal :=
  Functor.uncurry.obj ((constructibleTensorOrdinary l E W).map₂CochainComplex)

/-- A homogeneous pure tensor in a direct-sum totalization summand.
Source: Stacks 03EK and 06YL (blueprint: lem-fix-constructible-tensor-completion). -/
def constructibleTensorTotalSection
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (p q : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((constructibleTensorTotal l E W).obj (P, Q)).X (p + q)).val.obj U :=
  letI : MonoidalCategory (PresheafOfModules.{u + 1}
      (completedIntegralCoefficientSheafUnrestricted l E W).obj) :=
    PresheafOfModules.monoidalCategory
    (R := (completedIntegralCommRingSheafUnrestricted l E W).obj)
  (CochainComplex.ιMapBifunctor P Q (constructibleTensorOrdinary l E W)
    p q (p + q) rfl).val.app U
    ((SheafOfModules.tensorObjIsoSheafification
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X p) (Q.X q)).inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (completedIntegralCoefficientSheafUnrestricted l E W).obj)).unit.app
          ((P.X p).val ⊗ (Q.X q).val)).app U
            (x ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E W).obj.obj U] y)))

/-- The boundary 1-s for the specified strict finite-tensor quotient tower.
Source: Bhatt--Scholze Definition 3.4.10
(blueprint: lem-fix-constructible-tensor-completion). -/
abbrev constructibleTensorBoundary
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q))
    (integralOperationsTowerStep
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)))

set_option backward.isDefEq.respectTransparency true in
/-- The actual quotient-map completion comparison is invertible on constructible pairs;
the ordinary ambient tensor is derived complete. Both tensor presentation and comparison
are supplied, rather than assumed. The natural representative isomorphism identifies T
with the localization of signed total tensor on flat-term K-flat complexes. The chain
map chi has the coefficient quotient maps as its first product coordinates and zero
shifted coordinate, so it is the specified mapping-fiber map, not an arbitrary lift.
The natural transformation tau descends precisely chi using those comparisons.

Source: Bhatt--Scholze Lemma 6.5.5, pp. 49--50; Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: lem-fix-constructible-tensor-completion).

Proof:
1. Identify the quotient-tower completion and its unit with Koszul completion using
lem-weil-pbc-constant-completion-equivalence and the ringed Koszul reflector. Compare
its Roos triangle with def-weil-derived-complete; this proves that the particular
canonical unit is invertible exactly on derived-complete objects, without uniqueness
of arbitrary triangulated lifts.
2. Weakly etale restriction is exact slice restriction and preserves products. The
constructible closed-pullback limits theorem gives the same properties for closed
immersions with quasi-compact open complement. Exact countable products and derived
tensor pullback show that both restrictions commute with completion and its unit.
3. Choose finite constructible partitions for the finitely many residue cohomology
sheaves of M and N. Factor each actual stratum through a quasi-compact open and then
a closed immersion with quasi-compact complement. Pull back these open-closed splits
to build a finite qcqs splitting tree. Each leaf maps scheme-theoretically to one
stratum of each partition, using actual fiber products rather than image containment.
4. Cover each leaf by affine weakly contractible pro-etale charts. Residue cohomology
is bounded lisse finite-dimensional, hence flat; truncation triangles give its finite
Tor bound. Apply lem-fix-residue-lisse-projective-models to obtain bounded finite-projective
sheaf models for both inputs, refining their finite covers by intersections.
5. The coefficient unit B is canonically complete: its finite quotient transitions
are surjective on sections, so 1-s is surjective on their product with kernel B.
The strict-tower derived-limit theorem and K-flat descent make completion exact.
Thus its unit is invertible on finite sums, summands, and bounded complexes thereof.
6. The total tensor of the two bounded projective models is bounded projective termwise.
Its terms are flat and its finite stupid filtration proves K-flatness. It computes
the ordinary tensor, whose canonical completion map is invertible by step 5.
7. Restrictions detect the zero cone on each chart. Reverse the finite splitting tree:
the open-closed exact sequence detects zero cohomology from its open and closed
restrictions. The global canonical unit is therefore invertible, and step 1 gives
Roos-triangle derived completeness of the ordinary tensor.
8. On flat-term K-flat representatives, balancing identifies the reduction of the total
tensor with the total tensor of the reductions: ((p tensor q) tensor a) maps to
(p tensor a) tensor (q tensor 1). Its inverse multiplies scalars. These maps commute
with differentials and strict quotient transitions, and identify the unit with chi
specified below. Site tensor descent extends this map and its naturality uniquely
to the derived category, giving tau and its isomorphism on constructible pairs. -/
theorem constructibleTensorCompletion [CompactSpace W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃ (T : DerivedCategory (integralTowerModules l E W) ×
        DerivedCategory (integralTowerModules l E W) ⥤
          DerivedCategory (integralTowerModules l E W))
      (e : ((integralOperationsGoodComplex l E W).ι.prod
          (integralOperationsGoodComplex l E W).ι) ⋙ constructibleTensorTotal l E W ⋙
          DerivedCategory.Q ≅
        ((integralOperationsGoodLocalization l E W).prod
          (integralOperationsGoodLocalization l E W)) ⋙ T)
      (chi : constructibleTensorTotal l E W ⟶ integralOperationsTensorComplexFunctor l E W),
      (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (n : ℕ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (((chi.app (P, Q) ≫ CochainComplex.mappingCocone.fst
          (constructibleTensorBoundary l E W P Q) ≫
          Pi.π (fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q)) n).f
            (p + q)).val.app U)
          (constructibleTensorTotalSection l E W P Q p q U x y) =
        integralOperationsTotalTensorSection l E W n P Q p q U
          (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
          (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)) ∧
      (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i j : ℤ)
        (h : i + -1 = j),
        (chi.app (P, Q)).f i ≫ (CochainComplex.mappingCocone.snd
          (constructibleTensorBoundary l E W P Q)).v i j h = 0) ∧
      ∃ tau : T ⟶ integralCompletedTensor l E W,
        (∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
          e.hom.app (P, Q) ≫ tau.app (DerivedCategory.Q.obj P.obj,
              DerivedCategory.Q.obj Q.obj) ≫
            (integralCompletedTensorComparison l E W).hom.app (P, Q) =
          DerivedCategory.Q.map (chi.app (P.obj, Q.obj))) ∧
        ∀ M N : DerivedCategory (integralTowerModules l E W),
          sfIntegralConstructible l E W M → sfIntegralConstructible l E W N →
          IsDerivedCompleteUnrestricted l E W (T.obj (M, N)) ∧ IsIso (tau.app (M, N)) := by
  sorry

end WeilConjectures
