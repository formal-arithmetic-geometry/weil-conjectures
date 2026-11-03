/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData

import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerFiniteReduction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerDerivedComplete
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCofinalIntegralBounds
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeTowerCompletionUnit
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.EllCoefficientFiber
public import WeilConjectures.CategoryTheory.Cochain.CochainHomotopyComparison
public import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition

/-!
# Reconstruction of a normalized smooth-purity coefficient tower

Source: blueprint main-20261015, sec-smooth-purity,
`sk-lem-sp-tower/_section.md`; Stacks Project, Tags 0940 and 099P
(blueprint: sk-lem-sp-tower).

The natural index n denotes positive exponent n+1. A Roos triangle specifies the
actual derived inverse limit and its projections. The comparison at each finite level
is the tensor-restriction adjoint of that projection, in the finite-coefficient category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

attribute [-instance] spCoefficientModulesAbelian

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

variable (D : SpCoefficientTowersAbelian l E T)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private theorem native_counit_isIso
    (R : SpReductionTower l E T D) (L : NativeTower.Limit l E T D R)
    (C : spDerivedCoefficientTowers l E T D)
    (heval : ∀ n : ℕ, IsIso ((spDerivedCoefficientEvaluation l E T D n).map
      ((NativeTower.redLimitAdjunction l E T D R L).counit.app C))) :
    IsIso ((NativeTower.redLimitAdjunction l E T D R L).counit.app C) := by
  let := D.hasDerived
  let := D.equivalenceAdditive
  let : D.equivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : IsIso (D.equivalence.mapDerivedCategory.functor.map
      ((NativeTower.redLimitAdjunction l E T D R L).counit.app C)) := by
    apply (systemDerivedEvaluation_isIso_iff (spCoefficientCommRings l E T) _).2
    intro n
    let := D.evaluationLimits n
    let := D.evaluationColimits n
    let : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
      Functor.additive_of_preserves_binary_products _
    exact (NatIso.isIso_map_iff
      (Functor.mapDerivedCategoryCompIso D.equivalence.functor
        (systemEvaluation (spCoefficientCommRings l E T) n)) _).1 (heval n)
  exact isIso_of_reflects_iso _ D.equivalence.mapDerivedCategory.functor

/-- Simultaneous reduction over the pulled-back condensed integer ring is left adjoint
to total derived inverse limit, with its actual completion unit. On a Noetherian scheme
these same functors restrict to mutually inverse equivalences between native bounded
constructible complexes and normalized constructible finite-Tor towers.
Source: current blueprint sk-lem-sp-tower, both paragraphs; Stacks 0940 and 099P
(blueprint: sk-lem-sp-tower).

Proof, following the current six-step plan:
1. Construct ordinary scalar-extension/limit adjunction on strict towers and derive it
with the fixed K-flat reduction model. NativeTower.Limit retains the universal right
comparison and the representative transpose equation, so its unit is completion.
2. For native bounded constructible K, the condensed integral criterion gives canonical
uniformizer completeness. The power-torsion comparison makes the ell-completion unit
invertible. The existing reduction theorem gives normalization, constructibility and
common bounds after the exact section equivalence.
3--4. For a normalized tower the quotient-error triangle and perfect/Roos comparison,
with their projection equations, compute the evaluated counit. Its error tower is
nilpotent; the finite geometric sum contracts its Roos complex. These are the finite
counit clauses of NativeTower.limit_residue_and_counit.
5. The same theorem gives canonical uniformizer completeness of the limit and bounded
constructibility of its first uniformizer reduction. The Noetherian condensed integral
criterion gives native bounded constructibility of the limit.
6. Joint conservativity of derived evaluations gives the actual counit isomorphism.
Lift both functors to the two full subcategories. Restrict the ambient adjunction;
faithful inclusions identify the restricted unit and counit with the ambient ones.
Their invertibility yields the stated equivalence, whose functors are exactly the
restrictions, as the two displayed equalities assert. -/
theorem spTower_reconstruction_condensed :
    ∃ (R : SpReductionTower l E T D) (L : NativeTower.Limit l E T D R),
      (∀ K : NativeTower.Integral l E T, NativeTower.Complete l E T K →
        IsIso ((NativeTower.redLimitAdjunction l E T D R L).unit.app K)) ∧
      ∀ _hT : IsNoetherian T,
        ∃ e : ConstantModelBoundedConstructible (spIntegralCondensed l E) T ≌
            spNormalizedConstructibleTorTowerCategory l E T D,
          e.functor ⋙ (spNormalizedConstructibleTorTowers l E T D).ι =
            (constantModelBoundedConstructible (spIntegralCondensed l E) T).ι ⋙
              NativeTower.red l E T D R ∧
          e.inverse ⋙ (constantModelBoundedConstructible (spIntegralCondensed l E) T).ι =
            (spNormalizedConstructibleTorTowers l E T D).ι ⋙
              NativeTower.lim l E T D R L := by
  classical
  obtain ⟨R⟩ := sp_reduction_tower_normalized l E T D
  obtain ⟨L⟩ := NativeTower.exists_limit l E T D R
  refine ⟨R, L, NativeTower.unit_isIso_of_complete l E T D R L, ?_⟩
  intro hT
  let := hT
  let P := constantModelBoundedConstructible (spIntegralCondensed l E) T
  let Q := spNormalizedConstructibleTorTowers l E T D
  let red := NativeTower.red l E T D R
  let lim := NativeTower.lim l E T D R L
  let adj : red ⊣ lim := NativeTower.redLimitAdjunction l E T D R L
  have hred (K : P.FullSubcategory) : Q (red.obj K.obj) := by
    have : P.IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined (spIntegralCondensed l E) T).2.1
    have hK := P.prop_of_iso ((NativeTower.sectionEquivalence l E T).unitIso.app K.obj)
      K.property
    exact (R.constructible inferInstance inferInstance
      ((NativeTower.sectionEquivalence l E T).functor.obj K.obj) hK).2.1
  have hlim (C : Q.FullSubcategory) : P (lim.obj C.obj) := by
    exact (NativeTower.criterion l E T _).mpr
      (NativeTower.limit_residue_and_counit l E T D R L C.obj C.property).1
  let F : P.FullSubcategory ⥤ Q.FullSubcategory := Q.lift (P.ι ⋙ red) hred
  let G : Q.FullSubcategory ⥤ P.FullSubcategory := P.lift (Q.ι ⋙ lim) hlim
  let a : F ⊣ G := adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)
  have hunit (K : P.FullSubcategory) : P.ι.map (a.unit.app K) = adj.unit.app K.obj := by
    dsimp only [a]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    change adj.unit.app K.obj ≫ lim.map (𝟙 _) ≫ 𝟙 _ = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Category.comp_id]
    exact CategoryTheory.Category.comp_id _
  have hcounit (C : Q.FullSubcategory) : Q.ι.map (a.counit.app C) =
      adj.counit.app C.obj := by
    dsimp only [a]
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    change 𝟙 _ ≫ red.map (𝟙 _) ≫ adj.counit.app C.obj = _
    simp only [CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp]
  have hunitIso (K : P.FullSubcategory) : IsIso (a.unit.app K) := by
    obtain ⟨K', he, hcomplete, _⟩ := (NativeTower.criterion l E T K.obj).mp K.property
    have := NativeTower.unit_isIso_of_complete l E T D R L K.obj
      ⟨K', he, hcomplete⟩
    have : IsIso (P.ι.map (a.unit.app K)) := by
      rw [hunit]
      exact inferInstanceAs
        (IsIso ((NativeTower.redLimitAdjunction l E T D R L).unit.app K.obj))
    exact isIso_of_reflects_iso _ P.ι
  have hcounitIso (C : Q.FullSubcategory) : IsIso (a.counit.app C) := by
    have := native_counit_isIso l E T D R L C.obj
      (NativeTower.limit_residue_and_counit l E T D R L C.obj C.property).2
    have : IsIso (Q.ι.map (a.counit.app C)) := by
      rw [hcounit]
      exact inferInstanceAs
        (IsIso ((NativeTower.redLimitAdjunction l E T D R L).counit.app C.obj))
    exact isIso_of_reflects_iso _ Q.ι
  exact ⟨a.toEquivalence, rfl, rfl⟩

end AlgebraicGeometry.ProEtale
