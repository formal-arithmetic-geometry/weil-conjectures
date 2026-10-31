/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerP1CtfData
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.EtaleFlatConstructibleModel
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.EtaleChartComparisonIsos
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-! # A single level of projective-line pullback with twist and shift -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerP1Uniform

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- At one positive coefficient level, preserve the precise shifted intervals and
retain both a global model and its models over affine base opens.

Source: steps 4--6 of lem-sp-tower-p1-uniform-ctf-domains; Stacks Tags 09AL, 03TT,
0963 and 06YQ. (blueprint: lem-sp-tower-p1-level-ctf-model)

Proof: S and P1_S are Noetherian by finite type over k, and the coefficient ring is
finite. Descend the input bounded constructible level through finite-ring derived
comparison. Exactness and faithfulness preserve and reflect [r,s]; finite-Tor
comparison, via comparison_torAmplitudeIn_iff in the intrinsic coordinates,
reflects [a,b]. This interval is ordered because Tor amplitude includes
that condition. The flat constructible model theorem supplies a complex C supported
in [a,b], an isomorphism Q(C) to the etale antecedent, and constructible flat terms.
Trivialize the finite etale Tate line on an etale cover. Apply the pullback-line model
theorem to C, q, this line and shift 2. Its term formula gives support [a-2,b-2];
its exact cohomology formula gives [r-2,s-2]. The theorem retains all prescribed
pulled-back finite locally closed stratifications and their common trivializing covers.
The section-normalized derived evaluation of pullback and tensor, the recorded Tate
line evaluation, and the signed shift comparison identify the actual output level
with the intrinsic comparison of this model. Exact comparison and flat ringed-topos
pullback give flat terms and the identical support. The bounded-above flat criterion
gives independent-coefficient K-flatness. The localization comparison supplies the
required representing isomorphism. Exact cohomology comparison gives intrinsic
constructibility and the cohomological bounds; Tor comparison gives the stated interval.
For an affine open U, restrict the input etale model first using pullback with unit line
and shift zero; it stays flat and constructible with the same intervals. U is
Noetherian, so repeat the projective-line construction over U. The scheme-comparison
restriction square and compatibility of Tate lines with base change identify its
intrinsic realization with the restriction of the actual output along ProjectiveSpace.map.
Bundle these witnesses as LocalModel, globally and over each U. No choice of data is
used to define a functor; the theorem only asserts nonemptiness. Empty opens and zero
complexes use the same containing intervals. This construction uses only this one level. -/
theorem towerP1_level_ctf_model
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (hlp : l ≠ p)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (hS : IsUnit (l : Γ(S, ⊤))) (c : TowerClasses l E S hS)
    (DS : SpCoefficientTowersAbelian l E S)
    (DP : SpCoefficientTowersAbelian l E (ProjectiveLine S))
    (K : spDerivedCoefficientTowers l E S DS) (n : ℕ) (r s a b : ℤ)
    (hK : DerivedCategory.IsGE ((spDerivedCoefficientEvaluation l E S DS n).obj K) r ∧
      DerivedCategory.IsLE ((spDerivedCoefficientEvaluation l E S DS n).obj K) s ∧
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf S (SpTowerShriek.R l E n)
        ((DerivedCategory.homologyFunctor _ i).obj
          ((spDerivedCoefficientEvaluation l E S DS n).obj K))) ∧
      Scheme.HasProEtaleTorAmplitude S (SpTowerShriek.R l E n)
        ((spDerivedCoefficientEvaluation l E S DS n).obj K) a b) :
    (DerivedCategory.IsGE
      ((spDerivedCoefficientEvaluation l E (ProjectiveLine S) DP n).obj
        ((pullTwist l E c DS DP).obj K)) (r - 2) ∧
    DerivedCategory.IsLE
      ((spDerivedCoefficientEvaluation l E (ProjectiveLine S) DP n).obj
        ((pullTwist l E c DS DP).obj K)) (s - 2) ∧
    (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf (ProjectiveLine S)
      (SpTowerShriek.R l E n) ((DerivedCategory.homologyFunctor _ i).obj
        ((spDerivedCoefficientEvaluation l E (ProjectiveLine S) DP n).obj
          ((pullTwist l E c DS DP).obj K)))) ∧
    Scheme.HasProEtaleTorAmplitude (ProjectiveLine S) (SpTowerShriek.R l E n)
      ((spDerivedCoefficientEvaluation l E (ProjectiveLine S) DP n).obj
        ((pullTwist l E c DS DP).obj K)) (a - 2) (b - 2)) ∧
    Nonempty (LocalModel (SpTowerShriek.R l E n) (l ^ (n + 1))
      (SpTowerClasses.coefficient_annihilates l E n) S
      ((spDerivedCoefficientEvaluation l E S DS n).obj K)
      ((spDerivedCoefficientEvaluation l E (ProjectiveLine S) DP n).obj
        ((pullTwist l E c DS DP).obj K)) r s a b) ∧
    ∀ (U : S.Opens), IsAffineOpen U →
      Nonempty (LocalModel (SpTowerShriek.R l E n) (l ^ (n + 1))
        (SpTowerClasses.coefficient_annihilates l E n) U.toScheme
        ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) U.ι).obj
          ((spDerivedCoefficientEvaluation l E S DS n).obj K))
        ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n)
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) U.ι)).obj
            ((spDerivedCoefficientEvaluation l E (ProjectiveLine S) DP n).obj
              ((pullTwist l E c DS DP).obj K))) r s a b) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerP1Uniform
