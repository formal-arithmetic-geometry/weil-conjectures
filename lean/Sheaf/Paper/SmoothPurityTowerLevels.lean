/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.Paper.SmoothPurityTowerInjectiveComponents
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.SmoothPurityCoefficientTowers
import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
import Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint

/-!
# Levels of the smooth-purity tower direct image

Source: blueprint main-20261015, sec-smooth-purity, sk-lem-sp-tower-levels,
statement and its three proof paragraphs (blueprint: sk-lem-sp-tower-levels).

All indices n denote the positive level n+1. The module category is the recorded
varying-coefficient tower category, with its original small pro-etale site and
coefficient universe max u (t+1). Direct image is precomposition with base change,
with the scalar action induced by the constant-section map. No completion is taken.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing section-normalized equivalence, used only to evaluate towers.
Its section, restriction, transition and morphism normalizations determine this
presentation up to the identity on every component; no coefficient datum is chosen.
Source: blueprint coefficient-tower lemma, clause (2)
(blueprint: sk-lem-sp-tower-levels). -/
def spTowerLevelEquivalence (T : Scheme.{t}) :=
  (Classical.choice (sp_coefficient_towers_abelian l E T)).equivalence

/-- The recorded exact evaluation, using its section-normalized equivalence.
Source: blueprint coefficient-tower lemma, clause (2)
(blueprint: sk-lem-sp-tower-levels). -/
abbrev spTowerLevelEvaluation (T : Scheme.{t}) (n : ℕ) :=
  spCoefficientEvaluation l E T (spTowerLevelEquivalence l E T) n

/-- Additivity of the normalized equivalence. Source: blueprint coefficient-tower lemma
(blueprint: sk-lem-sp-tower-levels). -/
instance spTowerLevelEquivalenceAdditive (T : Scheme.{t}) :
    (spTowerLevelEquivalence l E T).functor.Additive :=
  (Classical.choice (sp_coefficient_towers_abelian l E T)).equivalenceAdditive

/-- Exact evaluation preserves kernels. Source: blueprint coefficient-tower lemma
(blueprint: sk-lem-sp-tower-levels). -/
instance spTowerLevelEvaluationLimits (T : Scheme.{t}) (n : ℕ) :
    PreservesFiniteLimits (spTowerLevelEvaluation l E T n) :=
  (Classical.choice (sp_coefficient_towers_abelian l E T)).evaluationLimits n

/-- Exact evaluation preserves cokernels. Source: blueprint coefficient-tower lemma
(blueprint: sk-lem-sp-tower-levels). -/
instance spTowerLevelEvaluationColimits (T : Scheme.{t}) (n : ℕ) :
    PreservesFiniteColimits (spTowerLevelEvaluation l E T n) :=
  (Classical.choice (sp_coefficient_towers_abelian l E T)).evaluationColimits n

variable {T S : Scheme.{t}} (g : T ⟶ S)

/-- The published tower direct image admits its module inverse-image left adjoint.
The ordinary operations keep both universes and module categories unchanged.
Source: blueprint tower-level lemma, preliminary operations; Stacks 03DA, 079H
and lemma-adjoint-push-pull-modules (blueprint: sk-lem-sp-tower-levels).
Proof: transport the sites to equivalent small models in max u (t+1). The ringed-site
Grothendieck theorem supplies the module categories. The canonical scalar maps define
inverse images by module Kan extension and sheafification. The tensor-unit adjunction
identifies their right adjoints
with the displayed sectionwise direct images. Apply this levelwise to towers:
naturality in quotient coefficients assembles the transitions, and the linear
Hom adjunction respects the transition squares. Thus it gives a tower adjunction.
All choices here are adjoints to the fixed, explicitly constructed direct images,
so the resulting inverse images are determined up to the unique adjunction isomorphism. -/
theorem sp_tower_operations_exist :
    (spTowerPush l E g).IsRightAdjoint := by
  sorry

/-- Existence of the tower inverse image. Source: blueprint tower-level lemma
(blueprint: sk-lem-sp-tower-levels). -/
instance spTowerPushforwardRightAdjoint : (spTowerPush l E g).IsRightAdjoint :=
  sp_tower_operations_exist l E g

/-- Inverse image is the left adjoint to the specified sectionwise direct image.
The adjunction determines its data up to unique compatible isomorphism.
Source: blueprint tower-level lemma, introductory clause
(blueprint: sk-lem-sp-tower-levels). -/
def spTowerPullback := (spTowerPush l E g).leftAdjoint

/-- Exactness and levelwise construction of the tower inverse image.
The level comparisons are comparisons of entire functors, including morphisms.
Source: blueprint tower-level lemma, introductory clause; Stacks 04JC
(blueprint: sk-lem-sp-tower-levels).
Proof: the inverse image of constant coefficients identifies canonically with the
same coefficients after base change, compatibly with all quotient maps. The module
inverse image is therefore the exact abelian inverse image with transported action.
Assemble the level inverse images and their transitions. Their level adjunctions
assemble to an adjunction with spTowerPush; uniqueness of left adjoints
identifies this construction with spTowerPullback. Exactness is levelwise by
sp_coefficient_towers_abelian. Direct image is additive since its section maps are
unchanged linear maps; its kernels are sectionwise, so it is left exact. -/
theorem sp_tower_operations_properties :
    PreservesFiniteLimits (spTowerPullback l E g) ∧
      PreservesFiniteColimits (spTowerPullback l E g) ∧
      (∀ n : ℕ, Nonempty
        (spTowerPullback l E g ⋙ spTowerLevelEvaluation l E T n ≅
          spTowerLevelEvaluation l E S n ⋙ (spLevelPush l E g n).leftAdjoint)) := by
  sorry

/-- Ordinary right derived tower direct image on the bounded below derived categories.
Source: blueprint tower-level lemma; Stacks 05TI
(blueprint: sk-lem-sp-tower-levels). -/
abbrev spTowerDerivedPushforward := (spTowerPush l E g).rightDerivedFunctorPlus

/-- Ordinary finite-coefficient right derived direct image on D+.
Source: blueprint tower-level lemma; Stacks 05TI
(blueprint: sk-lem-sp-tower-levels). -/
abbrev spTowerLevelDerivedPushforward (n : ℕ) :=
  (spLevelPush l E g n).rightDerivedFunctorPlus

/-- Exact evaluation commutes with the ordinary bounded below derived tower direct image.
Source: blueprint main-20261015, sk-lem-sp-tower-levels, all proof paragraphs
(blueprint: sk-lem-sp-tower-levels).
Proof:
1. The existing tower theorem gives Grothendieck abelianness and exact evaluation;
finite-level modules are Grothendieck by the small-site ringed-module theorem.
Grothendieck categories have enough injectives. The preliminary operations above
are the levelwise ones and the tower pullback is exact.
2. The evaluation right adjoint r_n is zero below n and constant at and above n,
with scalar restriction along the quotient maps. Its adjunction follows by composing
the component at n with the tower transitions. It is exact and preserves injectives.
3. Embed a tower into the product of r_n J_n for injective embeddings C_n into J_n.
At level r this product has only the finitely many coordinates n <= r. The rth
coordinate makes the embedding monic. For an injective tower the embedding splits,
so its rth level is a retract of this finite product of scalar-restricted injectives.
4. The acyclicity assertion det-sp-tower-injective-components makes each such
component acyclic for ordinary module direct image; no assertion that restriction
of scalars preserves injectives is needed.
5. Represent C by a bounded below complex (good truncation if necessary), then take
a bounded below injective tower resolution. Exact evaluation preserves the resolution
quasi-isomorphism; its evaluated terms are acyclic by step 4. Tower direct image of
the resolution represents its right derived image.
6. The acyclic-unit theorem identifies finite-level direct image of the evaluated
resolution with its finite-level derived direct image. Conjugate this unit by the
inverse evaluated tower-derived unit. On a resolution K -> I the full comparison
is ev Rg(QK) -> ev Rg(QI) -> Q(g_* I_n) -> Rg_n(QI_n) -> Rg_n(QK_n),
using the inverse resolution map for the final arrow. Derived-unit naturality makes
this independent of resolutions and natural in derived morphisms: bounded below
injective complexes are K-injective and their Hom groups compute derived Hom.
7. Exact evaluation descends by mapDerivedCategoryPlus, so this yields the displayed
isomorphism in D+(S_proet,R_n). The finite-level functor agrees with the ordinary
unbounded K-injective direct image restricted to D+: bounded below injectives are
K-injective and the two derived units agree on them, hence uniquely on D+. -/
theorem sp_tower_levels (n : ℕ) (C : DerivedCategory.Plus (spCoefficientTowers l E T)) :
    Nonempty
      ((spTowerLevelEvaluation l E S n).mapDerivedCategoryPlus.obj
          ((spTowerDerivedPushforward l E g).obj C) ≅
        (spTowerLevelDerivedPushforward l E g n).obj
          ((spTowerLevelEvaluation l E T n).mapDerivedCategoryPlus.obj C)) := by
  sorry

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
