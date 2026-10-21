/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Algebra.Homology.LocalizedStrictTensorLinearEvaluation
public import Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat
public import Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.Paper.ReductionPullbackDerivedTower
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness

import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.Paper.RestrictionDerivedProducts
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Normalized localized extension on derived strict coefficient towers

Source: Stacks Project, Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor;
Cohomology on Sites, Tags 06YS and 06YU; Categories, Tags 04VG and 04VK.
(blueprint: lem-sf-cbc-localized-strict-tensor-descent).

Strict towers are localized after taking complexes. The reduction functor is the
universal left derived functor of the actual ordinary tensor tower, equivalently
the diagram-site tensor of the constant diagram with the coefficient tower.
The counit fixes all representative comparisons; no functorial resolution is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace SheafOfModules.LocalizedStrictTensor
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The ordinary inverse-projection comparison of strict towers.
Source: Stacks 0E8I (blueprint: lem-sf-cbc-localized-strict-tensor-descent). -/
abbrev OrdinaryComparison (S : AlgebraTowers.{c, v, r} R) :=
  localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
    reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
      towerExtension.{c, v, r} R V

/-- The derived comparison of the specified universal strict reductions.
Source: Stacks 06YU (blueprint: lem-sf-cbc-localized-strict-tensor-descent). -/
abbrev DerivedComparison (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V)) (S : AlgebraTowers.{c, v, r} R) :=
  (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ m.F.obj S ≅
    mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
      (towerExtension.{c, v, r} R V).mapDerivedCategory

/-- Precisely the normalized descent assertions for the two canonical reductions.
This is conclusion data, not a hypothesis supplying a comparison.
Source: Stacks 0E8I, 06YU, 04VG, 04VK
(blueprint: lem-sf-cbc-localized-strict-tensor-descent). -/
structure Descent (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V)) where
  /-- The strict ordinary inverse projection. -/
  ordinary : ∀ S : AlgebraTowers.{c, v, r} R, OrdinaryComparison.{c, v, r} R V S
  /-- Its generator equation includes preservation of the scalar unit. -/
  ordinary_normalized : ∀ S, OrdinaryNormalized.{c, v, r} R V S (ordinary S)
  /-- The natural isomorphism on the unbounded derived categories of strict towers. -/
  derived : ∀ S : AlgebraTowers.{c, v, r} R, DerivedComparison.{c, v, r} R V m mV S
  /-- Every flat-term K-flat representative gives exactly the specified chain map. -/
  normalized : ∀ S, DerivedNormalized.{c, v, r} R V m mV S (ordinary S) (derived S)
  /-- Uniqueness among natural isomorphisms with this representative normalization. -/
  unique : ∀ (S : AlgebraTowers.{c, v, r} R)
    (ρ' : DerivedComparison.{c, v, r} R V m mV S),
    DerivedNormalized.{c, v, r} R V m mV S (ordinary S) ρ' → ρ' = derived S
  /-- Naturality in every coefficient-tower map already before localization. -/
  ordinary_natural : ∀ (S T : AlgebraTowers.{c, v, r} R) (a : S ⟶ T)
    (M : Modules.{max c v, v, r} (R.over V)),
    ((reductionFamily.{c, v, r} R).map a).app
        ((localizedSystemExtension.{c, v, r} R V).obj M) ≫ (ordinary T).hom.app M =
      (ordinary S).hom.app M ≫ (towerExtension.{c, v, r} R V).map
        (((reductionFamily.{max c v, v, r} (R.over V)).map
          (Functor.whiskerRight a (sliceAlgebras.{c, v, r} R V))).app M)
  /-- Naturality in every coefficient-tower map after localization. -/
  derived_natural : ∀ (S T : AlgebraTowers.{c, v, r} R) (a : S ⟶ T)
    (K : D.{max c v, v, r} (R.over V)),
    (m.F.map a).app ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategory.obj K) ≫
        (derived T).hom.app K =
      (derived S).hom.app K ≫ (towerExtension.{c, v, r} R V).mapDerivedCategory.map
        ((mV.F.map (Functor.whiskerRight a (sliceAlgebras.{c, v, r} R V))).app K)
  /-- At every positive level the comparison is scalar restriction of an S_n-linear iso. -/
  linear : ∀ (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ),
    LinearEvaluation.{c, v, r} R V m mV S n (ordinary S) (derived S)

/-- Exact localized extension commutes canonically with derived strict-tower tensor,
with its strict inverse-projection normalization, tower-map naturality, uniqueness,
and coefficient-linear evaluation. All models and comparisons are conclusions.
There is no ring-map flatness, transition-surjectivity, boundedness or completion assumption.

Source: Stacks sites-modules.tex, Tag 0E8I, lemma-j-shriek-and-tensor;
sites-cohomology.tex, Tags 06YS, 06YU; categories.tex, Tags 04VG, 04VK
(blueprint: lem-sf-cbc-localized-strict-tensor-descent).

Proof:
1. Resolve by flat-term K-flat complexes (lem-pc-kflat-resolution). Exact extension
preserves quasi-isomorphisms and K-flatness by lem-sf-ringed-open-total-tensor-kflat.
Its terms are flat: restrict an exact sequence, tensor by a flat term, and extend;
the ordinary projection formula identifies this with tensor by the extended term.
2. Under lem-weil-pbc-diagram-site-realization, evaluations are exact, detect
acyclicity, and preserve sums and total tensor (lem-pur-cochain-pullback-tensor-coherence).
Thus the constant diagram of every resolving complex is again flat-term K-flat.
3. lem-trf-site-one-sided-tensor-normalization computes the diagram derived tensor
by the actual tower P tensor S_n, with transitions 1 tensor s_n. The identifications
are the identity on local pure tensors; module sheafification uniqueness proves strict
transition compatibility. Termwise extension is exact by levelwise detection.
4. On each extension summand indexed by a:W -> V send [p]_a tensor s to
[p tensor s]_a. This balanced map and its inverse extend through sheafification
by the bilinear-extension existence and uniqueness lemmas. The maps are S_n-linear;
scalar restriction of extension is identified by the identity on these summands.
5. Apply this formula in every degree. Naturality in p gives compatibility with
differentials; naturality in s gives strict transitions and tower-map naturality.
Taking s=1 proves the ordinary scalar-unit clause, including all summands.
6. Conjugate the localized chain iso by the one-sided computation counits and exact
extension comparisons. It respects homotopies. The resolving-class localization
of lem-weil-pbc-site-derived-tensor-descent descends it and its inverse to rho.
7. Full faithfulness of restriction to resolving models proves uniqueness and
independence of representative. The same argument descends tower-map naturality.
8. Evaluate the representative equation. The normalized scalar-extension model and
exact restriction identify evaluation with scalar restriction of derived change
of rings. The S_n-linear chain iso of step 4 descends, and its scalar restriction
is the evaluated rho by the same counit equations and localization uniqueness.
No step needs coefficient flatness, surjective transitions, boundedness or completion. -/
theorem localized_strict_tensor_descent :
    ∃ (m : ReductionModel.{c, v, r} R)
      (mV : ReductionModel.{max c v, v, r} (R.over V)),
      Nonempty (Descent.{c, v, r} R V m mV) := by
  sorry

end SheafOfModules.LocalizedStrictTensor
