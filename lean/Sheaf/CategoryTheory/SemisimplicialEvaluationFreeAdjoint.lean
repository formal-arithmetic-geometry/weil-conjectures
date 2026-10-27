/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Adjunction
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor

/-! # Free extension from a semisimplicial component

Source: Stacks Project, spaces-simplicial.tex, Tags 0D72, 0D74 and 0D9E,
with the injective-order-map adaptation
(blueprint: lem-sfb-semisimplicial-evaluation-free-adjoint).

A certificate records the labelled coproduct construction, including its transition
maps and its specified adjunction. Its derived functor is the existing termwise
localization, with the same formulas and the original derived transitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory

namespace CategoryTheory.SemisimplicialRingedTotal

variable {F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u}}
  {D : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F}
  {R : RingDiagram D} {h : Presheaf.IsSheaf D.totalTopology R.presheaf}

/-- The labelled free extension and all its ordinary and derived normalizations.
For `a : m ⟶ p` in the opposite semi-simplex category, the label is the injection
`[p] ↪ [m]`. The colimit certificates include the empty coproduct, hence zero below `p`.
They specify genuine coproducts of the dependency's actual module pullbacks, rather
than an arbitrary left adjoint. The representative formulas specify the termwise
localization and the identification of exact pullback with left derived pullback.

Source: Stacks Project, spaces-simplicial.tex, Tags 0D72, 0D74 and 0D9E,
agent-supplied injective-order-map adaptation
(blueprint: lem-sfb-semisimplicial-evaluation-free-adjoint). -/
structure EvaluationFreeExtension (P : Presentation R h) (p : SemiSimplexCategoryᵒᵖ) where
  ordinary : (R.fibre p).modules ⥤ (R.total h).modules
  [additive : ordinary.Additive]
  [limits : PreservesFiniteLimits ordinary]
  [colimits : PreservesFiniteColimits ordinary]
  inclusion : ∀ {m : SemiSimplexCategoryᵒᵖ} (a : m ⟶ p),
    (P.pullback a).ordinary ⟶ ordinary ⋙ (P.evaluation m).ordinary
  coproduct : ∀ (m : SemiSimplexCategoryᵒᵖ) (G : (R.fibre p).modules),
    IsColimit (Cofan.mk ((P.evaluation m).ordinary.obj (ordinary.obj G))
      (fun a : m ⟶ p ↦ (inclusion a).app G))
  transition : ∀ {m k : SemiSimplexCategoryᵒᵖ} (a : m ⟶ p) (b : k ⟶ m)
      (G : (R.fibre p).modules),
    (P.pullback b).ordinary.map ((inclusion a).app G) ≫
        (P.transition b).app (ordinary.obj G) =
      (P.composition b a).ordinary.inv.app G ≫ (inclusion (b ≫ a)).app G
  adjunction : ordinary ⊣ (P.evaluation p).ordinary
  homEquiv : ∀ (G : (R.fibre p).modules) (E : (R.total h).modules)
      (v : ordinary.obj G ⟶ E),
    adjunction.homEquiv G E v = (P.identity p).ordinary.inv.app G ≫
      (inclusion (𝟙 p)).app G ≫ (P.evaluation p).ordinary.map v
  inverse_homEquiv : ∀ (G : (R.fibre p).modules) (E : (R.total h).modules)
      (v : G ⟶ (P.evaluation p).ordinary.obj E)
      {m : SemiSimplexCategoryᵒᵖ} (a : m ⟶ p),
    (inclusion a).app G ≫
        (P.evaluation m).ordinary.map ((adjunction.homEquiv G E).symm v) =
      (P.pullback a).ordinary.map v ≫ (P.transition a).app E
  unit : ∀ G : (R.fibre p).modules,
    adjunction.unit.app G =
      (P.identity p).ordinary.inv.app G ≫ (inclusion (𝟙 p)).app G
  unit_isIso : IsIso adjunction.unit
  counit : ∀ (E : (R.total h).modules) {m : SemiSimplexCategoryᵒᵖ} (a : m ⟶ p),
    (inclusion a).app ((P.evaluation p).ordinary.obj E) ≫
      (P.evaluation m).ordinary.map (adjunction.counit.app E) = (P.transition a).app E
  derivedAdjunction : ordinary.mapDerivedCategory ⊣ (P.evaluation p).derived
  derivedInclusion : ∀ {m : SemiSimplexCategoryᵒᵖ} (a : m ⟶ p),
    (P.pullback a).derived ⟶ ordinary.mapDerivedCategory ⋙ (P.evaluation m).derived
  derivedCoproduct : ∀ (m : SemiSimplexCategoryᵒᵖ) (G : (R.fibre p).D),
    IsColimit (Cofan.mk ((P.evaluation m).derived.obj (ordinary.mapDerivedCategory.obj G))
      (fun a : m ⟶ p ↦ (derivedInclusion a).app G))
  derivedTransition : ∀ {m k : SemiSimplexCategoryᵒᵖ} (a : m ⟶ p) (b : k ⟶ m)
      (G : (R.fibre p).D),
    (P.pullback b).derived.map ((derivedInclusion a).app G) ≫
        (P.derivedTransition b).app (ordinary.mapDerivedCategory.obj G) =
      (P.composition b a).derived.inv.app G ≫ (derivedInclusion (b ≫ a)).app G
  derivedHomEquiv : ∀ (G : (R.fibre p).D) (E : (R.total h).D)
      (v : ordinary.mapDerivedCategory.obj G ⟶ E),
    derivedAdjunction.homEquiv G E v = (P.identity p).derived.inv.app G ≫
      (derivedInclusion (𝟙 p)).app G ≫ (P.evaluation p).derived.map v
  derivedInverse_homEquiv : ∀ (G : (R.fibre p).D) (E : (R.total h).D)
      (v : G ⟶ (P.evaluation p).derived.obj E)
      {m : SemiSimplexCategoryᵒᵖ} (a : m ⟶ p),
    (derivedInclusion a).app G ≫
        (P.evaluation m).derived.map ((derivedAdjunction.homEquiv G E).symm v) =
      (P.pullback a).derived.map v ≫ (P.derivedTransition a).app E
  derivedUnit : ∀ G : (R.fibre p).D,
    derivedAdjunction.unit.app G =
      (P.identity p).derived.inv.app G ≫ (derivedInclusion (𝟙 p)).app G
  derivedUnit_isIso : IsIso derivedAdjunction.unit
  derivedCounit : ∀ (E : (R.total h).D) {m : SemiSimplexCategoryᵒᵖ} (a : m ⟶ p),
    (derivedInclusion a).app ((P.evaluation p).derived.obj E) ≫
      (P.evaluation m).derived.map (derivedAdjunction.counit.app E) =
        (P.derivedTransition a).app E
  exactPullback : ∀ {m n : SemiSimplexCategoryᵒᵖ} (a : m ⟶ n)
    (K : CochainComplex (R.fibre n).modules ℤ), IsIso ((P.pullback a).alpha K)
  inclusion_representative : ∀ {m : SemiSimplexCategoryᵒᵖ} (a : m ⟶ p)
      (K : CochainComplex (R.fibre p).modules ℤ),
    ∃ t : ((P.pullback a).ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
        ((P.evaluation m).ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
      (∀ q : ℤ, t.f q = (inclusion a).app (K.X q)) ∧
      (derivedInclusion a).app (DerivedCategory.Q.obj K) ≫
          (P.evaluation m).derived.map (ordinary.mapDerivedCategoryFactors.hom.app K) ≫
          (P.evaluation m).ordinary.mapDerivedCategoryFactors.hom.app
            ((ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
        (P.pullback a).alpha K ≫ DerivedCategory.Q.map t
  unit_representative : ∀ K : CochainComplex (R.fibre p).modules ℤ,
    derivedAdjunction.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((adjunction.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K) ≫
        (P.evaluation p).ordinary.mapDerivedCategoryFactors.inv.app
          ((ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (P.evaluation p).derived.map (ordinary.mapDerivedCategoryFactors.inv.app K)
  counit_representative : ∀ K : CochainComplex (R.total h).modules ℤ,
    derivedAdjunction.counit.app (DerivedCategory.Q.obj K) =
      ordinary.mapDerivedCategory.map
          ((P.evaluation p).ordinary.mapDerivedCategoryFactors.hom.app K) ≫
        ordinary.mapDerivedCategoryFactors.hom.app
          (((P.evaluation p).ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((adjunction.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K)

attribute [instance] EvaluationFreeExtension.additive EvaluationFreeExtension.limits
  EvaluationFreeExtension.colimits

/-- The finite labelled pullback sums give an exact additive free extension left
adjoint to component evaluation, with the specified derived adjunction and formulas.

Source: Stacks Project, spaces-simplicial.tex, Tags 0D72, 0D74 and 0D9E,
agent-supplied injective-order-map adaptation
(blueprint: lem-sfb-semisimplicial-evaluation-free-adjoint).

Proof: (1) For each component take the finite coproduct of the actual transition
pullbacks, labelled by injections out of p. Its transitions carry each inclusion
through the inverse of the dependency's composition isomorphism. The coherence
laws give a system, hence a module on the total site, and naturality gives an
additive functor. (2) Restrict a system map to the identity summand. Conversely,
extend u on the a summand by pullback of u followed by the transition of E.
The transition law shows this is a system map; identity and composition give the
two inverse equations and their naturality. (3) The only order-preserving
self-injection is the identity, so evaluation of the free extension at p is the
identity-summand identification. This is the unit; the counit on the a summand is
the transition of E. (4) Exact pullbacks and finite coproducts preserve short exact
sequences, including the empty sum. Exact jointly conservative evaluations detect
exactness in the total category, so the free extension is exact.
(5) Apply lem-weil-pbc-termwise-adjunction-homotopy on all complexes. Exactness gives
the unbounded termwise localizations by lem-weil-pbc-exact-functor-derived-factorization.
Apply lem-sfb-adjunction-localization; its unit and counit formulas are the two
representative equations. (6) Localize the finite coproduct inclusions and their
identities. The localized inclusions give the derived coproduct and transition law.
By lem-weil-pbc-exact-functor-derived-functor, exact pullback agrees with its left
derived functor on every complex. The dependency's representative normalization
therefore identifies the localized transitions with its derivedTransition. Localize
the unit and counit, and use the counit formula for an arbitrary derived morphism
to obtain the inverse-adjunct formula, including morphisms given by roofs. -/
theorem semisimplicial_evaluation_free_adjoint (P : Presentation R h)
    (exact : ∀ {m n : SemiSimplexCategoryᵒᵖ} (a : m ⟶ n),
      PreservesFiniteLimits (P.pullback a).ordinary ∧
        PreservesFiniteColimits (P.pullback a).ordinary)
    (p : SemiSimplexCategoryᵒᵖ) : Nonempty (EvaluationFreeExtension P p) := by
  sorry

end CategoryTheory.SemisimplicialRingedTotal
