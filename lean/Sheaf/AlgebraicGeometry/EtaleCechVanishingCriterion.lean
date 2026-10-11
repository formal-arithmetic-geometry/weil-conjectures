/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# The étale Čech vanishing criterion

Source: Stacks Project, Cohomology on Sites, Lemma 03F9
(blueprint: lem-weil-pbc-cech-vanishing-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Use the standard small model of the étale category, fixing the model universe explicitly.
Source: Mathlib `essentiallySmallSelf`; Stacks 03F9
(blueprint: lem-weil-pbc-cech-vanishing-criterion). -/
local instance etaleSiteEssentiallySmallForCechCriterion (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  essentiallySmallSelf.{0} _

/-- The standard Grothendieck abelian structure supplies injective resolutions without an
extra hypothesis. Source: Mathlib `Sheaf.isGrothendieckAbelian_of_essentiallySmall`; Stacks 03F9
(blueprint: lem-weil-pbc-cech-vanishing-criterion). -/
local instance etaleSheavesGrothendieckForCechCriterion (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1} _ _

/-- Stacks Project, Lemma 03F9 (blueprint: lem-weil-pbc-cech-vanishing-criterion).
Vanishing higher Čech cohomology on a cofinal collection of coverings implies vanishing
higher derived evaluation on every object of the chosen collection `B`. The predicate `Cov`
is membership in the collection of indexed families; `hcover` says they are coverings.
Products in `Over U` are the iterated fibre products over `U`.

Proof (the node's seven steps). Fix `B` and `Cov`, and induct on positive degree, with the
assertion quantified over all Čech-acyclic abelian sheaves (Step 1). Embed such a sheaf `G`
into an injective sheaf `I`, using lem-weil-pbc-module-sheaves-enough-injectives and
def-sp-injective-resolutions; let `Q` be the cokernel (Step 2). Injective sheaves have zero
higher Čech cohomology by lem-weil-pbc-injective-sheaf-cech-acyclic, Stacks 03AW (Step 3).
The cofinality hypothesis and lem-weil-pbc-ses-cech-h1-surjective, Stacks 03F8, give
surjectivity of `I(U) → Q(U)` for `U ∈ B`. Left exact evaluation, or the beginning of
lem-weil-pbc-derived-functor-long-exact and lem-sp-derived-well-defined, gives exactness
of the whole section sequence (Step 4). All intersections belong to `B`, so products of
these short exact sequences give a degreewise short exact sequence of Čech complexes,
using def-weil-pbc-cech-complex and lem-weil-pbc-cochain-complexes-degreewise-exact (Step 5).
Its long exact homology sequence, lem-weil-pbc-complex-ses-homology-long-exact, shows that
`Q` is again Čech-acyclic (Step 6). Finally lem-weil-pbc-derived-functor-long-exact and
lem-weil-pbc-derived-functor-injective-vanishing give zero in degree one by the section
surjectivity, and in each higher degree by dimension shifting to `Q`. Apply the induction
to the originally given `F` (Step 7). -/
theorem isZero_rightDerived_etale_of_cech_vanishing
    (X : Scheme.{u}) (B : Set X.Etale)
    (Cov : ∀ (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale),
      (∀ i : I, V i ⟶ U) → Prop)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hcover : ∀ (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale)
      (f : ∀ i : I, V i ⟶ U), Cov U I V f →
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
    (hB : ∀ (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale)
      (f : ∀ i : I, V i ⟶ U), Cov U I V f →
      U ∈ B ∧ (∀ i : I, V i ∈ B) ∧
      ∀ (p : ℕ) (a : Fin (p + 1) → I),
        (piObj (fun j : Fin (p + 1) ↦ Over.mk (f (a j)))).left ∈ B)
    (hcofinal : ∀ (U : X.Etale), U ∈ B →
      ∀ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U),
        Sieve.ofArrows V f ∈ X.smallEtaleTopology U →
        ∃ (K : Type (u + 1)) (W : K → X.Etale) (g : ∀ k : K, W k ⟶ U),
          Cov U K W g ∧ ∀ k : K, ∃ (i : I) (t : W k ⟶ V i), t ≫ f i = g k)
    (hcech : ∀ (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale)
      (f : ∀ i : I, V i ⟶ U), Cov U I V f → ∀ (p : ℕ), 0 < p →
        IsZero (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
          ((Over.forget U).op ⋙ F.obj)).homology p)) :
    ∀ (U : X.Etale), U ∈ B → ∀ (p : ℕ), 0 < p →
      IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op U)).rightDerived p).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
