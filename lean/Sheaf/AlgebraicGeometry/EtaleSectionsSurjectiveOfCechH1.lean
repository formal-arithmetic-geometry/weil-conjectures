/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Surjectivity of étale sections from vanishing Čech H¹

Source: Stacks Project, Cohomology on Sites, Lemma 03F8 (lemma-ses-cech-h1)
(blueprint: lem-weil-pbc-ses-cech-h1-surjective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- A short exact sequence of abelian étale sheaves is surjective on sections over `U`
if the kernel has vanishing Čech H¹ on a cofinal system of coverings of `U`.
`Cov` is the membership predicate of that system of indexed families. Its members are
coverings by `hcover`; `hcofinal` expresses refinement of every covering by a member.
The Čech complex is computed in `Over U`, so products are fibre products over `U`.
Source: Stacks Project, Lemma 03F8 (lemma-ses-cech-h1).
(blueprint: lem-weil-pbc-ses-cech-h1-surjective)

Proof (the node's six steps). (1) Short exactness makes `S.g` an epimorphism and `S.f`
its kernel inclusion. By lem-weil-pbc-sheafification-exact, kernels are computed
sectionwise, so the section map of `S.f` is injective with image the kernel of `S.g`.
(2) Fix a section `h` of `S.X₃` over `U`. The epimorphism is locally surjective by
lem-weil-pbc-abelian-sheaf-epi-locally-surjective, so `h` has local lifts on a covering.
(3) Refine this covering to one in `Cov` using `hcofinal`, and restrict the lifts along
the refinement maps. Naturality shows that they remain lifts of `h`.
(4) On pairwise fibre products, the difference of the two restricted lifts maps to zero,
so it has a unique preimage in `S.X₁`. These differences form a Čech 1-cocycle: on triple
fibre products their alternating sum maps under the injective kernel inclusion to
`(g₂ - g₁) - (g₂ - g₀) + (g₁ - g₀) = 0`.
(5) By `hcech`, this cocycle is a coboundary of a 0-cochain of `S.X₁`. Subtract its image
under `S.f` from each local lift. The corrected lifts agree on pairwise fibre products
and still map to the restrictions of `h`.
(6) The sheaf condition of `S.X₂` glues these lifts to a section over `U`. Its image is `h`
by the separatedness of `S.X₃`. This proves surjectivity. -/
theorem surjective_sections_of_cech_h1_vanishing
    (X : Scheme.{u}) (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) (U : X.Etale)
    (Cov : ∀ (I : Type (u + 1)) (V : I → X.Etale), (∀ i : I, V i ⟶ U) → Prop)
    (hcover : ∀ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U),
      Cov I V f → Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
    (hcofinal : ∀ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U →
      ∃ (K : Type (u + 1)) (W : K → X.Etale) (g : ∀ k : K, W k ⟶ U),
        Cov K W g ∧ ∀ k : K, ∃ (i : I) (t : W k ⟶ V i), t ≫ f i = g k)
    (hcech : ∀ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U),
      Cov I V f → IsZero (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
        ((Over.forget U).op ⋙ S.X₁.obj)).homology 1)) :
    Function.Surjective (S.g.hom.app (op U)) := by
  sorry

end AlgebraicGeometry.Scheme
