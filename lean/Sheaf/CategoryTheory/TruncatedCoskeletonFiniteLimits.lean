/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Coskeleta of truncated simplicial objects as finite limits

Source: literature/stacks-project/simplicial.tex, Lemmas 0183--0185 and
hypercovering.tex, Lemma 01GD (blueprint: lem-weil-pbc-truncated-coskeleton-finite-limits)
-/

@[expose] public section

universe u v w v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Coskeleta exist as a functor, are computed by finite limits, and commute with
finite-limit-preserving functors, on objects and morphisms.

Source: literature/stacks-project/simplicial.tex, Lemmas 0183--0185 and
hypercovering.tex, Lemma 01GD (blueprint: lem-weil-pbc-truncated-coskeleton-finite-limits).

1. For each degree, there are finitely many arrows from truncated simplices to that
simplex, and finitely many arrows between them. Form the limit of the diagram
sending such an arrow to its truncated source term
(def-galois-finite-limits-colimits, def-weil-pbc-simplicial-set). Its projections
induce the simplicial operators by postcomposition; uniqueness proves their
identity and composition laws (def-weil-pbc-simplicial-object). Mathlib's
`RightExtension.coneAt` is exactly this cone, using the opposite-comma encoding.
2. Maps to these limits are compatible families. A map out of a simplicial object
is determined by the components at identity arrows. Conversely, a map from its
truncation gives the family by composing with each simplicial operator. These
constructions are inverse, proving the coskeleton mapping property
(def-weil-pbc-simplicial-coskeleton).
3. In a truncated degree the identity arrow is initial in the opposite indexing
category. Its projection is therefore an isomorphism, so the counit is an isomorphism
(Stacks 0184--0185).
4. A finite-limit-preserving functor sends each of these cones to a limit cone.
Their projection equations give the same simplicial operators after applying the
functor, hence the image object with the image counit is a coskeleton. The image
of a canonical coskeletality isomorphism is still an isomorphism and satisfies the
canonical counit equation, proving preservation of coskeletality.
5. A truncated morphism induces maps of the limit diagrams. Their unique induced
maps commute with simplicial operators and counits. The mapping property proves
uniqueness; applying it to identities and composites gives a functor, and applying
it to an inverse preserves isomorphisms. Applying the finite-limit-preserving
functor to the same equations gives precisely the induced map between image coskeleta.
6. Presheaf limits are computed objectwise and evaluations preserve finite limits
(lem-weil-pbc-presheaf-finite-limits-objectwise). Thus steps 4 and 5 apply to every
presheaf evaluation, including the canonical coskeletality isomorphism.
-/
theorem truncatedCoskeletonFiniteLimits
    (C : Type u) [Category.{v} C] [HasFiniteLimits C] (m : ℕ) :
    ∃ (R : SimplicialObject.Truncated C m ⥤ SimplicialObject C)
      (ε : R ⋙ SimplicialObject.truncation m ⟶ 𝟭 _),
      (∀ U, (R.obj U).IsRightKanExtension (ε.app U)) ∧
      (∀ U, Nonempty
        ((Functor.RightExtension.mk (R.obj U) (ε.app U)).IsPointwiseRightKanExtension)) ∧
      (∀ U, IsIso (ε.app U)) ∧
      (∀ (U U' : SimplicialObject.Truncated C m) (β : U ⟶ U') (b : R.obj U ⟶ R.obj U'),
        (SimplicialObject.truncation m).map b ≫ ε.app U' = ε.app U ≫ β →
          b = R.map β) ∧
      ∀ (D : Type w) [Category.{v'} D] (Φ : C ⥤ D),
        PreservesFiniteLimits Φ →
        (∀ U, (R.obj U ⋙ Φ).IsRightKanExtension (Functor.whiskerRight (ε.app U) Φ)) ∧
        (∀ (U U' : SimplicialObject.Truncated C m) (β : U ⟶ U')
          (b : R.obj U ⋙ Φ ⟶ R.obj U' ⋙ Φ),
          (SimplicialObject.truncation m).map b ≫ Functor.whiskerRight (ε.app U') Φ =
              Functor.whiskerRight (ε.app U) Φ ≫ Functor.whiskerRight β Φ →
            b = Functor.whiskerRight (R.map β) Φ) ∧
        (∀ (K : SimplicialObject C)
          (c : K ⟶ R.obj ((SimplicialObject.truncation m).obj K)),
          (SimplicialObject.truncation m).map c ≫
            ε.app ((SimplicialObject.truncation m).obj K) = 𝟙 _ →
          IsIso c →
          ∀ c' : K ⋙ Φ ⟶ R.obj ((SimplicialObject.truncation m).obj K) ⋙ Φ,
            (SimplicialObject.truncation m).map c' ≫
              Functor.whiskerRight (ε.app ((SimplicialObject.truncation m).obj K)) Φ = 𝟙 _ →
            IsIso c')
    := by
  sorry

end CategoryTheory
