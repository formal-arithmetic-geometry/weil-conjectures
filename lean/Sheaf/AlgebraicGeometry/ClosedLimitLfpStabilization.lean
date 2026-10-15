/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Stabilization of a closed inverse system with locally finitely presented limit

Source: Stacks Project, Limits, Tag 081B, Lemma `lemma-finite-type-eventually-closed`,
clause (3), applied to the identity of the limit
(blueprint: lem-weil-pbc-closed-limit-lfp-stabilization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A directed inverse system of quasi-compact schemes locally of finite type over a base,
with closed immersion transitions and locally finitely presented limit over that base,
has isomorphic limit projections at every sufficiently large stage.

Source: Stacks Project, Limits, Tag 081B, clause (3)
(blueprint: lem-weil-pbc-closed-limit-lfp-stabilization).

Proof plan:
1. Fix a stage `a`. Local finite type and quasi-compactness give a finite affine cover of
   that stage by charts mapping into affine opens of the base. Closed immersion transitions
   give quotient rings on all later inverse-image charts, with surjective transition maps.
2. By `exists_limit_affine_transition`, its open-restriction and affine clauses identify
   the limit charts with spectra of the filtered colimits of these rings. Every colimit
   element has a representative, so the map from the chart ring at `a` is surjective.
   Local finite presentation makes each limit chart ring finitely presented over its base
   chart ring, by `LocallyOfFinitePresentation.finitePresentation_appLE`.
3. Present the stage chart ring by finitely many polynomial generators. The composite
   polynomial-ring surjection to the limit has finitely generated kernel by
   `Algebra.FinitePresentation.ker_fg_of_mvPolynomial`. Its images generate the kernel of
   the stage-to-limit map, so the limit chart ring is a quotient by finitely many elements.
4. Eventual equality of representatives in a filtered colimit kills these finitely many
   elements at one common later stage. Surjectivity and equality of kernels identify every
   subsequent chart ring with the limit chart ring. An empty generator list needs no delay.
5. Take a common upper bound for the finitely many chart bounds. Each limit projection is
   an isomorphism on this affine open cover. Its local inverses agree on overlaps by inverse
   uniqueness and glue by `Scheme.Cover.glueMorphisms`. Both composites are identities by
   `Scheme.Cover.hom_ext`. An empty cover means the stage and every later scheme are empty,
   and their projections are isomorphisms as well. -/
theorem exists_isIso_limitProjection_of_isClosedImmersion_of_locallyOfFinitePresentation
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (S : Scheme.{u}) (D : Iᵒᵖ ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, LocallyOfFiniteType (t.app i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsClosedImmersion (D.map f)]
    (c : Cone D) (hc : IsLimit c) (q : c.pt ⟶ S)
    (hq : ∀ i : Iᵒᵖ, c.π.app i ≫ t.app i = q)
    [LocallyOfFinitePresentation q] :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsIso (c.π.app (op i)) := by
  sorry

end AlgebraicGeometry
