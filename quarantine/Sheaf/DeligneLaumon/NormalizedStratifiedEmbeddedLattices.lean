/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData

/-! # Embedded lattices on a reduced refinement -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.StratifiedContinuousLattices

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} X.ProEt

/-- Refine a given finite lisse partition by embedded integral lattices and reduce it.

Source: Bhatt--Scholze, Lemma 6.8.13 first paragraph, Proposition 6.8.4(6),
Remark 6.8.15; Stacks Project, Tag 054M; steps 1, 6 and 7 of
lem-zl-continuous-constructible-stratified-lattices.
(blueprint: lem-zl-normalized-stratified-embedded-lattices).

Proof: each member of S is separated and finite type over D.k: immersions are
separated and locally of finite type, and a subspace of the noetherian base is
quasi-compact. Continuous coefficient restriction identifies its given finite locally
free module with the rational encoding of a lisse internal module. Apply the
fixed-field stratified lattice theorem on each member and take the finite disjoint
union of these refinements. Composition of immersions gives the factor maps and
factorization. Encode every internal integral inclusion. The identity restriction
comparison preserves its monomorphism; the lisse criterion preserves local freeness.
The unit-normalized scalar comparison identifies its extension-induced map with
ordinary rationalization, so it is an isomorphism. Replace each refined domain by
its reduction. Reduction is a surjective closed immersion, so these domains have the
same disjoint covering images. Exact inverse image preserves the monomorphism;
locallyFree_upperStar preserves lisseness; the tensor comparison preserves the
inclusion-induced localization. These are precisely the LatticeRestriction data,
including their unit equations. The identical pullback construction applies to any
further immersion. If the base is empty use the empty refinement; a rank-zero module
has the zero lattice. No lattice is glued between different strata and E is unchanged. -/
theorem normalized_stratified_embedded_lattices (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (c : CoefficientFamily l E)
    (X : PerAdic.Base D.k)
    (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (S : Scheme.FiniteLocallyClosedStratification X.scheme)
    (hS : ∀ i : Fin S.n, ((proEtaleModuleInverseImage (S.immersion i)
      (rationalCoefficientSheaf l X.scheme E)).obj F).IsFiniteLocallyFree) :
    Nonempty (Stratified l E X.scheme c.atScheme F S) := by sorry

end WeilConjectures.StratifiedContinuousLattices
