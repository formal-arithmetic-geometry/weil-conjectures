/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.Paper.IntegralConstructibleSerre

/-!
# Uniform proper heart amplitude over a Noetherian base

The finite-amplitude part of the proper heart theorem, independently of coproduct
continuity. Source: Bhatt--Scholze, Section 6.8, and blueprint proper heart bound.
(blueprint: lem-sfb-noetherian-proper-heart-uniform-bound)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper direct image has a uniform upper bound on the Serre coproduct closure of
constructible modules, for an ell-adic coefficient ring and a Noetherian base scheme.

Source: Bhatt--Scholze, Theorem 6.7.1, Lemma 6.7.2 and Remark 6.8.15;
blueprint sk-lem-proper-heart-bound and
sk-thm-sfb-proper-base-change, integral compactness/direct-sums clause (1).
(blueprint: lem-sfb-noetherian-proper-heart-uniform-bound)

Proof: a proper morphism is of finite type and the base is quasi-compact. A finite
collection of affine charts bounds the dimensions of all its geometric fibres by one
integer r. On constructible integral modules, reduce an integral lattice modulo the
powers of a uniformizer. Proper torsion cohomological dimension gives vanishing above
2r for every reduction. Derived completeness and the Milnor exact sequence give
vanishing above 2r+1 for the lattice. Inverting ell gives the same bound for finite
rational coefficients. For the condensed algebraic closure, use the filtered system
of finite coefficient fields and bounded-below qcqs continuity; the bound is independent
of the coefficient field. Finite extensions given by an arbitrary presentation have
the same coefficient rings after transport along a continuous field isomorphism.
Constructible modules form a coherent abelian subcategory over these coefficients;
their filtered-colimit closure is replete and closed under kernels, cokernels,
extensions and small coproducts. It therefore contains their Serre coproduct closure.
Bounded-below qcqs continuity extends the constructible bound to these filtered
colimits. Restricting to the smaller Serre coproduct closure proves the assertion.
This proof is local on the Noetherian target; it uses a relative fibre bound, not
finite-dimensionality of the base or positive characteristic. Empty fibres, zero
modules and the empty coproduct satisfy the same bound.
-/
theorem properLowerStar_uniformBound_ellAdic
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [IsEllAdicFinitenessCoefficient ℓ Λ]
    {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p] :
    ∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ Z M →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
