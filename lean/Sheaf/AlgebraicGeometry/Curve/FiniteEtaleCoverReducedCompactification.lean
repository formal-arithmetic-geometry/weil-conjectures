/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve

import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Reduced cartesian compactification

Source: Stacks Project, etale-cohomology.tex, 03SD and 05K0.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- A finite etale cover of an open of a reduced curve has a reduced finite
compactification whose square over the original open is cartesian.

Source: Stacks Project 03SD (lemma-vanishing-easier), compactification paragraph;
05K0 (lemma-quasi-finite-separated-pass-through-finite).
(blueprint: r1-finite-etale-cover-reduced-cartesian-compactification)

Proof: Apply finite Zariski main theorem to v followed by j. Replace its finite
scheme by the reduced closure of the image of V. Since V is etale over the reduced
open U, it is reduced, and embeds openly in this reduced closure. The closed
immersion of the closure followed by the original finite morphism is finite.
Composition gives a separated finite-type k-scheme; integral incomparability
bounds its dimension by that of X. Over U the open V in the inverse image of U
is finite: a map into a separated U-scheme whose composite to U is finite is
finite. Its image is therefore closed. It is dense in that inverse image since
V is dense in the closure, hence surjective. A surjective open immersion is an
isomorphism, which identifies V with Y times_X U and gives the pullback square.
The empty-cover case gives the empty compactification and the same square. -/
theorem exists_reduced_cartesian_finite_cover_compactification
    {k : Type u} [Field k] [IsAlgClosed k] {X U V : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (v : V ⟶ U) [IsFinite v] [Etale v] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (a : V ⟶ Y),
      IsFinite p ∧ IsCurve (p ≫ f) ∧ IsReduced Y ∧ IsOpenImmersion a ∧
        IsPullback a v p j := by sorry

end AlgebraicGeometry.IsCurve
