/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Termwise Tor acyclicity computes derived tensor

Source: Stacks Project, `perfect.tex`, Tag 08IB, `lemma-compare-base-change`
(blueprint: lem-pc-termwise-tor-acyclic-derived-tensor).

The derived tensor is represented by an arbitrary K-flat resolution `f : P.obj ⟶ Q`.
The canonical comparison is represented by `f ⊗ B`, with `B` in degree zero. Applying
`tensoringRight B` termwise gives exactly this tensor complex and comparison map, as
complexes of R-modules, as in the node. The choice of resolution is universally quantified.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

/-- (blueprint: lem-pc-termwise-tor-acyclic-derived-tensor) For a bounded complex `Q`
of modules over a commutative ring `R`, if every term has vanishing positive Tor with
an `R`-algebra `B`, the canonical derived-to-ordinary tensor comparison is a
quasi-isomorphism and induces an isomorphism in every cohomological degree.
Source: Stacks Project, Tag 08IB, `lemma-compare-base-change`, the Tor-independent
comparison. The comparison is expressed on every K-flat resolution of `Q`.

Proof: Choose bounds `a,b` for the nonzero terms. The stupid truncations give degreewise
split exact sequences with quotient `Q.X n` in degree `n`; they retain termwise Tor
acyclicity (def-weil-pbc-tor-modules). For a one-term complex, a shifted projective
resolution is K-flat (lem-pc-module-bounded-flat-kflat), and the homology of its tensor
with `B` is Tor (def-weil-pbc-tor-modules). Positive Tor vanishes by assumption, and
Tor zero is the ordinary tensor. The zero complex is immediate. Induct down the finite
stupid-truncation filtration. Both derived tensor (lem-pur-derived-change-of-rings) and
ordinary tensor send these split sequences to distinguished triangles
(lem-weil-pbc-complex-ses-triangle). The canonical comparison is natural and commutes
with shifts, hence gives a morphism of triangles
(lem-weil-pbc-commshift-nattrans-triangle-morphism) and of long exact cohomology sequences
(lem-weil-pbc-derived-cohomology-ladder). The four outer vertical maps in each five-term
segment are isomorphisms by induction and the one-term case, so the middle map is an
isomorphism (lem-weil-pbc-five-lemma). This proves the comparison is a quasi-isomorphism;
its homology maps are therefore isomorphisms in every degree. -/
theorem quasiIso_tensor_of_termwise_tor_acyclic
    {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
    (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Q.X n))
    (hTor : ∀ (n : ℤ) (i : ℕ), 0 < i →
      IsZero (((Tor' (ModuleCat.{u} R) i).obj (Q.X n)).obj (ModuleCat.of R B)))
    (P : CochainComplex.KFlat (ModuleCat.{u} R)) (f : P.obj ⟶ Q)
    (hf : QuasiIso f) :
    QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) ∧
    ∀ i : ℤ, IsIso (homologyMap
      ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) i) := by
  sorry

end CochainComplex
