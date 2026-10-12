/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Topology.AbelianOpenExtensionByZero
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.KrullDimension

/-! # Integer extension-by-zero generators in the dimension induction

Source: Stacks Project, Cohomology, Proposition 02UZ, irreducible case.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Lower-dimensional vanishing kills the integer extension-by-zero generators
on an irreducible Noetherian space.
Source: Stacks Project, Cohomology, Proposition 02UZ, final two paragraphs
(https://stacks.math.columbia.edu/tag/02UZ).
(blueprint: new-node-irreducible-integer-extension-vanishing).

Proof: If U is empty its extension by zero is zero. Otherwise U is dense by
irreducibility. For d=0 every nonempty open is X: a nonempty proper closed
subset would contain an irreducible closed subset, giving a chain of length one.
Thus the generator is the constant integer sheaf and constant-sheaf acyclicity
kills its degree-p cohomology since p>0. For d>0 put Z = X \ U. It is a closed
Noetherian subspace of dimension at most d-1: append X to any irreducible closed
chain in Z. Use the short exact sequence from the open-closed decomposition of
the constant integer sheaf. The terms are j_!Z_U, Z_X, and i_*Z_Z, since inverse
image of a constant sheaf is constant. Constant-sheaf acyclicity kills H^p(X,Z_X).
Closed-pushforward comparison identifies H^(p-1)(X,i_*Z_Z) with H^(p-1)(Z,Z_Z).
The lower-dimensional hypothesis with e=d-1 kills this term, because p>d implies
p-1>d-1. The exact segment from these two outer terms to H^p(X,j_!Z_U) proves
that the latter is zero. The empty closed complement causes no problem: its
cohomology is zero by the same lower-dimensional hypothesis (or the empty axiom).
Only integer constant extensions are treated here; arbitrary sheaves are handled
separately by Lemma 02UX. -/
theorem irreducible_integer_extension_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hlower : ∀ (e : ℕ), e < d →
      ∀ (Y : Type u) [TopologicalSpace Y] [NoetherianSpace Y]
        (hdimY : topologicalKrullDim Y ≤ (e : WithBot ℕ∞))
        (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
        (r : ℕ), e < r → IsZero (CategoryTheory.Sheaf.H' G r (⊤ : Opens Y)))
    (p : ℕ) (hp : d < p) (U : Opens X) (hU : IsCompact (U : Set X)) :
    IsZero (CategoryTheory.Sheaf.H'
      ((TopCat.Sheaf.abelianOpenExtensionByZero U).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) p
      (⊤ : Opens X)) := by sorry

end TopCat
