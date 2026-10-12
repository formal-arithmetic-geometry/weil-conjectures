/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.Mathlib.RingTheory.LocalRing.Basic

/-! # Clopen subsets and idempotent global functions of schemes

Source: Stacks Project, Algebra, Lemma 10.21.3 (Tag 00EE,
`lemma-disjoint-decomposition`), the affine case; the scheme case follows by the sheaf
property, as in Schemes, Tag 01I5, proof of `lemma-disjoint-union-affines`.
(blueprint: lem-weil-pbc-scheme-clopen-idempotent)

## Main statements

* `scheme_clopen_idempotent`: the clopen correspondence and its pullback compatibility.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The locus where a global function has nonzero germ, used for the idempotent
correspondence of Stacks Project, Algebra, Tag 00EE (`lemma-disjoint-decomposition`).
(blueprint: lem-weil-pbc-scheme-clopen-idempotent) -/
def idempotentOpen {X : Scheme.{u}} (e : Γ(X, ⊤)) : Set X :=
  {x | X.presheaf.Γgerm x e ≠ 0}

/-- (blueprint: lem-weil-pbc-scheme-clopen-idempotent) Let `X` be a scheme. For every
idempotent global section `e`, the set of points where its germ is nonzero equals the
locus where its germ is one and is clopen, with complementary locus for `1 - e`.
Idempotents and clopen opens are bijective, with inverse given by the section restricting
to one and zero on the two complementary opens. Pullback of an idempotent locus is
its inverse image under a scheme morphism.

Source: Stacks Project, Algebra, Tag 00EE (`lemma-disjoint-decomposition`), extended
from affine schemes by the sheaf property (Schemes, Tag 01I5, proof).

Proof, following the node's five steps:
1. Germ maps are ring homomorphisms, so every germ of an idempotent is idempotent.
   Stalks are local rings (`def-pc-scheme`); by
   `lem-weil-pbc-local-ring-idempotent-zero-one`, these germs are zero or one.
   Thus the nonzero-germ locus is the one-germ locus and the basic open of the section
   (`lem-weil-pbc-basic-open-function`).
2. The basic open is open. The section `1 - e` is idempotent, and its germs are the
   complements of the germs of `e`. Its locus is exactly the complementary set,
   also open, proving closedness of the original locus.
3. Equal loci give equal germs, since idempotent germs are zero or one. The sheaf
   property, `lem-weil-pbc-sheaf-sections-determined-by-germs`, gives equal sections,
   proving injectivity.
4. For a clopen `U`, use `lem-weil-pbc-sheaf-disjoint-union-product` to identify
   global sections with sections on `U` times sections on its complement. The inverse
   image of `(1, 0)` is unique, is idempotent, and has locus `U`, proving surjectivity
   and describing the inverse. This also works for an empty open, whose ring is zero.
   Restriction values and the displayed germ values are equivalent by sheaf extensionality.
5. Pullback on global sections is a ring homomorphism, so it preserves idempotence.
   Apply `lem-weil-pbc-basic-open-pullback` to the basic opens identified in step 1
   to obtain the inverse-image equality. -/
theorem scheme_clopen_idempotent (X : Scheme.{u}) :
    (∀ (e : Γ(X, ⊤)), IsIdempotentElem e →
      idempotentOpen e = {x : X | X.presheaf.Γgerm x e = 1} ∧
      IsOpen (idempotentOpen e) ∧
      IsClosed (idempotentOpen e) ∧
      idempotentOpen (1 - e) = (idempotentOpen e)ᶜ) ∧
    (Function.Injective (fun (e : {e : Γ(X, ⊤) // IsIdempotentElem e}) ↦
      idempotentOpen e.1) ∧
      (∀ (U : Set X), IsOpen U ∧ IsClosed U → ∃ e : Γ(X, ⊤),
        IsIdempotentElem e ∧ idempotentOpen e = U)) ∧
    (∀ (U : {U : Set X // IsOpen U ∧ IsClosed U}), ∃! (e : Γ(X, ⊤)),
      IsIdempotentElem e ∧
      (∀ x : X, x ∈ U.1 → X.presheaf.Γgerm x e = 1) ∧
      (∀ x : X, x ∉ U.1 → X.presheaf.Γgerm x e = 0)) ∧
    (∀ {Y : Scheme.{u}} (g : Y ⟶ X) (e : Γ(X, ⊤)), IsIdempotentElem e →
      IsIdempotentElem (g.appTop e) ∧
      idempotentOpen (g.appTop e) = g.base ⁻¹' idempotentOpen e) := by sorry

end AlgebraicGeometry
