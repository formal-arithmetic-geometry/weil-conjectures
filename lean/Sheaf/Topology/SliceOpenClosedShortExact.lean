/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Exactness for the slice-site open extension

Source: Stacks Project, Modules, Lemma 02UT
(blueprint: lem-sc-slice-open-closed-short-exact).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Modules, Lemma 02UT (the two stalk cases).
(blueprint: lem-sc-slice-open-closed-short-exact).

Proof: On an open V contained in U, the index type V ⟶ U has exactly one
member. The direct sum is therefore F(V), and the hypothesis makes the
presheaf map induced by a the identity on this summand. On any other open
there are no summands, so that map is zero. The equivalence between opens
of U and the slice of opens over U identifies this construction, including
its map to F, with the topological extension by zero of F restricted to U.
The sheafification universal property makes a the canonical counit.
At a point in U the counit is an isomorphism on stalks and the closed
pushforward has zero stalk. At a point in the complement the source stalk
is zero. The closed-pushforward germ comparison and the inverse-image
stalk comparison identify the stalk of the unit with the identity on F's
stalk, since both comparisons send each germ to the germ of its unit image.
Thus in the two cases the sequence is respectively identity followed by
zero, or zero followed by identity. The composite has zero stalk maps,
and the stalk functors are jointly faithful, so its composite is zero.
The stalkwise short-exactness criterion now gives the asserted short exact
complex. For U empty the first sheaf is zero and the last map is an
isomorphism; for U all of X the first map is an isomorphism and the last
sheaf is zero. No Noetherian assumption is needed. -/
theorem slice_open_closed_short_exact
    (X : TopCat.{u}) (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      ((siteExtensionByZeroPresheaf U).obj (F.over U).obj) ⟶ F)
    (ha : ∀ (V : Opens X) (φ : V ⟶ U) (s : F.obj.obj (Opposite.op V)),
      (a.hom.app (Opposite.op V))
        ((toSheafify (Opens.grothendieckTopology X)
          ((siteExtensionByZeroPresheaf U).obj (F.over U).obj)).app (Opposite.op V)
          (DirectSum.of (fun ψ : V ⟶ U ↦
            (F.over U).obj.obj (Opposite.op (Over.mk ψ))) φ s)) = s) :
    ∃ h : a ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          TopCat.of ↥((U : Set X)ᶜ) ⟶ X)).unit.app F = 0,
      (ShortComplex.mk a
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            TopCat.of ↥((U : Set X)ᶜ) ⟶ X)).unit.app F) h).ShortExact := by
  sorry

end TopCat
