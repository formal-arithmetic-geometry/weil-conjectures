/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import Sheaf.Topology.GlueSheavesOfModules

/-!
# Čech transition functions glue local trivial line bundles

Source: Stacks Project, Sheaves Lemma 00AM (lemma-glue-sheaves-structures),
with uniqueness from Lemma 04TN (lemma-glue-maps).
(blueprint: lem-sc-glue-component-transition-cocycle)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace AlgebraicGeometry

/-- Units on pairwise overlaps satisfying the Čech identities glue the trivial local
modules to an invertible module with chosen frames, uniquely up to the unique
isomorphism preserving those frames. All overlap comparisons use restriction maps.

Source: Stacks Project, Sheaves Lemma 00AM (lemma-glue-sheaves-structures),
with uniqueness from Lemma 04TN (lemma-glue-maps).
(blueprint: lem-sc-glue-component-transition-cocycle).

Step 1: take the local modules `O_{U a}` and multiplication by `g a b` as the
transition isomorphisms; the inverse units give their inverses
(`def-sc-invertible-module`). Step 2: identity and inverse transitions follow from
`hid` and `hinv`; after restriction to any triple overlap, `hcoc` says their
composites equal the direct transition. Step 3: apply
`lem-weil-pbc-glue-sheaves-of-modules` to obtain a module and compatible
trivializations. Their inverse images of 1 are the frames `e`, and compatibility
reads `e a = g a b • e b` on the overlap. Step 4: these frames make the module
locally free of rank one, hence invertible (`def-sc-invertible-module`). For any
other glued module, the local maps sending its frames to `e` agree on overlaps;
the fully faithful gluing theorem (`lem-weil-pbc-glue-sheaves-of-modules`)
glues them and their inverses to the unique global isomorphism. -/
theorem exists_invertible_of_cech_transition
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hcover : ⨆ a, U a = ⊤)
    (g : ∀ a b, Γ(X, U a ⊓ U b)ˣ)
    (hid : ∀ a, g a a = 1)
    (hinv : ∀ a b (W : X.Opens) (ha : W ≤ U a) (hb : W ≤ U b),
      Units.map (X.presheaf.map (homOfLE (le_inf hb ha)).op).hom.toMonoidHom (g b a) =
        (Units.map (X.presheaf.map (homOfLE (le_inf ha hb)).op).hom.toMonoidHom (g a b))⁻¹)
    (hcoc : ∀ a b c (W : X.Opens)
      (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c),
      Units.map (X.presheaf.map (homOfLE (le_inf ha hc)).op).hom.toMonoidHom (g a c) =
        Units.map (X.presheaf.map (homOfLE (le_inf ha hb)).op).hom.toMonoidHom (g a b) *
          Units.map (X.presheaf.map (homOfLE (le_inf hb hc)).op).hom.toMonoidHom (g b c)) :
    ∃ (L : X.Modules) (e : ∀ a, Γ(L, U a)),
      L.IsInvertible ∧ (∀ a, IsFreeGenerator (e a)) ∧
      (∀ a b, L.presheaf.map (homOfLE inf_le_left).op (e a) =
        (g a b).val • L.presheaf.map (homOfLE inf_le_right).op (e b)) ∧
      ∀ (L' : X.Modules) (e' : ∀ a, Γ(L', U a)),
        (∀ a, IsFreeGenerator (e' a)) →
        (∀ a b, L'.presheaf.map (homOfLE inf_le_left).op (e' a) =
          (g a b).val • L'.presheaf.map (homOfLE inf_le_right).op (e' b)) →
        ∃! f : L' ≅ L, ∀ a, f.hom.app (U a) (e' a) = e a := by
  sorry

end AlgebraicGeometry
