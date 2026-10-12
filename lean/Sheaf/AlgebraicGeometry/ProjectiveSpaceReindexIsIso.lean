/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible

/-! # Invertibility of the coordinate reindexing morphism

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-reindex-is-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- The morphism defined by the coordinate sections in a bijectively renamed order
is an isomorphism. No finiteness or nonemptiness assumption is needed.

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-reindex-is-iso).

Proof: On the open indexed by i, the free generator is the pullback of T_(b i)
under the identity. The coefficients of the other sections are T_(b j)/T_(b i).
The standardOpenIso identifies these opens with relative affine spaces over S.
After restriction over an affine open Spec R of S, the construction
homOfIsFreeGenerator therefore has the map of polynomial coordinate rings
over R sending T_j/T_i to T_(b j)/T_(b i), and fixing R by
homOfIsFreeGenerator_over. These affine opens cover the relative charts. Bijectivity of b
identifies the variables other than i with the variables other than b i, so this
ring map is an isomorphism, with inverse given by b.symm. These affine maps have
the same coordinate-ratio formulas on intersections. The maps formed by b and
b.symm compose to the identity on every standard chart, since their maps on the
base and on all coordinate ratios are identities. The standard charts cover,
so equality of these composites holds globally. Thus the displayed morphism
has a two-sided inverse. For empty coordinate types the schemes are empty and
the same chartwise equality argument applies to the empty cover. -/
theorem isIso_homOfIsFreeGenerator_reindex (β γ : Type u) (b : γ ≃ β)
    (S : Scheme.{u}) :
    let s := fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
      (twistOneSection β S (b j))
    let U := fun j : γ ↦ standardOpen β S (b j)
    let hs := fun j : γ ↦
      isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j)
    let hU : ⨆ j, U j = ⊤ := (b.iSup_comp).trans (iSup_standardOpen β S)
    IsIso (homOfIsFreeGenerator s U hs (ℙ(β; S) ↘ S) hU) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
