/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Direct image of a formal system with closed ambient support

Source: Stacks Project, Theorem 088E and Lemma 0CYJ.
(blueprint: lem-weil-pbc-formal-system-closed-support-pushforward)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Direct image along an open immersion preserves the coherent adic conditions when
all levels have support in a fixed closed subset of the ambient scheme contained in
that open immersion's image.

Source: Stacks Project, coherent.tex, Theorem 088E (theorem-grothendieck-existence),
the extension paragraph, and Lemma 0CYJ (lemma-pushforward-coherent-on-open).
(blueprint: lem-weil-pbc-formal-system-closed-support-pushforward)

Proof: Identify Y with the open image U of j. Lemma 0CYJ makes every j_*F_n coherent
and zero on X minus T. On U the restriction/direct-image counit identifies the entire
system, including its transitions, with F. Restriction of K identifies its products
and positive powers with those of K.comap j; restriction preserves cokernels.
Thus on U the power-product annihilation and quotient-transition conditions are those
of F. On X minus T all modules and their products and quotients are zero. These two
opens cover X since T lies in U. Vanishing of the power products is local. Each
transition therefore kills its indicated ideal-power product globally and factors
through its cokernel. This factor restricts to an isomorphism on each of the two
opens, so it is globally an isomorphism. These factors have the required equations
with quotient projections by construction. -/
theorem coherentFormal_pushforward_of_closed_support
    {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (j : Y ⟶ X) [IsOpenImmersion j] (K : X.IdealSheafData)
    (F : ℕᵒᵖ ⥤ Y.Modules) (T : TopologicalSpace.Closeds X)
    (hT : (T : Set X) ⊆ Set.range j.base)
    (hSupp : ∀ n : ℕ,
      {y : Y | ¬ Subsingleton ((F.obj (op n)).presheaf.stalk y)} ⊆
        j.base ⁻¹' (T : Set X))
    (hF : IsCoherentFormalModule (K.comap j) F) :
    IsCoherentFormalModule K (F ⋙ Scheme.Modules.pushforward j) := by sorry

end AlgebraicGeometry
