/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# A representative extension of a Zariski torsor

Source: Stacks Project, Cohomology of Sheaves, Lemma 02FQ, first construction.
(blueprint: lem-sc-zariski-torsor-representative-exists)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace CategoryTheory.Sheaf

/-- A Zariski torsor is the fibre over one of an extension by the integer sheaf.

Source: Stacks Project, Cohomology of Sheaves, Lemma 02FQ, first construction
(https://stacks.math.columbia.edu/tag/02FQ).
Proof: Sheafify the free abelian presheaf on the underlying sheaf of `T`, and map it
onto the constant integer sheaf by summing coefficients. Local sections of `T`
make this map locally surjective. On its kernel, send `[t] - [t']` to the unique
`g` with `g +ᵥ t' = t`; the torsor laws give additivity, independence of expressions,
and compatibility with restriction. Push out the kernel inclusion along this map
to obtain `G → E → ℤ`. Pushout of a short exact sequence in the abelian sheaf
category is short exact. The map `t ↦ [t]` into `E` has degree one and is equivariant.
Locally choose `t₀`: write `[t] = [t₀] + (t -ᵥ t₀)` in the pushout, so every degree-one
section is uniquely `[t₀] + g`. Thus this map identifies `T` with the lifting torsor
as sheaves, compatibly with the `G` action. All free groups and quotient sections
are formed in universe `u`; no enlargement of the coefficient universe is needed.
(blueprint: lem-sc-zariski-torsor-representative-exists) -/
theorem zariski_torsor_representative_exists (X : Scheme.{u})
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (T : G.Torsor) :
    ∃ (E : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ι : G ⟶ E) (p : E ⟶
        (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u, 0} ℤ)))
      (hzero : ι ≫ p = 0)
      (hS : (ShortComplex.mk ι p hzero).ShortExact),
      Nonempty (Torsor.Iso T
        (Torsor.lifts (IsTerminal.ofUnique (⊤ : Opens X)) hS
          ((toSheafify (Opens.grothendieckTopology X)
            ((Functor.const (Opens X)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u, 0} ℤ)))).app (op ⊤) ⟨1⟩))) := by
  sorry

end CategoryTheory.Sheaf
