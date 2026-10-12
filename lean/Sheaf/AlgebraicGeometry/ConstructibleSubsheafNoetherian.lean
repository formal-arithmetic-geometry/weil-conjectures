/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric
import Sheaf.AlgebraicGeometry.IrreducibleLisseStrata
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Subsheaves of constructible module sheaves on Noetherian schemes

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, and Stacks Project,
Proposition 59.74.1(3), Tag 03RY
(blueprint: lem-weil-pbc-constructible-subobjects-noetherian).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every subsheaf of a constructible sheaf of modules over a finite commutative ring
on the small etale site of a Noetherian scheme is constructible.
Source: Stacks Project, Proposition 59.74.1(3), Tag 03RY
(blueprint: lem-weil-pbc-constructible-subobjects-noetherian).

Proof following the blueprint:
1. For a subsheaf `H` of a constant finite module sheaf on an irreducible scheme `W`,
   membership of each constant element `m` in a geometric stalk of `H` defines an open
   subset `W_m`. Represent membership by sections on etale neighbourhoods; their images
   are open by `lem-weil-pbc-flat-lfp-open`. The local lifts glue uniquely by monicity
   (`lem-weil-pbc-constant-subsheaf-generic`).
2. Intersect the finitely many nonempty `W_m`. Each contains the generic point, so the
   intersection is nonempty. On it `H` is the constant generic-stalk submodule: the glued
   sections induce an isomorphism on geometric stalks, hence an isomorphism by
   `lemma-weil-pbc-geometric-stalk-conservative`.
3. Use Noetherian induction on closed subsets of `T`. Pullback preserves the inclusion
   by `prop-weil-pbc-geometric-stalks-exact` and preserves constructibility. Separate the
   finitely many irreducible components (`lem-weil-pbc-noetherian-finite-components`).
   On an irreducible component choose a generic lisse open using
   `lem-weil-pbc-irreducible-lisse-strata`, then an etale trivialization. Remove the other
   components of the trivializing scheme and apply steps 1 and 2. Its open image gives
   a nonempty base open on which `G` is finite locally constant by etale descent.
   Induction partitions the proper closed complement. Adjoin the open; every resulting
   locally closed part is constructible because `T` is Noetherian (Stacks Tag 005L).
   This is the required finite constructible lisse partition. -/
theorem isConstructibleEtaleModuleSheaf_of_mono_noetherian
    {T : Scheme.{u}} [IsNoetherian T] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {G F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (i : G ⟶ F) [Mono i] (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleModuleSheaf G := by
  sorry

end AlgebraicGeometry.Scheme
