/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Generic constancy of module subsheaves -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A module subsheaf of a constructible sheaf is finite locally constant on a dense open.
Source: Stacks Project, Tag 09BH, proof of (3), generic-neighbourhood argument
(blueprint: lem-weil-pbc-module-subobject-generic-constancy).

Proof: On a dense open the target is finite locally constant. At each of the finitely
many component generic points, choose an etale trivialization and remove the other
components. The target is a constant finitely generated module M on an irreducible
scheme. Its generic submodule N is finitely generated over the Noetherian ring.
Lift finitely many generators to sections on one pointed etale neighbourhood,
shrinking until their images are the corresponding constant sections of M.
Monicity makes the lifts agree on the fibre product, so etale descent descends them
to its open image. The constant N embeds in the source there. The quotient embeds
in the constant M/N and has zero generic stalk, hence is zero: a nonzero locally
constant germ in a constant sheaf on an irreducible etale neighbourhood would remain
nonzero at its generic point. Thus the source is constant N on that neighbourhood.
Descent gives finite local constancy on an open about each component generic point.
Remove the other components before taking these opens; they are pairwise disjoint.
Their finite union is dense and the source is finite locally constant on it.
For the empty scheme take the empty open; the zero sheaf is also covered. -/
theorem exists_dense_open_of_mono_noetherian
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type (u + 1)} [CommRing Λ]
    [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] [IsConstructibleSheaf G] :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F) := by sorry

end AlgebraicGeometry.Scheme
