/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Local constancy of a module subsheaf near a component generic point -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A subsheaf of a finite locally constant module sheaf is locally constant near each
component generic point.
Source: Stacks Project, Tag 09BH, proof of Proposition 59.74.1 (3), before induction.
(blueprint: lem-weil-pbc-module-subobject-generic-neighbourhood).

Proof: Remove the other irreducible components, then choose an etale trivialization of
G about the chosen geometric generic point. Shrink the trivializing scheme to an
irreducible neighbourhood. Write the target as the constant finite module M. The generic
stalk of F is a submodule N of M, hence finitely generated over the Noetherian ring.
Represent its finitely many generators on a common pointed etale neighbourhood, shrinking
so their images are the corresponding constant sections of M. Monicity makes the two
pullbacks of each lift equal; sheaf descent descends the lifts to the open image.
The resulting map from constant N into F is monic, since its composite into constant M
is monic. The quotient embeds into constant M/N and its geometric generic stalk is zero.
A nonzero germ in a constant sheaf on an irreducible etale neighbourhood persists at a
geometric generic point, so this quotient vanishes (Stacks 09BG). Thus F is constant N
there. The image of this etale neighbourhood is open and contains the component generic
point, and local constancy descends along this surjective etale map. Zero generic stalks
use N = 0 and the same argument; the empty scheme has no component generic point. -/
theorem exists_open_locallyConstant_of_mono_at_genericPoint
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type (u + 1)} [CommRing Λ]
    [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] [IsFiniteLocallyConstantSheaf G]
    (η : X) (hη : η ∈ genericPoints X) :
    ∃ U : X.Opens, η ∈ U ∧
      IsLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F) := by sorry

end AlgebraicGeometry.Scheme
