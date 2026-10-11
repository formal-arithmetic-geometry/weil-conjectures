/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Essential finite type for Artinian local algebras

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 07DT (blueprint:
lem-weil-pbc-artinian-local-essentially-finite-type-residue).
-/

@[expose] public section

namespace RingHom

/--
(blueprint: lem-weil-pbc-artinian-local-essentially-finite-type-residue)
Let `f : R →+* S` be a homomorphism of commutative rings. If `S` is Artinian and
local, and the induced map from `R` to its residue field is essentially of finite
type, then `f` is essentially of finite type. This is the converse direction of
Stacks Project, Lemma Tag 07DT, part (3); its proof uses the finite generation
statement for Artinian local algebras over their residue fields and composition
of essentially finite type maps.
-/
theorem essFiniteType_of_artinian_local_residue
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    [IsArtinianRing S] [IsLocalRing S]
    (h : (IsLocalRing.residue S).comp f |>.EssFiniteType) :
    f.EssFiniteType := by
  sorry

end RingHom
