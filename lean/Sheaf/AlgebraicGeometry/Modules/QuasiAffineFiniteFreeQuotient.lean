/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators

/-! # Finite free quotients on Noetherian quasi-affine opens

Source: Stacks Project, Tag 0EKP, the global-generation step of (2) to (3).
(blueprint: new-sbc-quasi-affine-embedding-existence)
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free module on an open of a Noetherian affine scheme is
an epimorphic image of a finite free module.

Source: Stacks Project, Tag 0EKP, the global-generation step of (2) to (3),
with the ample invertible module the structure sheaf.
(blueprint: new-sbc-quasi-affine-embedding-existence)

Proof: V is quasi-compact because Spec R is Noetherian. At every point choose a
principal open D(f) contained in V on which N is finite free; principal opens form
an affine basis, so finitely many such opens cover V. The finite locally free N
is quasi-coherent. Apply exists_tensorPowSection_eq_restrict, the section-clearing
lemma, to each basis section on each D(f), with the invertible module O_V and its
section f restricted to V. Identify every tensor power of O_V with O_V. This gives
a global section whose restriction is f to some nonnegative power times the
chosen basis section. On D(f) the factor is invertible. Thus these sections still
span N at every point of D(f). Their union is finite and spans every stalk of N.
The morphism from the free module indexed by this finite collection, sending its
basis to these sections, is therefore epi by the stalkwise criterion. Reindex the
collection by ULift (Fin r). On the empty open use the empty collection and r = 0;
zero ranks add no sections, and different opens may have different finite ranks. -/
theorem exists_epi_free_of_isFiniteLocallyFree
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of R)).Opens) (N : V.toScheme.Modules) [N.IsFiniteLocallyFree] :
    ∃ (r : ℕ) (β : free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ N),
      Epi β := by
  sorry

end AlgebraicGeometry.Scheme.Modules
