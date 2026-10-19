/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed

/-!
# Separatedness of an admissible finite scheme quotient

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IX, §1.4,
printed pp. 132--133 (blueprint: lem-per-admissible-finite-quotient-separated).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- The quotient of a separated finite-type scheme by an admissible finite group action
is separated over the Noetherian base. The map `r : Q ⟶ S` is the induced structure map,
expressed by the compatibility equation `q ≫ r = p`.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IX, §1.4,
printed pp. 132--133 (blueprint: lem-per-admissible-finite-quotient-separated).

Proof: the admissible quotient predicate gives that `q` is finite and its underlying
quotient map is surjective. A finite morphism is proper and hence universally closed;
applying `isSeparated_of_surjective_universallyClosed` to `q`, with the displayed
compatibility equation and the separated map `p`, proves that `r` is separated.
No freeness of the action and no invertibility assumption on the order of the group is
used.
-/
theorem isSeparated_of_admissibleFiniteSchemeQuotient
    {G : Type v} [Group G] [Finite G]
    {S M Q : Scheme.{u}} [IsNoetherian S]
    (p : M ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (a : G →* Aut M) (q : M ⟶ Q)
    (hquot : IsAdmissibleFiniteSchemeQuotient a q)
    (r : Q ⟶ S) (hr : q ≫ r = p) : IsSeparated r := by
  sorry

end AlgebraicGeometry
