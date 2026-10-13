/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation

/-! # Spreading density of an open in ordinary fibres

Source: Stacks Project, Tag 054X, Lemma 37.24.3.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- An open subset dense in the generic fibre is dense in every ordinary fibre
on a neighbourhood of the generic point.

Source: Stacks Project, Tag 054X, Lemma 37.24.3.
Proof: give the closed complement Z of W its reduced induced scheme structure.
The assumption says that Z has nowhere dense generic fibre. Replace the base
by its reduction; the associated base changes are universal homeomorphisms,
so neither the assumption nor the conclusion changes. The reduced base is
integral because it has a generic point. Apply generic flatness and finite
presentation to X and Z, and intersect their generic neighbourhoods. Suppose
that Z_t has nonempty interior in X_t. Choose a generic point of a component
of X_t in that interior. Flatness of Z lifts it to a generalization in Z over
the generic point (Tag 03HV). Constancy of fibre dimension along this
specialization for flat locally finitely presented morphisms (Tag 054U,
Lemma 37.22.10) equates the dimensions of Z and X at the lifted point: at the
original point they agree because Z_t contains a neighbourhood. A component
of Z at the lifted point consequently has the dimension of a component of
X there, contradicting nowhere density in the generic fibre. Thus the
complement is nowhere dense in each fibre. Its open complement is dense.
The common nonempty base open contains the generic point; transport it back
through the reduction homeomorphism. Empty fibres satisfy density vacuously.

(blueprint: lem-sbc-generic-open-fibre-density) -/
theorem exists_open_fibre_dense_of_generic_dense {X T : Scheme.{u}}
    (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (W : X.Opens) (η : T) (hη : IsGenericPoint η Set.univ)
    (hdense : Dense ((f.fiberι η) ⁻¹' (W : Set X))) :
    ∃ U : T.Opens, η ∈ U ∧
      ∀ (t : T), t ∈ U → Dense ((f.fiberι t) ⁻¹' (W : Set X)) := by sorry

end AlgebraicGeometry
