/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Constructible subobjects exhaust a directed-partition module

Source: ILO, Travaux de Gabber, Expose XVII, Proposition 7.4.3 and Lemma 7.4.4,
p. 306 (blueprint: lem-per-directed-galois-constructible-subobject-sup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.GaloisPartition

/-- Any subobject containing every constructible subobject in the fixed weak class is
the whole object. This asserts exhaustion in the subobject lattice, without asserting
directedness or choosing a small indexing category or a colimit.

Source: ILO XVII, Proposition 7.4.3 and the extension argument of Lemma 7.4.4, p. 306
(blueprint: lem-per-directed-galois-constructible-subobject-sup).

Proof: On one stratum use the torsion local-system monodromy equivalence. Finite subsets
of a discrete continuous representation of a profinite group have finite orbits. Their
coefficient spans give finitely generated stable submodules, directed by sums. Normal
subgroup ind-unipotence is inherited by these subrepresentations. Their associated sheaves
are constructible members of the one-stratum weak class and exhaust the original sheaf.
For a directed partition use its first open stratum and the complementary reduced closed
subscheme. The open/closed short exact sequence has kernel the extension by zero from the
first stratum; that extension preserves filtered unions and constructibility. Induction
exhausts the closed quotient by constructible subobjects in its weak class. Pull back each
of them to the middle object. Lemma 7.4.4, formalized as the finite-stage extension lemma,
descends its extension by the directed kernel to a constructible kernel stage. The middle
comparison is monic. Its sums with later kernel stages are constructible subobjects in the
weak class, exhaust that pullback, and hence exhaust the whole original object as the
closed quotient varies. Finite sums of constructible subobjects in the weak class stay in
that class and have finite stalk modules; monodromy on each stratum makes them locally
constant there, so they are constructible. Zero supplies nonemptiness. These facts give
directedness and supremum top. An empty partition has only zero sheaves; its subobject
lattice is subsingleton and zero supplies the same conclusions. -/
theorem constructible_subobject_sup (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsNoetherian X]
    (P : GaloisPartition X) (hP : P.IsDirected)
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    [Algebra (ULift.{u + 1} (ZMod ℓ)) A]
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (hE : P.modules A E) :
    ∀ U : Subobject E,
        (∀ S : Subobject E,
          P.constructible A (S : Sheaf X.smallEtaleTopology (ModuleCat A)) → S ≤ U) →
        U = ⊤ := by
  sorry

end AlgebraicGeometry.Scheme.GaloisPartition
