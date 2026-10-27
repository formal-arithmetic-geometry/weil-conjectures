/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V9
-/
module

public import Sheaf.Paper.LisseCompletedSystemData
public import Sheaf.Paper.EtaleMonodromyRealizationData
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Completed integral lattices before monodromy reconstruction

Source: Bhatt--Scholze, Proposition 6.8.4(6), Lemma 6.8.13, first paragraph,
and the geometric-cover argument in Lemma 7.4.10.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CompletedLisse

/-- A lisse rational module on a connected normal base has a completed integral lattice,
expressed using the coefficient identification of any fixed normalized comparison.
This is a lattice-existence assertion; it constructs no representation or equivalence.

Source: Bhatt--Scholze, Proposition 6.8.4(6), Lemma 6.8.13, first paragraph,
and Lemma 7.4.10, pp. 59--61, 71
(blueprint: lem-a1-normal-lisse-completed-lattice).

Proof. Choose a small model of the finite coefficient extension and transport continuous
coefficient sheaves, finite free charts, and their scalar maps along the field isomorphism.
Apply normal_lattice_finite_cover_presentation to the given normal Noetherian separated
base. The invertibility required there follows from invertibility in every residue field
by the local-ring unit criterion. The presentation supplies a finite etale surjection
Y to X and an actual locally finite free integral lattice on Y whose rationalization is
the pullback of L. Its normalized completion isomorphisms identify this with a lattice
for continuous integral coefficients, preserving the rationalization map.

Use the equivalence between sheaf modules and internal abelian-sheaf modules and the
continuous-coefficient realization to apply continuousLisse_finiteEtale_lattice. The
construction there takes the image of the pushed lattice in the rational pushforward
and pulls it back along the rational adjunction unit. Thus it descends existence of a
lattice without assuming a descent datum on the given lattice. Its finite local matrix
models prove local finite freeness and its localization comparison gives rationalization
isomorphic to L. Transport back from internal modules and the small coefficient model.

Finally extend this integral lattice along C.coefficientIso.hom to the completed ring.
Scalar restriction and extension along a ring-sheaf isomorphism are inverse equivalences
and preserve finite free charts. Associativity of scalar extension and
C.coefficientIso.hom followed by C.coefficientIso.inv equal to the identity identify its
rationalization along the displayed map with L. These tensor isomorphisms send pure
tensors to the same products, so they apply to the specified comparison C. Rank zero
uses the zero lattice throughout. No monodromy equivalence or integral-model theorem
whose proof depends on that equivalence is used. -/
theorem normal_lisse_completed_lattice (l : ℕ) [Fact l.Prime]
    (P : Base.{u} l) [ConnectedSpace P.X]
    (hnormal : ∀ x : P.X,
      IsDomain (P.X.presheaf.stalk x) ∧ IsIntegrallyClosed (P.X.presheaf.stalk x))
    (C : Comparison l P) (L : SfRationalModules l P.E P.X)
    (hL : L.IsFiniteLocallyFree) :
    ∃ M : Integral l P,
      Nonempty ((completedAdicChange P.X
        (C.coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X)).obj M.obj ≅ L) := by
  sorry

end AlgebraicGeometry.ProEtale.CompletedLisse
