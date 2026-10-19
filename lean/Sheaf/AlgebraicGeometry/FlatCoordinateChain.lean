/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.RingTheory.Depth
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.RingTheory.IsRegularOfDimensionDrop
import WeilConjectures.RingTheory.DepthQuotientNonzerodivisor
import Sheaf.Topology.PresheafModuleStalkFunctor

import Mathlib.Algebra.Category.ModuleCat.Stalk
import Sheaf.AlgebraicGeometry.ParameterChartGermCriterion
import WeilConjectures.Topology.PresheafModuleStalkFunctor
/-!
# Single-coordinate chains between flat quasi-finite charts

Source: SGA 4, Exposé XVIII, Lemmas 2.5–2.6, pp. 551–552
(blueprint: lem-pur-flat-coordinate-chain).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Two flat quasi-finite charts on a separated finite-type pure-dimensional
Cohen–Macaulay scheme over an algebraically closed field are joined, near any closed
point, by a finite chain of flat quasi-finite charts changing at most one coordinate
at each step. In dimension zero the chain has no edges.

Source: SGA 4, Exposé XVIII, Lemmas 2.5–2.6, pp. 551–552.
(blueprint: lem-pur-flat-coordinate-chain)

Proof:
1. In dimension zero both charts are the structure map to the base, up to the
canonical identification of zero-dimensional affine space with the base. Take U = X
and a chain of length zero. Otherwise fix the closed point x. Its residue field is k.
Center the coordinate germs of both charts in the maximal ideal of O_{X,x}. The
parameter-chart germ criterion says this local ring is Noetherian of dimension d
and that both centered tuples are systems of parameters.
2. Induct on the dimension e of a nonzero Noetherian Cohen–Macaulay local ring B to
connect any two ordered systems of parameters p and q by single-entry replacements.
For e = 0 the tuples are empty; for e = 1 one replacement suffices.
3. For e at least two, the dimension-drop criterion makes p and q regular sequences.
Their first entries are nonzerodivisors, and the quotients by those entries are
Cohen–Macaulay of dimension e - 1.
4. Choose z in the maximal ideal avoiding the associated primes of B, B/(p_1), and
B/(q_1). There are finitely many such primes and each is strictly smaller than the
maximal ideal, since these three rings have positive depth. Prime avoidance and the
associated-prime description of zero divisors make z regular on all three rings.
5. Complete (p_1,z) and (q_1,z) to systems of parameters a and b: the successive
Cohen–Macaulay quotients have dimension e - 2, and their depth supplies regular
sequences of that length. Lift them to the maximal ideal of B. The quotient B/(z)
is also Cohen–Macaulay of dimension e - 1.
6. Apply induction in B/(p_1), B/(z), and B/(q_1) to connect p to a, a to b, and b to
q with the respective fixed entry held in place. Lift each quotient chain one
changed coordinate at a time. At an endpoint, correct any differences that are
multiples of the fixed entry one coordinate at a time; the generated parameter
ideal stays unchanged. Concatenate these three chains and apply the result in O_{X,x}.
7. Choose one section representative near x for each distinct germ in this finite
chain, and shrink so its endpoints equal the actual centered coordinate sections.
This preserves every equality between adjacent coordinates. Prepend the successive
coordinate translations from the first chart to its centered chart, and append
the reverse translations for the second chart. The parameter-chart germ criterion
gives neighbourhoods where each of the finitely many charts is flat and quasi-finite.
Take a common affine neighbourhood U. Its section ring is a finitely generated
k-algebra, hence also a finite-type algebra over the coordinate-polynomial algebra
of each chart. Thus quasi-finiteness includes the required finite-type condition.
Enumerate the concatenation by Fin (r + 1), with the prescribed exact endpoints. -/
theorem exists_flat_coordinate_chain
    {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    (hpure : X.IsPureDimension d)
    (hCM : ∀ y : X,
      (IsLocalRing.depth (R := X.presheaf.stalk y) (X.presheaf.stalk y) : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk y))
    (f g : X ⟶ 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)))
    [f.IsOver (Spec (CommRingCat.of k))] [g.IsOver (Spec (CommRingCat.of k))]
    (hf : f.IsQuasiFinite) (hg : g.IsQuasiFinite) [Flat f] [Flat g]
    (x : X) (hx : x ∈ closedPoints X) :
    ∃ (U : X.Opens) (_hxU : x ∈ U) (r : ℕ)
      (w : Fin (r + 1) → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)))),
      (∀ j, w j ≫ 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k) = U.ι ≫ X ↘ Spec (CommRingCat.of k)) ∧
      (∀ j, (w j).IsQuasiFinite ∧ Flat (w j)) ∧
      w 0 = U.ι ≫ f ∧ w (Fin.last r) = U.ι ≫ g ∧
      (∀ j : Fin r, Set.Subsingleton {i : ULift.{u} (Fin d) |
        (w j.castSucc).appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) ≠
          (w j.succ).appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i)}) ∧
      (d = 0 → r = 0) := by
  sorry

end AlgebraicGeometry
