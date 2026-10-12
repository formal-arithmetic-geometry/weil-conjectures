/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Finite geometric detection of scalar annihilation

Source: normalization exact-sequence blueprint, finite-coefficient reduction, steps 1 and 3
of `lem-weil-pbc-finite-coefficient-of-finite-stalks`.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Finitely many geometric stalks detect scalar annihilation of a constructible module sheaf.
This does not require finite stalks or a finite coefficient ring.

Source: normalization exact-sequence blueprint, finite-coefficient reduction in
`lem-weil-pbc-finite-pushforward-finite-stalk-module`; steps 1 and 3 of
`lem-weil-pbc-finite-coefficient-of-finite-stalks`.
(blueprint: lem-weil-pbc-constructible-finite-stalk-annihilator-detection)

Proof: Choose the finite stratification witnessing constructibility. Each stratum has
Noetherian underlying space because its immersion is an embedding into X, and is therefore
quasi-compact. Choose a trivializing etale cover of each stratum. The images of its members
are open and cover the stratum, so finitely many cover it. Discard empty members and choose
one point in every remaining member; compose with its maps to the stratum and X. List these
finitely many points as x_i. A geometric stalk of F at x_i is linearly isomorphic to the
constant module on the selected chart: lift the algebraic closure of the residue field of
x_i along the immersion and the etale chart, then use pullback/stalk compatibility and the
constant-sheaf stalk formula. A scalar killing these selected stalks thus kills the constant
value on every selected chart. Every geometric point of X lifts to its locally closed
stratum and a selected chart, so that scalar kills every geometric stalk of F. The scalar
endomorphism of F is consequently zero by conservativity of geometric stalks for module
sheaves. Evaluating that endomorphism on an arbitrary etale object says the scalar belongs
to its section-module annihilator; intersect over all such objects. For empty X select
n = 0: there are no geometric stalks, conservativity makes every scalar endomorphism zero,
and the intersection of section annihilators is the unit ideal. For the zero sheaf any
finite selection works. No section-module finiteness is claimed. -/
theorem exists_finite_stalk_annihilator_detection
    (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf F) :
    ∃ (n : ℕ) (x : Fin n → X),
      (⨅ i : Fin n, Module.annihilator Λ
        ((((pointSmallEtale (X.algClosurePoint (x i))).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj F)) ≤
      ⨅ U : X.Etaleᵒᵖ, Module.annihilator Λ (F.obj.obj U) := by
  sorry

end AlgebraicGeometry.Scheme
