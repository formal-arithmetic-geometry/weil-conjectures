/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.RegularBaseChange

/-! # Maximal bad quotients for Popescu's theorem -/

@[expose] public section

universe u v
open CategoryTheory

/-- A failure of ind-smoothness has a nonzero maximal bad quotient.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07F5,
first paragraph, lines 2011--2026 (blueprint: lem-weil-pbc-popescu-maximal-bad-quotient).

Proof: For the given regular map, consider the ideals I for which the induced map
R/I → Λ/IΛ is not ind-smooth. The zero ideal belongs to this set: the quotient by
zero is canonically isomorphic to the original algebra. The ascending chain condition
on ideals gives a maximal member I. Quotients are Noetherian, and regular base change
along R → R/I gives regularity of the quotient map, using the tensor-quotient
isomorphism. Every nonzero ideal J of R/I comes from an ideal strictly containing I;
maximality and the quotient-of-quotient isomorphisms give ind-smoothness modulo J.
The quotient R/I is nonzero, since a zero base forces a zero target, which is itself
smooth over that base and hence a constant filtered colimit. All algebra and colimit
properties are transported along the canonical quotient isomorphisms. -/
theorem exists_popescu_maximal_bad_quotient
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ]
    (hreg : RingHom.IsRegular (algebraMap R Λ))
    (hbad : ¬ ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} R ↦ Algebra.Smooth R B) (CommAlgCat.of R Λ)) :
    ∃ (R' : Type u) (Λ' : Type (max u v)) (_ : CommRing R') (_ : CommRing Λ')
      (_ : Algebra R' Λ') (_ : IsNoetherianRing R') (_ : IsNoetherianRing Λ')
      (_ : Nontrivial R'),
      RingHom.IsRegular (algebraMap R' Λ') ∧
      (¬ ObjectProperty.ind.{max u v}
        (fun B : CommAlgCat.{max u v} R' ↦ Algebra.Smooth R' B) (CommAlgCat.of R' Λ')) ∧
      ∀ (I : Ideal R'), I ≠ ⊥ →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} (R' ⧸ I) ↦ Algebra.Smooth (R' ⧸ I) B)
          (CommAlgCat.of (R' ⧸ I) (Λ' ⧸ I.map (algebraMap R' Λ'))) := by sorry
