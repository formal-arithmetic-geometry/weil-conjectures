/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import Sheaf.Topology.AbelianOpenExtensionByZero
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # ConstantSubsheafQuotientGluing

Source: Stacks Project, Cohomology, Lemma 0A38
(blueprint: lem-sc-constant-subsheaf-quotient-gluing).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Source: Stacks Project, Cohomology, Lemma 0A38, final paragraph.
Proof: The opens with label b+1 together with the lower-label union cover iSup A,
since every positive label is at most b+1. On the top opens the sections s i agree
on intersections: apply the monomorphism into the constant integer sheaf and use
naturality of the constant section. Their images under π therefore glue on the top
union. The sheaf Q restricted to the lower union is zero, because all its stalks
there vanish. Consequently those images agree with zero on overlaps with the lower
union. Glue with zero to obtain a section on iSup A. Use the constant-sheaf
adjunction to define a morphism on the restriction, then send each open-slice
summand of the extension presheaf by restriction of that morphism and apply
sheafifyLift. On each A i with top label its unit section has the stated image.
Empty unions and an absent top layer give the zero morphism and vacuous equations.
(blueprint: lem-sc-constant-subsheaf-quotient-gluing). -/
theorem constantSubsheaf_quotient_gluing
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (n : ℕ) (A : Fin n → Opens X) (c : Fin n → ℕ)
    (s : ∀ i, K.obj.obj (op (A i)))
    (hvalue : ∀ i, (ι ≫ isoC.hom).hom.app (op (A i)) (s i) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op (A i)) (ULift.up (c i : ℤ)))
    (b : ℕ) (hc : ∀ i, 0 < c i ∧ c i ≤ b + 1)
    (Q : Sheaf AddCommGrpCat X) (π : K ⟶ Q)
    (hzero : ∀ x : X, x ∈ (⨆ i : Fin n, if c i ≤ b then A i else ⊥) →
      IsZero (TopCat.Presheaf.stalk Q.obj x)) :
    ∃ q : (abelianOpenExtensionByZero (iSup A)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ Q,
      ∀ i, c i = b + 1 → q.hom.app (op (A i))
        (abelianOpenExtensionSection (iSup A)
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
          (A i) (le_iSup A i)
          ((toSheafify
            (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
            ((Functor.const (Opens ((Opens.toTopCat X).obj (iSup A)))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op ((Opens.map (iSup A).inclusion').obj (A i))) (ULift.up 1))) =
          π.hom.app (op (A i)) (s i) := by sorry

end TopCat.Sheaf
