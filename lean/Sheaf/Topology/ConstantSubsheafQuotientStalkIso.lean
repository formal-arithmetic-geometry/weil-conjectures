/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import Sheaf.Topology.AbelianOpenExtensionByZero
import Sheaf.Topology.AbelianOpenExtensionByZeroStalks
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # ConstantSubsheafQuotientStalkIso

Source: Stacks Project, Cohomology, Lemma 0A38
(blueprint: lem-sc-constant-subsheaf-quotient-stalk-iso).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Source: Stacks Project, Cohomology, Lemma 0A38, final paragraph.
Proof: Fix x in U outside V. Every A i containing x has label b+1: a smaller
label would put x in V. At least one A i contains x. Extension-by-zero stalks
identify each active summand with the integers and every inactive summand with zero.
The epimorphism g remains surjective on stalks, so the germs of active s i generate
K_x. Their images under the injective stalk map to the constant integer sheaf all
equal b+1. This positive integer is nonzero; hence each active s i is a generator
of an infinite cyclic K_x. Since L_x is zero, exactness of stalks identifies
K_x with the cokernel stalk. The displayed compatibility says q_x takes the
canonical integer generator to that generator. It is therefore bijective and an
isomorphism in AddCommGrpCat. The empty-family case has no x in U.
(blueprint: lem-sc-constant-subsheaf-quotient-stalk-iso). -/
theorem constantSubsheaf_quotient_stalk_iso
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (n : ℕ) (A : Fin n → Opens X) (c : Fin n → ℕ)
    (g : (∐ fun i => (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K) [Epi g]
    (s : ∀ i, K.obj.obj (op (A i)))
    (hsection : ∀ i,
      (Sigma.ι (fun j => (abelianOpenExtensionByZero (A j)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A j)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) i ≫ g).hom.app
        (op (A i))
        (abelianOpenExtensionSection (A i)
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
          ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1))) = s i)
    (hvalue : ∀ i, (ι ≫ isoC.hom).hom.app (op (A i)) (s i) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op (A i)) (ULift.up (c i : ℤ)))
    (b : ℕ) (hc : ∀ i, 0 < c i ∧ c i ≤ b + 1) :
    let D := fun i => (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    let f : (∐ D) ⟶ K := Sigma.desc (fun i ↦
      if c i ≤ b then Sigma.ι D i ≫ g else 0)
    let L := image f
    let l : L ⟶ K := image.ι f
    let U := iSup A
    let V := ⨆ i : Fin n, if c i ≤ b then A i else ⊥
    (∀ x : X, x ∉ V → IsZero (TopCat.Presheaf.stalk L.obj x)) →
    ∀ q : (abelianOpenExtensionByZero (iSup A)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ cokernel l,
      (∀ i, c i = b + 1 → q.hom.app (op (A i))
        (abelianOpenExtensionSection (iSup A)
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
          (A i) (le_iSup A i)
          ((toSheafify
            (Opens.grothendieckTopology ((Opens.toTopCat X).obj (iSup A)))
            ((Functor.const (Opens ((Opens.toTopCat X).obj (iSup A)))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op ((Opens.map (iSup A).inclusion').obj (A i))) (ULift.up 1))) =
          (cokernel.π l).hom.app (op (A i)) (s i)) →
      ∀ x : X, x ∈ U → x ∉ V →
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map q.hom) := by sorry

end TopCat.Sheaf
