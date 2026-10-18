/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Sheafification at an object with finite partition refinements

Source: Stacks Project, Pro-étale Topology, Tag 0F63,
`lemma-presheaf-value-weakly-contractible`, abstract finite-partition form;
Sites, Tags 00WB, 00WK and 00WH (blueprint: lem-zl-partition-refinement-sheafification).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Source: Stacks Project, Pro-étale Topology, Tag 0F63, abstract finite-partition
refinement form; Sites, Tags 00WB, 00WK and 00WH
(blueprint: lem-zl-partition-refinement-sheafification).

A finite decomposition is an arbitrary colimiting cofan, rather than just a chosen coproduct.
The empty family is included throughout. The value universe contains both site universes.

Proof: (1) The sheafification unit has a sheaf as target. The empty covering makes its
value at an initial object a singleton, as is the corresponding value of `P`.
(2) For injectivity, the local-equality part of
`lem-weil-pbc-site-sheafification-sections-local` gives a covering on which two sections
with equal images agree. Refine it by a finite decomposition of `W`. Functoriality
makes the restrictions agree on every component; injectivity of the product restriction
map makes the original sections equal.
(3) For surjectivity, the local-representative part of the same lemma gives local lifts
of a sheafified section. Refine by a finite decomposition and restrict the lifts to its
components. The product bijection assembles them into a section of `P(W)`. Its image
agrees with the given section on all components, hence globally by sheaf separatedness,
since the component maps cover. For an empty partition the empty product supplies the
section and separatedness for the empty covering gives the same equality.
(4) Functoriality of sheafification from `def-weil-pbc-sheafification` gives
`α ≫ η_Q = η_P ≫ α♯`; evaluation at `W` is the asserted naturality square. -/
theorem bijective_toSheafify_of_partition_refinement
    {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteCoproducts C]
    [HasStrictInitialObjects C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (hdisjoint : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
      IsColimit (Cofan.mk X j) → ∀ (a b : Fin n), a ≠ b →
        Nonempty (IsInitial (pullback (j a) (j b))))
    (hstable : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
      IsColimit (Cofan.mk X j) → ∀ (Y : C) (f : Y ⟶ X),
        Nonempty (IsColimit (Cofan.mk Y (fun a ↦ pullback.snd (j a) f))))
    (hcover : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
      IsColimit (Cofan.mk X j) → Presieve.ofArrows U j ∈ J X)
    (W : C)
    (hrefine : ∀ (S : Presieve W), S ∈ J W →
      ∃ (n : ℕ) (U : Fin n → C) (j : ∀ a, U a ⟶ W),
        Nonempty (IsColimit (Cofan.mk W j)) ∧
        ∀ a, ∃ (V : C) (f : V ⟶ W), S f ∧ ∃ h : U a ⟶ V, h ≫ f = j a)
    (P : Cᵒᵖ ⥤ Type (max u v w))
    (hempty : Nonempty (P.obj (op (⊥_ C))) ∧ Subsingleton (P.obj (op (⊥_ C))))
    (hprod : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
      IsColimit (Cofan.mk X j) →
        Function.Bijective (fun s : P.obj (op X) ↦ fun a ↦ P.map (j a).op s)) :
    Function.Bijective ((toSheafify J.toGrothendieck P).app (op W)) ∧
      ∀ (Q : Cᵒᵖ ⥤ Type (max u v w))
        (_ : Nonempty (Q.obj (op (⊥_ C))) ∧ Subsingleton (Q.obj (op (⊥_ C))))
        (_ : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
          IsColimit (Cofan.mk X j) →
            Function.Bijective (fun s : Q.obj (op X) ↦ fun a ↦ Q.map (j a).op s))
        (α : P ⟶ Q),
        α.app (op W) ≫ (toSheafify J.toGrothendieck Q).app (op W) =
          (toSheafify J.toGrothendieck P).app (op W) ≫
            (sheafifyMap J.toGrothendieck α).app (op W) := by
  sorry

end CategoryTheory
