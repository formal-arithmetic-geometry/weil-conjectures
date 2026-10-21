/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall

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

/-- An actual cover inside a generated covering sieve.
Source: Stacks, Sites, Definition 00VH. Induct on the generated topology,
using covering pullbacks and bind composition. The same argument occurs in
`BoundedConstantChainMapLocal.covering_refinement`. -/
private theorem covering_refinement {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings) {U : C} {S : Sieve U}
    (hS : S ∈ J.toGrothendieck U) : ∃ T ∈ J U, T ≤ S.arrows := by
  classical
  have : J.HasIsos := hJ.1
  induction hS with
  | of X R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top X =>
    exact ⟨Presieve.singleton (𝟙 X), J.mem_coverings_of_isIso (𝟙 X), by simp⟩
  | pullback X S hS Y f ih =>
    obtain ⟨R, hR, hle⟩ := ih
    let I := Σ Z : C, {a : Z ⟶ X // R a}
    let V : I → C := fun i ↦ i.1
    let a : ∀ i : I, V i ⟶ X := fun i ↦ i.2.1
    have heq : Presieve.ofArrows V a = R := by
      funext Z b
      apply propext
      constructor
      · rintro ⟨i⟩
        exact i.2.2
      · intro hb
        exact Presieve.ofArrows.mk (Y := V) (f := a) ⟨Z, b, hb⟩
    obtain ⟨P, p, q, hpq, hp⟩ := hJ.2.2 I X V a (heq ▸ hR) Y f
    refine ⟨Presieve.ofArrows P p, hp, ?_⟩
    rintro Z b ⟨i⟩
    change S (p i ≫ f)
    rw [(hpq i).w]
    exact S.downward_closed (hle _ _ i.2.2) (q i)
  | transitive X S T hS hT ihS ihT =>
    obtain ⟨R, hR, hle⟩ := ihS
    have hh : ∀ (Y : C) (f : Y ⟶ X) (_ : R f),
        ∃ Q ∈ J Y, Q ≤ (T.pullback f).arrows := by
      intro Y f hf
      exact ihT (hle _ _ hf)
    choose Q hQ hQT using hh
    refine ⟨R.bind (fun {Y f} hf ↦ Q Y f hf),
      hJ.2.1 X R (fun {Y} f hf ↦ Q Y f hf) hR hQ, ?_⟩
    intro Z f hf
    obtain ⟨Y, g, a, ha, hg, rfl⟩ := hf
    exact hQT Y a ha _ _ hg


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
  classical
  have _ := hdisjoint
  have _ := hstable
  have _ := hempty
  -- Implement the local-equality and local-lift steps directly in the value universe.
  have : EssentiallySmall.{max u v w} C := essentiallySmallSelf.{w} C
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{max u v w} C).inverse.op)
        (Type (max u v w)) := fun _ ↦ hasLimitsOfShape_of_essentiallySmall _ _
  have : J.toGrothendieck.WEqualsLocallyBijective (Type (max u v w)) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
      J.toGrothendieck (A := Type (max u v w))
  have hsheaf : Presieve.IsSheaf J.toGrothendieck (sheafify J.toGrothendieck P) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((presheafToSheaf J.toGrothendieck (Type (max u v w))).obj P).property
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p q hpq
    obtain ⟨S, hS, hle⟩ := covering_refinement J hJ
      (Presheaf.equalizerSieve_mem J.toGrothendieck
        (toSheafify J.toGrothendieck P) p q hpq)
    obtain ⟨n, U, j, ⟨hc⟩, hj⟩ := hrefine S hS
    apply (hprod n U W j hc).injective
    funext a
    obtain ⟨V, f, hf, h, hh⟩ := hj a
    have heq := hle V f hf
    change P.map f.op p = P.map f.op q at heq
    change P.map (j a).op p = P.map (j a).op q
    rw [← hh, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, heq]
  · intro t
    obtain ⟨S, hS, hle⟩ := covering_refinement J hJ
      (Presheaf.imageSieve_mem J.toGrothendieck (toSheafify J.toGrothendieck P) (U := op W) t)
    obtain ⟨n, U, j, ⟨hc⟩, hj⟩ := hrefine S hS
    choose V f hf h hh using hj
    have hlift : ∀ a, ∃ r : P.obj (op (U a)),
        (toSheafify J.toGrothendieck P).app (op (U a)) r =
          (sheafify J.toGrothendieck P).map (j a).op t := by
      intro a
      obtain ⟨s, hs⟩ := hle (V a) (f a) (hf a)
      refine ⟨P.map (h a).op s, ?_⟩
      rw [NatTrans.naturality_apply, hs, ← Functor.map_comp_apply, ← op_comp, hh]
    choose r hr using hlift
    obtain ⟨p, hp⟩ := (hprod n U W j hc).surjective r
    refine ⟨p, ?_⟩
    apply (hsheaf.isSheafFor_of_mem_precoverage (hcover n U W j hc)).isSeparatedFor.ext
    rintro Z g ⟨a⟩
    rw [← NatTrans.naturality_apply]
    exact (congrArg ((toSheafify J.toGrothendieck P).app (op (U a)))
      (congrFun hp a)).trans (hr a)
  · intro Q hQempty hQprod α
    exact congrArg (fun η ↦ η.app (op W)) (toSheafify_naturality J.toGrothendieck α)

end CategoryTheory
