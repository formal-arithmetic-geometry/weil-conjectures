/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# The site of the closed complement of a representable subterminal

Source: Stacks Project, Sites, Tag 08LY (`lemma-closed-subtopos`), on its chosen
subcanonical finite-limit site (blueprint: lem-trf-closed-complement-site-construction).

A presieve encodes a family by its arrows; `Sieve.generate` implements the covering-family
convention in the node. The direct image is specified on all underlying presheaves and maps.
-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

private def openSieve {C : Type w} [SmallCategory C] (U V : C) : Sieve V where
  arrows W _ := Nonempty (W ⟶ U)
  downward_closed := fun ⟨u⟩ g ↦ ⟨g ≫ u⟩

private def complementTopology {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (U : C) : GrothendieckTopology C where
  sieves V := {R | R ⊔ openSieve U V ∈ J V}
  top_mem' V := by simp
  pullback_stable' {_ _ _} f h := J.pullback_stable f h
  transitive' {_ _} hS R h := by
    apply J.transitive hS (R ⊔ openSieve U _)
    intro W f hf
    rcases hf with hf | hf
    · exact h hf
    · apply J.covering_of_eq_top
      exact Sieve.pullback_eq_top_of_mem _ (Or.inr hf)

private lemma le_complementTopology {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (U : C) : J ≤ complementTopology J U :=
  fun _ _ hR ↦ J.superset_covering le_sup_left hR

private lemma openSieve_eq_generate {C : Type w} [SmallCategory C] [HasFiniteLimits C]
    (X : C) (hX : IsTerminal X) (U : C) (i : U ⟶ X) (V : C) :
    openSieve U V = Sieve.generate (Presieve.singleton (pullback.snd i (hX.from V))) := by
  apply le_antisymm
  · intro W f hf
    obtain ⟨u⟩ := hf
    have e : u ≫ i = f ≫ hX.from V := hX.hom_ext _ _
    exact ⟨_, pullback.lift u f e, _, Presieve.singleton.mk,
      pullback.lift_snd _ _ _⟩
  · rw [Sieve.generate_le_iff]
    intro W f hf
    cases hf
    exact ⟨pullback.fst _ _⟩

private lemma complement_isSheaf_iff {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (U : C) (P : Cᵒᵖ ⥤ Type w)
    (hP : Presieve.IsSheaf J P) :
    Presieve.IsSheaf (complementTopology J U) P ↔
      ∀ (W : C), Nonempty (W ⟶ U) → Nonempty (Unique (P.obj (.op W))) := by
  classical
  constructor
  · intro h W hW
    have hbot : (⊥ : Sieve W) ∈ complementTopology J U W := by
      change (⊥ : Sieve W) ⊔ openSieve U W ∈ J W
      simp only [bot_sup_eq]
      apply J.covering_of_eq_top
      apply top_unique
      intro Z f _
      obtain ⟨u⟩ := hW
      exact ⟨f ≫ u⟩
    have hh := h ⊥ hbot
    let x : Presieve.FamilyOfElements P (⊥ : Presieve W) := fun _ _ h ↦ h.elim
    obtain ⟨t, _, ht⟩ := hh x (by intro _ _ _ _ _ _ _ h; exact h.elim)
    exact ⟨{ default := t, uniq := fun s ↦ ht s (by intro _ _ h; exact h.elim) }⟩
  · intro h V R hR x hx
    let y : Presieve.FamilyOfElements P ((R ⊔ openSieve U V).arrows) :=
      fun {W} f hf ↦ if hr : R f then x f hr else (h W (hf.resolve_left hr)).some.default
    have hyR {W : C} (f : W ⟶ V) (hf : R f) : y f (Or.inl hf) = x f hf := by
      dsimp [y]
      rw [dif_pos hf]
    have hy : y.Compatible := by
      apply (Presieve.compatible_iff_sieveCompatible y).2
      intro W Z f g hf
      by_cases hr : R f
      · have hgr := R.downward_closed hr g
        simp only [y, dif_pos hr, dif_pos hgr]
        exact hx.to_sieveCompatible f g hr
      · have hu := hf.resolve_left hr
        let := (h Z (by obtain ⟨u⟩ := hu; exact ⟨g ≫ u⟩)).some
        exact Subsingleton.elim _ _
    obtain ⟨t, ht, huniq⟩ := hP (R ⊔ openSieve U V) hR y hy
    refine ⟨t, ?_, ?_⟩
    · intro W f hf
      exact (ht f (Or.inl hf)).trans (hyR f hf)
    · intro s hs
      apply huniq s
      intro W f hf
      by_cases hr : R f
      · exact (hs f hr).trans (hyR f hr).symm
      · let := (h W (hf.resolve_left hr)).some
        exact Subsingleton.elim _ _

private lemma complement_projection_iff {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) [J.Subcanonical] (U : C) (G : Sheaf J (Type w)) :
    IsIso (prod.fst : J.yoneda.obj U ⨯ G ⟶ J.yoneda.obj U) ↔
      ∀ (W : C), Nonempty (W ⟶ U) → Nonempty (Unique (G.obj.obj (.op W))) := by
  classical
  let F := J.yoneda.obj U
  let p : F ⨯ G ⟶ F := prod.fst
  constructor
  · intro hp W ⟨u⟩
    let a : J.yoneda.obj W ⟶ F := J.yoneda.map u
    let b : J.yoneda.obj W ⟶ G := a ≫ inv p ≫ prod.snd
    refine ⟨{ default := J.yonedaEquiv b, uniq := ?_ }⟩
    intro t
    apply J.yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    have he : prod.lift a (J.yonedaEquiv.symm t) = a ≫ inv p := by
      apply (cancel_mono p).1
      simp [p]
    have he' := congrArg (fun k ↦ k ≫ (prod.snd : F ⨯ G ⟶ G)) he
    simpa only [prod.lift_snd, Category.assoc] using he'
  · intro h
    let s : F ⟶ G := ⟨{
      app := fun W ↦ ↾fun f ↦ (h W.unop ⟨f⟩).some.default
      naturality := by
        intro W Z g
        ext f
        let := (h Z.unop ⟨g.unop ≫ f⟩).some
        exact Subsingleton.elim _ _ }⟩
    refine ⟨⟨prod.lift (𝟙 _) s, ?_, ?_⟩⟩
    · apply prod.hom_ext
      · simp
      · apply Sheaf.hom_ext
        ext W z
        let u : W.unop ⟶ U := (prod.fst : F ⨯ G ⟶ F).hom.app W z
        let := (h W.unop ⟨u⟩).some
        exact Subsingleton.elim _ _
    · simp

/-- Adjoining `U ×_X V → V` to each covering test constructs the complementary closed site.
The geometric direct image is the inclusion on underlying presheaves, and its essential image
is exactly the sheaves for which the projection `h_U × G → h_U` is invertible.
No subcanonicity is asserted for the new topology.

Source: Stacks Project, Sites, Tag 08LY (`lemma-closed-subtopos`)
(blueprint: lem-trf-closed-complement-site-construction).

Proof plan, following the eight steps of the node:
1. For each V let O_V be the sieve generated by U ×_X V → V. An arrow W → V lies in it
   exactly when W maps to U. Such a map is unique because U → X is mono and X terminal.
   Thus pullback of O_V along W → V equals O_W. Define Jc by R ∪ O_V being J-covering.
2. Check the topology axioms using `def-weil-pbc-topos`: maximality and pullback stability
   are immediate. For transitivity apply J-transitivity to S ∪ O_V; on arrows in S use
   the hypothesis, and on arrows in O_V the pullback of R ∪ O_V is maximal.
3. The union sieve is generated by the original presieve and the added arrow. This gives
   exactly the asserted family rule. Since J ≤ Jc, each Jc-sheaf is a J-sheaf. The identity
   on underlying presheaves and transformations defines a fully faithful inclusion.
4. By `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`, the projection at W is
   Hom(W,U) × G(W) → Hom(W,U). Its invertibility means G(W) is a singleton whenever W
   maps to U, equivalently G(U ×_X V) is a singleton for every V. Use subcanonicity for h_U.
5. For a Jc-sheaf and W mapping to U, O_W is maximal, so the empty sieve covers W for Jc.
   Its sheaf condition makes G(W) a singleton. Step 4 proves the projection criterion.
6. Conversely, extend a matching family on a Jc-covering R to R ∪ O_V using the unique
   sections on domains mapping to U. Compatibility on the overlap is forced. Glue for J;
   any two amalgamations on R also agree on O_V by uniqueness there, hence are equal.
   This proves the exact essential image, invariant under isomorphisms.
7. Apply `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction` to the identity from
   (C,J) to (C,Jc). Its presheaf left Kan extension is the identity: the indexing category
   has (W,id) initial, hence its opposite has that object terminal. Thus the left adjoint
   is Jc-sheafification of the underlying presheaf.
8. Sectionwise finite limits and `lem-weil-pbc-sheafification-sets-exact` show that this
   left adjoint preserves finite limits. With its adjunction this is the geometric morphism
   of `def-trf-geometric-morphism`, and the direct image is the inclusion from step 3.
-/
theorem closed_complement_site_construction
    (C : Type w) [SmallCategory C] [HasFiniteLimits C]
    (J : GrothendieckTopology C) [J.Subcanonical]
    (X : C) (hX : IsTerminal X) (U : C) (i : U ⟶ X) [Mono i] :
    ∃ Jc : GrothendieckTopology C,
      (∀ (V : C) (R : Presieve V),
        Sieve.generate R ∈ Jc V ↔
          Sieve.generate (R ⊔ Presieve.singleton (pullback.snd i (hX.from V))) ∈ J V) ∧
      ∃ q : GeometricMorphism (Sheaf Jc (Type w)) (Sheaf J (Type w)),
        q.direct ⋙ sheafToPresheaf J (Type w) = sheafToPresheaf Jc (Type w) ∧
        Nonempty q.direct.FullyFaithful ∧
        ∀ G : Sheaf J (Type w),
          q.direct.essImage G ↔
            IsIso (prod.fst : J.yoneda.obj U ⨯ G ⟶ J.yoneda.obj U) := by
  classical
  let Jc := complementTopology J U
  have hle : J ≤ Jc := le_complementTopology J U
  let I : Sheaf Jc (Type w) ⥤ Sheaf J (Type w) :=
    ObjectProperty.ιOfLE (fun _ h ↦ h.of_le hle)
  let L : Sheaf J (Type w) ⥤ Sheaf Jc (Type w) :=
    sheafToPresheaf J (Type w) ⋙ presheafToSheaf Jc (Type w)
  let adj : L ⊣ I := (sheafificationAdjunction Jc (Type w)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J (Type w)) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)
  let q : GeometricMorphism (Sheaf Jc (Type w)) (Sheaf J (Type w)) :=
    { inverse := L, direct := I, adj := adj, leftExact := comp_preservesFiniteLimits _ _ }
  refine ⟨Jc, ?_, q, rfl,
    ⟨ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.of_le hle)⟩, ?_⟩
  · intro V R
    change Sieve.generate R ⊔ openSieve U V ∈ J V ↔ _
    rw [openSieve_eq_generate X hX U i V]
    rw [← Sieve.giGenerate.gc.l_sup]
  · intro G
    rw [complement_projection_iff]
    constructor
    · rintro ⟨H, ⟨e⟩⟩
      apply (complement_isSheaf_iff J U G.obj
        ((isSheaf_iff_isSheaf_of_type _ _).1 G.property)).1
      apply Presieve.isSheaf_iso Jc ((sheafToPresheaf J (Type w)).mapIso e)
      exact (isSheaf_iff_isSheaf_of_type _ _).1 H.property
    · intro h
      have hG : Presheaf.IsSheaf Jc G.obj :=
        (isSheaf_iff_isSheaf_of_type _ _).2
          ((complement_isSheaf_iff J U G.obj
            ((isSheaf_iff_isSheaf_of_type _ _).1 G.property)).2 h)
      exact ⟨⟨G.obj, hG⟩, ⟨Iso.refl _⟩⟩

end CategoryTheory
