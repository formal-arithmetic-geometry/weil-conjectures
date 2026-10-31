/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Small sheaf coproducts and their local labels

Source: Stacks Project, Sites, Tags 00WI, 00WK, 00WB and 00WH
(blueprint: lem-trf-small-sheaf-coproduct-labels).

## Main definitions

* `CategoryTheory.sheafCoproductLabelPresheaf`: the pointwise labelled disjoint sum.

## Main statements

* `CategoryTheory.small_sheaf_coproduct_labels`: sheafification is the coproduct,
  its summands are monic, sections locally have labels, and the empty-cover criteria hold.
-/

@[expose] public section

universe u v w

open Opposite CategoryTheory.Limits

namespace CategoryTheory

/-- The presheaf of labelled sections, with restrictions preserving the label.
Source: Stacks Project, Sites, Tag 00WI, discrete-diagram specialization
(blueprint: lem-trf-small-sheaf-coproduct-labels). -/
def sheafCoproductLabelPresheaf {D : Type u} [Category.{v} D] {I : Type w}
    (G : I → Dᵒᵖ ⥤ Type (max u v w)) : Dᵒᵖ ⥤ Type (max u v w) where
  obj V := Σ i : I, (G i).obj V
  map f := ↾fun s ↦ ⟨s.1, (G s.1).map f s.2⟩
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro s
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    simp

-- Covering sieves contain actual covers under the recorded covering-presieve axioms.
private theorem label_covering_refinement
    {D : Type u} [Category.{v} D] (J : Precoverage D) (hJ : J.IsSiteForCoverings)
    {V : D} {S : Sieve V} (hS : S ∈ J.toGrothendieck V) :
    ∃ T ∈ J V, T ≤ S.arrows := by
  classical
  have : J.HasIsos := hJ.1
  induction hS with
  | of X R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top X =>
    exact ⟨Presieve.singleton (𝟙 X), J.mem_coverings_of_isIso (𝟙 X), by simp⟩
  | pullback X S hS Y f ih =>
    obtain ⟨R, hR, hle⟩ := ih
    let I := Σ Z : D, {a : Z ⟶ X // R a}
    let V : I → D := fun i ↦ i.1
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
    have hh : ∀ (Y : D) (f : Y ⟶ X) (_ : R f),
        ∃ Q ∈ J Y, Q ≤ (T.pullback f).arrows := by
      intro Y f hf
      exact ihT (hle _ _ hf)
    choose Q hQ hQT using hh
    refine ⟨R.bind (fun {Y f} hf ↦ Q Y f hf),
      hJ.2.1 X R (fun {Y} f hf ↦ Q Y f hf) hR hQ, ?_⟩
    intro Z f hf
    obtain ⟨Y, g, a, ha, hg, rfl⟩ := hf
    exact hQT Y a ha _ _ hg

-- The concrete plus API works in any universe containing both site universes.
private theorem label_toPlus_injective
    {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
    (P : Dᵒᵖ ⥤ Type (max u v w)) :
    Presheaf.IsLocallyInjective K (K.toPlus P) := by
  open GrothendieckTopology.Plus in
    refine ⟨?_⟩
    intro X x y h
    rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact K.superset_covering
      (fun Y f hf ↦ congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

private theorem label_toPlus_surjective
    {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
    (P : Dᵒᵖ ⥤ Type (max u v w)) :
    Presheaf.IsLocallySurjective K (K.toPlus P) := by
  open GrothendieckTopology.Plus in
    refine ⟨?_⟩
    intro X x
    obtain ⟨S, x, rfl⟩ := exists_rep x
    refine K.superset_covering (fun Y f hf ↦ ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using!
      x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. }

/-- A small labelled sum sheafifies to the coproduct, with sectionwise injective
and monic inclusions, local labels, and the exact empty-cover behavior.
Source: Stacks Project, Sites, Tags 00WI, 00WK, 00WB and 00WH
(blueprint: lem-trf-small-sheaf-coproduct-labels).

Proof:
1. The labelled sums are small sets, and the restrictions in
   `sheafCoproductLabelPresheaf` preserve labels. Apply the double-plus theorem
   `lem-weil-pbc-sheafification-plus-theorem` to obtain a sheaf C and its universal
   map eta. Define c_i by composing the label-i inclusion with eta.
2. A family G_i -> H uniquely defines a presheaf map P -> H, by its value on each
   pair (i,s). The sheafification universal property
   `def-weil-pbc-sheafification` extends it uniquely to C -> H. This proves the
   specified Hom bijection and the coproduct property
   `def-weil-pbc-category-colimit`, also for an empty index type.
3. Apply `lem-weil-pbc-site-sheafification-sections-local` to a section of C and
   write each local representative as a pair (i,s). This gives the covering
   presieve and local labels in the statement.
4. If two sections in one summand have the same image, local equality from that
   same node makes their restrictions equal on a cover. The separatedness of
   G_i makes them equal. Evaluate two sheaf morphisms sectionwise to deduce
   categorical cancellation, hence Mono c_i.
5. If different labels have equal images, local equality gives a cover on each
   arrow of which the labels are equal. There can be no covering arrow, so this
   is the empty covering presieve. The reindexing convention of
   `def-weil-pbc-sites-and-cohomology` identifies it with the empty family.
6. For an empty covering the two products in a sheaf equalizer diagram are
   singleton sets. The equalizer, and thus H(V), is a singleton.
7. When I is empty, every local representative would be an element of the empty
   set. Step 3 therefore forces the covering to be empty whenever C(V) has a
   section. Otherwise C(V) is empty; on an empty-covered object step 6 applies.

The site hypothesis uses the recorded covering-presieve axioms, without stronger
composition or global-pullback assumptions. All section sets and labels lie in
one universe containing both site universes. No sheafification-existence
hypothesis is imposed: eta and its universal property are conclusions. -/
theorem small_sheaf_coproduct_labels
    {D : Type u} [Category.{v} D] (J : Precoverage D)
    (hJ : J.IsSiteForCoverings) {I : Type w}
    (G : I → Sheaf J.toGrothendieck (Type (max u v w))) :
    ∃ (C : Sheaf J.toGrothendieck (Type (max u v w)))
      (eta : sheafCoproductLabelPresheaf (fun i ↦ (G i).obj) ⟶ C.obj)
      (c : ∀ i : I, G i ⟶ C),
      (∀ (i : I) (V : D) (s : (G i).obj.obj (op V)),
        (c i).hom.app (op V) s = eta.app (op V) ⟨i, s⟩) ∧
      (∀ H : Sheaf J.toGrothendieck (Type (max u v w)),
        Function.Bijective (fun f : C ⟶ H ↦ eta ≫ f.hom)) ∧
      Nonempty (IsColimit (Cofan.mk C c)) ∧
      (∀ H : Sheaf J.toGrothendieck (Type (max u v w)),
        Function.Bijective (fun f : C ⟶ H ↦ fun i : I ↦ c i ≫ f)) ∧
      (∀ (i : I) (V : D), Function.Injective ((c i).hom.app (op V))) ∧
      (∀ i : I, Mono (c i)) ∧
      (∀ (V : D) (a : C.obj.obj (op V)),
        ∃ S : Presieve V, S ∈ J V ∧
          ∀ (W : D) (f : W ⟶ V), S f →
            ∃ (i : I) (s : (G i).obj.obj (op W)),
              eta.app (op W) ⟨i, s⟩ = C.obj.map f.op a) ∧
      (∀ (V : D) (i j : I) (s : (G i).obj.obj (op V))
        (t : (G j).obj.obj (op V)), i ≠ j →
        (c i).hom.app (op V) s = (c j).hom.app (op V) t →
          (⊥ : Presieve V) ∈ J V) ∧
      (∀ (H : Sheaf J.toGrothendieck (Type (max u v w))) (V : D),
        (⊥ : Presieve V) ∈ J V →
          Nonempty (H.obj.obj (op V)) ∧ Subsingleton (H.obj.obj (op V))) ∧
      (IsEmpty I → ∀ V : D,
        ((⊥ : Presieve V) ∈ J V →
          Nonempty (C.obj.obj (op V)) ∧ Subsingleton (C.obj.obj (op V))) ∧
        ((⊥ : Presieve V) ∉ J V → IsEmpty (C.obj.obj (op V)))) := by
  classical
  let K := J.toGrothendieck
  let P := sheafCoproductLabelPresheaf (fun i ↦ (G i).obj)
  let C : Sheaf K (Type (max u v w)) := ⟨K.sheafify P, K.sheafify_isSheaf P⟩
  let eta : P ⟶ C.obj := K.toSheafify P
  have hli : Presheaf.IsLocallyInjective K eta := by
    have := label_toPlus_injective K P
    have := label_toPlus_injective K (K.plusObj P)
    dsimp [eta, GrothendieckTopology.toSheafify]
    rw [GrothendieckTopology.plusMap_toPlus]
    infer_instance
  have hls : Presheaf.IsLocallySurjective K eta := by
    have := label_toPlus_surjective K P
    have := label_toPlus_surjective K (K.plusObj P)
    dsimp [eta, GrothendieckTopology.toSheafify]
    rw [GrothendieckTopology.plusMap_toPlus]
    infer_instance
  let inc (i : I) : (G i).obj ⟶ P :=
    { app := fun V ↦ ↾fun s ↦ ⟨i, s⟩
      naturality := by intros; rfl }
  let c (i : I) : G i ⟶ C := ⟨inc i ≫ eta⟩
  have huniv : ∀ H : Sheaf K (Type (max u v w)),
      Function.Bijective (fun f : C ⟶ H ↦ eta ≫ f.hom) := by
    intro H
    constructor
    · intro a b hab
      apply Sheaf.hom_ext
      exact K.sheafify_hom_ext a.hom b.hom H.property hab
    · intro a
      exact ⟨⟨K.sheafifyLift a H.property⟩, K.toSheafify_sheafifyLift a H.property⟩
  have hfam : ∀ H : Sheaf K (Type (max u v w)),
      Function.Bijective (fun f : C ⟶ H ↦ fun i ↦ c i ≫ f) := by
    intro H
    constructor
    · intro a b hab
      apply (huniv H).1
      ext V ⟨i, s⟩
      exact congrArg (fun f : G i ⟶ H ↦ f.hom.app V s) (congrFun hab i)
    · intro a
      let b : P ⟶ H.obj :=
        { app := fun V ↦ ↾fun s ↦ (a s.1).hom.app V s.2
          naturality := by
            intro V W f
            apply ConcreteCategory.hom_ext
            intro s
            exact NatTrans.naturality_apply (a s.1).hom f s.2 }
      obtain ⟨f, hf⟩ := (huniv H).2 b
      refine ⟨f, ?_⟩
      funext i
      apply Sheaf.hom_ext
      ext V s
      exact congrArg (fun e : P ⟶ H.obj ↦ e.app V ⟨i, s⟩) hf
  have hcolim : IsColimit (Cofan.mk C c) :=
    Cofan.IsColimit.mk _
      (fun t ↦ ((hfam t.pt).2 t.inj).choose)
      (fun t i ↦ congrFun ((hfam t.pt).2 t.inj).choose_spec i)
      (fun t m hm ↦ (hfam t.pt).1
        ((funext hm).trans ((hfam t.pt).2 t.inj).choose_spec.symm))
  have hinj : ∀ (i : I) (V : D), Function.Injective ((c i).hom.app (op V)) := by
    intro i V s t hst
    obtain ⟨R, hR, hle⟩ := label_covering_refinement J hJ
      (Presheaf.equalizerSieve_mem K eta ⟨i, s⟩ ⟨i, t⟩ hst)
    have hsheaf := (isSheaf_iff_isSheaf_of_type K (G i).obj).mp (G i).property
    apply (hsheaf.isSheafFor_of_mem_precoverage hR).isSeparatedFor.ext
    intro W f hf
    exact eq_of_heq (Sigma.mk.inj (hle W f hf)).2
  have hlocal : ∀ (V : D) (a : C.obj.obj (op V)),
      ∃ S : Presieve V, S ∈ J V ∧
        ∀ (W : D) (f : W ⟶ V), S f →
          ∃ (i : I) (s : (G i).obj.obj (op W)),
            eta.app (op W) ⟨i, s⟩ = C.obj.map f.op a := by
    intro V a
    obtain ⟨R, hR, hle⟩ := label_covering_refinement J hJ
      (Presheaf.imageSieve_mem K eta a)
    refine ⟨R, hR, ?_⟩
    intro W f hf
    obtain ⟨⟨i, s⟩, hs⟩ := hle W f hf
    exact ⟨i, s, hs⟩
  have hempty : ∀ (H : Sheaf K (Type (max u v w))) (V : D),
      (⊥ : Presieve V) ∈ J V →
        Nonempty (H.obj.obj (op V)) ∧ Subsingleton (H.obj.obj (op V)) := by
    intro H V hV
    have hbot : (⊥ : Sieve V) ∈ K V := by
      simpa using J.generate_mem_toGrothendieck hV
    let h := Types.isTerminalEquivUnique _ (H.isTerminalOfBotCover V hbot)
    exact ⟨⟨h.default⟩, ⟨fun a b ↦ (h.uniq a).trans (h.uniq b).symm⟩⟩
  refine ⟨C, eta, c, (fun _ _ _ ↦ rfl), huniv, ⟨hcolim⟩, hfam, hinj,
    ?_, hlocal, ?_, hempty, ?_⟩
  · intro i
    exact Sheaf.mono_of_injective (c i) (fun V ↦ hinj i V.unop)
  · intro V i j s t hij hst
    obtain ⟨R, hR, hle⟩ := label_covering_refinement J hJ
      (Presheaf.equalizerSieve_mem K eta ⟨i, s⟩ ⟨j, t⟩ hst)
    have heq : R = ⊥ := by
      funext W f
      apply propext
      exact ⟨fun hf ↦ hij (congrArg Sigma.fst (hle W f hf)), False.elim⟩
    exact heq ▸ hR
  · intro hI V
    refine ⟨hempty C V, ?_⟩
    intro hV
    refine ⟨fun a ↦ ?_⟩
    obtain ⟨R, hR, hr⟩ := hlocal V a
    have heq : R = ⊥ := by
      funext W f
      apply propext
      constructor
      · intro hf
        obtain ⟨i, s, hs⟩ := hr W f hf
        exact hI.false i
      · exact False.elim
    exact hV (heq ▸ hR)

end CategoryTheory
