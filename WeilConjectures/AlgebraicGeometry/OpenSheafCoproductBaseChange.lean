/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.FppfSheafCoproductPartition
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Scheme base changes of a coproduct of open subfunctors

Source: Stacks Project, Spaces, Tag 02WR, first paragraph of the proof
(blueprint: lem-trf-open-sheaf-coproduct-base-change).

Representing squares and the comparison are written in presheaves. The theorem also
asserts that the lifted representables are sheaves, so these are precisely the
corresponding squares and isomorphisms of fppf sheaves. No global sheafification or
coproduct instance is assumed on this big site.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Scheme-test representability with a property, allowing larger sets of sections.
The square uses the canonical lifted Hom presheaf, not an arbitrary replacement.
Source: Stacks, Spaces, relative representable properties preceding Tag 025Y
(blueprint: lem-trf-open-sheaf-coproduct-base-change). -/
def IsRepresentableWithLift {S : Scheme.{u}}
    (P : MorphismProperty (Over S))
    {G F : (Over S)ᵒᵖ ⥤ Type (max u v)} (f : G ⟶ F) : Prop :=
  ∀ (T : Over S) (a : uliftYoneda.{v}.obj T ⟶ F),
    ∃ (U : Over S) (p : U ⟶ T) (q : uliftYoneda.{v}.obj U ⟶ G),
      IsPullback q (uliftYoneda.{v}.map p) f a ∧ P p

/-- Every scheme base change is represented by a scheme in the chosen site universe.
Source: Stacks, Spaces, relative representable properties preceding Tag 025Y
(blueprint: lem-trf-open-sheaf-coproduct-base-change). -/
def IsRepresentableLift {S : Scheme.{u}}
    {G F : (Over S)ᵒᵖ ⥤ Type (max u v)} (f : G ⟶ F) : Prop :=
  IsRepresentableWithLift ⊤ f

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.Scheme

private theorem small_coproduct_support {I : Type*} (V : I → Scheme.{u})
    (C : Scheme.{u}) (k : ∀ i, V i ⟶ C) (hc : IsColimit (Cofan.mk C k)) :
    Small.{u} {i // Nonempty (V i)} := by
  classical
  let B : Scheme.{u} := (⊤_ Scheme.{u}) ⨿ (⊤_ Scheme.{u})
  let a (i j : I) : V j ⟶ B :=
    terminal.from (V j) ≫ (if i = j then coprod.inl else coprod.inr)
  let p (i : I) : C ⟶ B := Cofan.IsColimit.desc hc (a i)
  have hp (i j : I) : k j ≫ p i = a i j := Cofan.IsColimit.fac hc (a i) j
  apply small_of_injective (f := fun i : {i // Nonempty (V i)} ↦
    k i.val (Classical.choice i.property))
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have h := congrArg (fun x ↦ p i.val x) hij
  have hi := congrArg (fun g : V i.val ⟶ B ↦ g (Classical.choice i.property)) (hp i.val i.val)
  have hj := congrArg (fun g : V j.val ⟶ B ↦ g (Classical.choice j.property)) (hp i.val j.val)
  simp only [Scheme.Hom.comp_apply] at hi hj
  rw [hi, hj] at h
  simp only [a, if_true, if_neg hne, Scheme.Hom.comp_apply] at h
  exact inl_ne_inr _ _ _ _ h

private theorem support_isColimit {I : Type*} (V : I → Scheme.{u})
    (C : Scheme.{u}) (k : ∀ i, V i ⟶ C) (hc : IsColimit (Cofan.mk C k)) :
    Nonempty (IsColimit (Cofan.mk C (fun i : {i // Nonempty (V i)} ↦ k i.val))) := by
  classical
  refine ⟨Cofan.IsColimit.mk _ (fun s ↦ Cofan.IsColimit.desc hc (fun i ↦
    if hi : Nonempty (V i) then s.inj ⟨i, hi⟩ else
      (isInitial_iff_isEmpty.mpr (not_nonempty_iff.mp hi)).some.to s.pt)) ?_ ?_⟩
  · intro s i
    change k i.val ≫ _ = _
    rw [show k i.val = (Cofan.mk C k).inj i.val from rfl, Cofan.IsColimit.fac]
    simp only [dif_pos i.property]
  · intro s m hm
    apply Cofan.IsColimit.hom_ext hc
    intro i
    rw [Cofan.IsColimit.fac]
    by_cases hi : Nonempty (V i)
    · exact hm ⟨i, hi⟩ |>.trans (by simp only [dif_pos hi])
    · rw [dif_neg hi]
      exact (isInitial_iff_isEmpty.mpr (not_nonempty_iff.mp hi)).some.hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
private theorem coproduct_geometry {I : Type*} (V : I → Scheme.{u})
    (C : Scheme.{u}) (k : ∀ i, V i ⟶ C) (hc : IsColimit (Cofan.mk C k)) :
    (∀ i, IsOpenImmersion (k i)) ∧ (∀ x : C, ∃ i y, k i y = x) ∧
    (∀ i j, i ≠ j → ∀ x y, k i x ≠ k j y) := by
  classical
  let N := {i // Nonempty (V i)}
  let : Small.{u} N := small_coproduct_support V C k hc
  let B := Shrink.{u} N
  let e : B ≃ N := (equivShrink N).symm
  let r : B → I := fun b ↦ (e b).val
  let W : B → Scheme.{u} := fun b ↦ V (r b)
  have hcN := (support_isColimit V C k hc).some
  have hcB : IsColimit (Cofan.mk C (fun b : B ↦ k (r b))) :=
    (Cofan.isColimitEquivOfEquiv e (Cofan.mk C (fun i : N ↦ k i.val))) hcN
  let E : (∐ W) ≅ C := (coproductIsCoproduct W).coconePointUniqueUpToIso hcB
  have hk (b : B) : Sigma.ι W b ≫ E.hom = k (r b) :=
    (coproductIsCoproduct W).comp_coconePointUniqueUpToIso_hom hcB ⟨b⟩
  have hop (b : B) : IsOpenImmersion (k (r b)) := by
    rw [← hk]
    infer_instance
  have hr (i : I) (hi : Nonempty (V i)) : r (e.symm ⟨i, hi⟩) = i := by
    simp [r]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : Nonempty (V i)
    · exact (hr i hi) ▸ hop (e.symm ⟨i, hi⟩)
    · let : IsEmpty (V i) := not_nonempty_iff.mp hi
      infer_instance
  · intro x
    obtain ⟨b, y, hy⟩ := (sigmaOpenCover W).exists_eq (E.inv x)
    change (Sigma.ι W b) y = E.inv x at hy
    refine ⟨r b, y, ?_⟩
    rw [← hk, Scheme.Hom.comp_apply, hy]
    exact congrArg (fun f : C ⟶ C ↦ f x) E.inv_hom_id
  · intro i j hij x y hxy
    let A : Scheme.{u} := (⊤_ Scheme.{u}) ⨿ (⊤_ Scheme.{u})
    let a (l : I) : V l ⟶ A :=
      terminal.from (V l) ≫ (if i = l then coprod.inl else coprod.inr)
    let p := Cofan.IsColimit.desc hc a
    have hi : k i ≫ p = a i := Cofan.IsColimit.fac hc a i
    have hj : k j ≫ p = a j := Cofan.IsColimit.fac hc a j
    have he := congrArg (fun z ↦ p z) hxy
    have hi' := congrArg (fun g : V i ⟶ A ↦ g x) hi
    have hj' := congrArg (fun g : V j ⟶ A ↦ g y) hj
    simp only [Scheme.Hom.comp_apply] at hi' hj'
    have he := hi'.symm.trans (he.trans hj')
    simp only [a, if_true, if_neg hij, Scheme.Hom.comp_apply] at he
    exact inl_ne_inr _ _ _ _ he

private theorem empty_bot_cover {S : Scheme.{u}} (W : Over S) [IsEmpty W.left] :
    ⊥ ∈ (fppfTopology.over S) W := by
  rw [fppfTopology.mem_over_iff]
  simp only [map_bot]
  exact bot_mem_grothendieckTopology _

private theorem coproduct_cover {S : Scheme.{u}} {I : Type*} (V : I → Over S)
    (C : Over S) (k : ∀ i, V i ⟶ C)
    (hc : IsColimit (Cofan.mk C.left (fun i ↦ (k i).left))) :
    Sieve.ofArrows V k ∈ (fppfTopology.over S) C := by
  have hg := coproduct_geometry (fun i ↦ (V i).left) C.left (fun i ↦ (k i).left) hc
  rw [fppfTopology.mem_over_iff, Sieve.ofArrows, Sieve.overEquiv_generate,
    ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
    Presieve.map_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  apply zariskiPrecoverage_le_fppfPrecoverage
  exact (ofArrows_mem_precoverage_iff _).mpr ⟨hg.2.1, hg.1⟩

set_option backward.isDefEq.respectTransparency false in
private theorem sheaf_coproduct_sections {S : Scheme.{u}} {I : Type*}
    (V : I → Over S) (C : Over S) (k : ∀ i, V i ⟶ C)
    (hc : IsColimit (Cofan.mk C.left (fun i ↦ (k i).left)))
    (K : Sheaf (fppfTopology.over S) (Type (max u v)))
    (a : ∀ i, K.obj.obj (op (V i))) :
    ∃! b : K.obj.obj (op C), ∀ i, K.obj.map (k i).op b = a i := by
  have hg := coproduct_geometry (fun i ↦ (V i).left) C.left (fun i ↦ (k i).left) hc
  have hs := (isSheaf_iff_isSheaf_of_type _ _).mp K.property
  apply (Presieve.isSheafFor_arrows_iff _ _).mp
    (hs.isSheafFor _ (coproduct_cover V C k hc)) a
  intro i j W f g hfg
  by_cases hij : i = j
  · subst j
    have : IsOpenImmersion (k i).left := hg.1 i
    have he : f = g := by
      apply Over.OverMorphism.ext
      exact (cancel_mono (k i).left).mp (congrArg (fun h ↦ h.left) hfg)
    rw [he]
  · have : IsEmpty W.left := ⟨fun x ↦ hg.2.2 i j hij (f.left x) (g.left x)
      (congrArg (fun h : W ⟶ C ↦ h.left x) hfg)⟩
    let := Types.isTerminalEquivUnique _ (K.isTerminalOfBotCover W (empty_bot_cover W))
    exact Subsingleton.elim _ _

private theorem representable_isSheaf {S : Scheme.{u}} (X : Over S) :
    Presheaf.IsSheaf (fppfTopology.over S) (uliftYoneda.{v}.obj X) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

set_option backward.isDefEq.respectTransparency false in
private theorem representable_coproduct {S : Scheme.{u}} {I : Type*}
    (V : I → Over S) (C : Over S) (k : ∀ i, V i ⟶ C)
    (hc : IsColimit (Cofan.mk C.left (fun i ↦ (k i).left))) :
    Nonempty (IsColimit (Cofan.mk
      ((fppfTopology.over S).uliftYoneda.{v}.obj C)
      (fun i ↦ (fppfTopology.over S).uliftYoneda.{v}.map (k i)))) := by
  classical
  let Y := (fppfTopology.over S).uliftYoneda.{v}
  have h (s : Cofan (fun i ↦ Y.obj (V i))) :
      ∃! b : (Y.obj C ⟶ s.pt), ∀ i, Y.map (k i) ≫ b = s.inj i := by
    obtain ⟨a, ha, hu⟩ := sheaf_coproduct_sections V C k hc s.pt
      (fun i ↦ uliftYonedaEquiv.{v} (s.inj i).hom)
    refine ⟨⟨uliftYonedaEquiv.{v}.symm a⟩, ?_, ?_⟩
    · intro i
      apply Sheaf.hom_ext
      apply uliftYonedaEquiv.{v}.injective
      change uliftYonedaEquiv (uliftYoneda.map (k i) ≫
        uliftYonedaEquiv.symm a) = _
      exact (uliftYonedaEquiv_naturality
        (uliftYonedaEquiv.{v}.symm a) (k i).op).symm.trans (by simpa using ha i)
    · intro b hb
      apply Sheaf.hom_ext
      apply uliftYonedaEquiv.{v}.injective
      simpa only [Equiv.apply_symm_apply] using hu (uliftYonedaEquiv.{v} b.hom) (fun i ↦ by
        rw [uliftYonedaEquiv_naturality]
        exact congrArg (fun g ↦ uliftYonedaEquiv.{v} g.hom) (hb i))
  exact ⟨Cofan.IsColimit.mk _ (fun s ↦ (h s).choose)
    (fun s i ↦ (h s).choose_spec.1 i) (fun s b hb ↦ (h s).choose_spec.2 b hb)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem coproduct_partition {S : Scheme.{u}} {I : Type (max u v)}
    (G : I → Sheaf (fppfTopology.over S) (Type (max u v)))
    (V : I → Over S) (C : Over S) (k : ∀ i, V i ⟶ C)
    (hc : IsColimit (Cofan.mk C.left (fun i ↦ (k i).left)))
    (s : ∀ i, uliftYoneda.{v}.obj (V i) ⟶ (G i).obj) :
    ∃ (d : FppfCoproductPartition G C)
      (e : ∀ i, V i ≅ fppfPartitionOpen C (d.opens i)),
      (∀ i, (e i).hom ≫ fppfPartitionInclusion C (d.opens i) = k i) ∧
      (∀ i, uliftYoneda.{v}.map (e i).hom ≫
        uliftYonedaEquiv.{v}.symm (d.sections i) = s i) := by
  classical
  have hg := coproduct_geometry (fun i ↦ (V i).left) C.left (fun i ↦ (k i).left) hc
  have (i : I) : IsOpenImmersion (k i).left := hg.1 i
  let U (i : I) : C.left.Opens := (k i).left.opensRange
  let E (i : I) : V i ≅ fppfPartitionOpen C (U i) :=
    Over.isoMk (IsOpenImmersion.isoOfRangeEq (k i).left (U i).ι
      (by exact (Opens.range_ι (U i)).symm)) (by
        change _ ≫ (U i).ι ≫ C.hom = (V i).hom
        rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Over.w])
  have hE (i : I) : (E i).hom ≫ fppfPartitionInclusion C (U i) = k i := by
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _
      (by exact (Opens.range_ι (U i)).symm)
  have hclosed (i : I) : IsClosed (U i : Set C.left) := by
    have he : (U i : Set C.left)ᶜ = ⋃ j : {j // j ≠ i}, (U j.val : Set C.left) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨j, y, rfl⟩ := hg.2.1 x
        refine ⟨⟨j, fun h ↦ hx (h ▸ ⟨y, rfl⟩)⟩, y, rfl⟩
      · rintro ⟨j, y, rfl⟩ ⟨z, hz⟩
        exact hg.2.2 i j.val (Ne.symm j.property) z y hz
    exact isOpen_compl_iff.mp (he ▸ isOpen_iUnion (fun j ↦ (U j.val).isOpen))
  let d : FppfCoproductPartition G C :=
    { opens := U
      isClosed := hclosed
      disjoint := fun i j hij ↦ by
        apply disjoint_iff.mpr
        apply le_bot_iff.mp
        intro x hx
        obtain ⟨y, hy⟩ := hx.1
        obtain ⟨z, hz⟩ := hx.2
        exact hg.2.2 i j hij y z (hy.trans hz.symm)
      covers := by
        apply TopologicalSpace.Opens.ext
        ext x
        simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion,
          TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
        obtain ⟨i, y, rfl⟩ := hg.2.1 x
        exact ⟨i, y, rfl⟩
      sections := fun i ↦ (G i).obj.map (E i).inv.op (uliftYonedaEquiv.{v} (s i)) }
  refine ⟨d, E, hE, ?_⟩
  intro i
  dsimp [d]
  rw [uliftYonedaEquiv_symm_map (E i).inv.op]
  simp only [Quiver.Hom.unop_op, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    Equiv.symm_apply_apply]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem coproduct_hom_ext {S : Scheme.{u}} {I : Type*}
    (V : I → Over S) (C : Over S) (k : ∀ i, V i ⟶ C)
    (hc : IsColimit (Cofan.mk C.left (fun i ↦ (k i).left)))
    (K : Sheaf (fppfTopology.over S) (Type (max u v)))
    {a b : uliftYoneda.{v}.obj C ⟶ K.obj}
    (h : ∀ i, uliftYoneda.{v}.map (k i) ≫ a = uliftYoneda.{v}.map (k i) ≫ b) :
    a = b := by
  have hh := (representable_coproduct V C k hc).some
  exact congrArg (fun f ↦ f.hom) (Cofan.IsColimit.hom_ext hh
    (show (fppfTopology.over S).uliftYoneda.{v}.obj C ⟶ K from ⟨a⟩)
    (show (fppfTopology.over S).uliftYoneda.{v}.obj C ⟶ K from ⟨b⟩)
    (fun i ↦ Sheaf.hom_ext (h i)))

set_option backward.isDefEq.respectTransparency false in
private theorem coproduct_over {S : Scheme.{u}} {I : Type*}
    (V : I → Over S) (C : Over S) (k : ∀ i, V i ⟶ C)
    (hc : IsColimit (Cofan.mk C.left (fun i ↦ (k i).left))) :
    Nonempty (IsColimit (Cofan.mk C k)) := by
  refine ⟨Cofan.IsColimit.mk _ (fun s ↦ Over.homMk
    (Cofan.IsColimit.desc hc (fun i ↦ (s.inj i).left)) ?_) ?_ ?_⟩
  · apply Cofan.IsColimit.hom_ext hc
    intro i
    rw [Cofan.IsColimit.fac_assoc]
    exact (Over.w (s.inj i)).trans (Over.w (k i)).symm
  · intro s i
    apply Over.OverMorphism.ext
    exact Cofan.IsColimit.fac hc _ i
  · intro s m hm
    apply Over.OverMorphism.ext
    apply Cofan.IsColimit.hom_ext hc
    intro i
    change (k i).left ≫ m.left = (k i).left ≫ Cofan.IsColimit.desc hc _
    exact (congrArg Over.Hom.left (hm i)).trans
      (Cofan.IsColimit.fac hc (fun i ↦ (s.inj i).left) i).symm

/-- The specified open scheme base changes and their scheme coproduct in the site.
The projection `p` is characterized by its restrictions to the coproduct summands.
Source: Stacks, Spaces, Tag 02WR, first proof paragraph
(blueprint: lem-trf-open-sheaf-coproduct-base-change). -/
structure OpenSheafCoproductTest {S : Scheme.{u}} {I : Type (max u v)}
    {F : Sheaf (fppfTopology.over S) (Type (max u v))}
    (Fi : I → Sheaf (fppfTopology.over S) (Type (max u v)))
    (ι : ∀ i, Fi i ⟶ F) (T : Over S) (t : uliftYoneda.{v}.obj T ⟶ F.obj) where
  /-- The schemes representing the open pullbacks. -/
  V : I → Over S
  /-- Their projections to the test scheme. -/
  inclusion : ∀ i, V i ⟶ T
  /-- Their universal component sections. -/
  sectionMap : ∀ i, uliftYoneda.{v}.obj (V i) ⟶ (Fi i).obj
  /-- These are the specified representing squares. -/
  cartesian : ∀ i, IsPullback (sectionMap i)
    (uliftYoneda.{v}.map (inclusion i)) (ι i).hom t
  /-- The representing projections are open immersions. -/
  isOpen : ∀ i, IsOpenImmersion (inclusion i).left
  /-- The coproduct lies in the chosen category of schemes. -/
  C : Over S
  /-- Its summand injections over the base scheme. -/
  injection : ∀ i, V i ⟶ C
  /-- Its scheme coproduct universal property. -/
  isColimit : IsColimit (Cofan.mk C.left (fun i ↦ (injection i).left))
  /-- The induced projection of the coproduct. -/
  p : C ⟶ T
  /-- It restricts to the given inclusion on each summand. -/
  injection_p : ∀ i, injection i ≫ p = inclusion i

/-- Equations characterizing the canonical comparison, including its projection to `T`.
Source: Stacks, Spaces, Tag 02WR, first proof paragraph
(blueprint: lem-trf-open-sheaf-coproduct-base-change). -/
def OpenSheafCoproductTest.ComparisonEquations
    {S : Scheme.{u}} {I : Type (max u v)}
    {F : Sheaf (fppfTopology.over S) (Type (max u v))}
    {Fi : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {ι : ∀ i, Fi i ⟶ F}
    {H : Sheaf (fppfTopology.over S) (Type (max u v))}
    (j : ∀ i, Fi i ⟶ H) (q : H ⟶ F)
    {T : Over S} {t : uliftYoneda.{v}.obj T ⟶ F.obj}
    (D : OpenSheafCoproductTest Fi ι T t)
    (e : uliftYoneda.{v}.obj D.C ≅ pullback q.hom t) : Prop :=
  (∀ i, uliftYoneda.{v}.map (D.injection i) ≫ e.hom ≫ pullback.fst q.hom t =
    D.sectionMap i ≫ (j i).hom) ∧
  e.hom ≫ pullback.snd q.hom t = uliftYoneda.{v}.map D.p

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_section {S : Scheme.{u}} {I : Type (max u v)}
    {F : Sheaf (fppfTopology.over S) (Type (max u v))}
    {Fi : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {ι : ∀ i, Fi i ⟶ F}
    (H : Sheaf (fppfTopology.over S) (Type (max u v)))
    (j : ∀ i, Fi i ⟶ H) (hcol : IsColimit (Cofan.mk H j))
    {T : Over S} {t : uliftYoneda.{v}.obj T ⟶ F.obj}
    (D : OpenSheafCoproductTest Fi ι T t) :
    ∃ a : uliftYoneda.{v}.obj D.C ⟶ H.obj,
      (∀ i, uliftYoneda.{v}.map (D.injection i) ≫ a = D.sectionMap i ≫ (j i).hom) ∧
      (∀ i, IsPullback (D.sectionMap i) (uliftYoneda.{v}.map (D.injection i))
        (j i).hom a) := by
  classical
  obtain ⟨d, E, hE, hs⟩ := coproduct_partition Fi D.V D.C D.injection D.isColimit D.sectionMap
  obtain ⟨a, ha, -⟩ := (fppfSheaf_coproduct_partition Fi).2 H j hcol |>.2.2.2.1 D.C d
  have heq (i : I) : uliftYoneda.{v}.map (fppfPartitionInclusion D.C (d.opens i)) ≫
      uliftYonedaEquiv.{v}.symm a = uliftYonedaEquiv.{v}.symm (d.sections i) ≫
        (j i).hom := by
    exact (uliftYonedaEquiv_symm_map
      (fppfPartitionInclusion D.C (d.opens i)).op a).symm.trans
      ((congrArg (fun x ↦ uliftYonedaEquiv.{v}.symm x) (ha i).symm).trans
        (uliftYonedaEquiv_symm_comp (d.sections i) (j i).hom).symm)
  refine ⟨uliftYonedaEquiv.{v}.symm a, ?_, ?_⟩
  · intro i
    rw [← hE i, Functor.map_comp, Category.assoc, heq, ← Category.assoc, hs i]
  · intro i
    have hp := ((fppfSheaf_coproduct_partition Fi).2 H j hcol).2.2.1 D.C a d ha |>.2.1 i
    exact hp.flip.of_iso' (uliftYoneda.{v}.mapIso (E i)) (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simpa using hs i)
      (by simpa using congrArg (fun f ↦ uliftYoneda.{v}.map f) (hE i))
      (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
private theorem partition_cartesian {S : Scheme.{u}} {I : Type (max u v)}
    {Fi : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {H : Sheaf (fppfTopology.over S) (Type (max u v))}
    (j : ∀ i, Fi i ⟶ H) (hcol : IsColimit (Cofan.mk H j))
    (W : Over S) (x : uliftYoneda.{v}.obj W ⟶ H.obj) :
    ∃ (Z : I → Over S) (k : ∀ i, Z i ⟶ W)
      (s : ∀ i, uliftYoneda.{v}.obj (Z i) ⟶ (Fi i).obj),
      Nonempty (IsColimit (Cofan.mk W.left (fun i ↦ (k i).left))) ∧
      ∀ i, IsPullback (s i) (uliftYoneda.{v}.map (k i)) (j i).hom x := by
  obtain ⟨d, hd, -⟩ := ((fppfSheaf_coproduct_partition Fi).2 H j hcol).2.1
    W (uliftYonedaEquiv.{v} x)
  have hp := ((fppfSheaf_coproduct_partition Fi).2 H j hcol).2.2.1
    W (uliftYonedaEquiv.{v} x) d hd
  refine ⟨(fun i ↦ fppfPartitionOpen W (d.opens i)),
    (fun i ↦ fppfPartitionInclusion W (d.opens i)),
    (fun i ↦ uliftYonedaEquiv.{v}.symm (d.sections i)), hp.1, ?_⟩
  intro i
  simpa only [Equiv.symm_apply_apply] using (hp.2.1 i).flip

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_lift {S : Scheme.{u}} {I : Type (max u v)}
    {F : Sheaf (fppfTopology.over S) (Type (max u v))}
    {Fi : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {ι : ∀ i, Fi i ⟶ F}
    (H : Sheaf (fppfTopology.over S) (Type (max u v)))
    (j : ∀ i, Fi i ⟶ H) (hcol : IsColimit (Cofan.mk H j))
    (q : H ⟶ F) (hfac : ∀ i, j i ≫ q = ι i)
    {T : Over S} {t : uliftYoneda.{v}.obj T ⟶ F.obj}
    (D : OpenSheafCoproductTest Fi ι T t)
    (a : uliftYoneda.{v}.obj D.C ⟶ H.obj)
    (ha : ∀ i, uliftYoneda.{v}.map (D.injection i) ≫ a = D.sectionMap i ≫ (j i).hom)
    (hp : ∀ i, IsPullback (D.sectionMap i) (uliftYoneda.{v}.map (D.injection i))
      (j i).hom a)
    (W : Over S) (x : uliftYoneda.{v}.obj W ⟶ H.obj) (b : W ⟶ T)
    (hw : x ≫ q.hom = uliftYoneda.{v}.map b ≫ t) :
    ∃! g : W ⟶ D.C, uliftYoneda.{v}.map g ≫ a = x ∧ g ≫ D.p = b := by
  classical
  obtain ⟨Z, k, s, hZ, hs⟩ := partition_cartesian j hcol W x
  let hZ' := (coproduct_over Z W k hZ.some).some
  have he (i : I) : s i ≫ (ι i).hom = uliftYoneda.{v}.map (k i ≫ b) ≫ t := by
    rw [← hfac i]
    change s i ≫ ((j i).hom ≫ q.hom) = _
    rw [← Category.assoc, (hs i).w, Category.assoc, hw, ← Functor.map_comp_assoc]
  let di (i : I) : Z i ⟶ D.V i := uliftYoneda.{v}.preimage
    ((D.cartesian i).lift (s i) (uliftYoneda.{v}.map (k i ≫ b)) (he i))
  have hdi (i : I) : uliftYoneda.{v}.map (di i) ≫ D.sectionMap i = s i := by
    simp only [di, Functor.map_preimage, IsPullback.lift_fst]
  have hdp (i : I) : di i ≫ D.inclusion i = k i ≫ b := by
    apply uliftYoneda.{v}.map_injective
    simp only [Functor.map_comp, di, Functor.map_preimage, IsPullback.lift_snd]
  let g : W ⟶ D.C := Cofan.IsColimit.desc hZ' (fun i ↦ di i ≫ D.injection i)
  have hg (i : I) : k i ≫ g = di i ≫ D.injection i := Cofan.IsColimit.fac hZ' _ i
  have hga : uliftYoneda.{v}.map g ≫ a = x := by
    apply coproduct_hom_ext Z W k hZ.some H
    intro i
    rw [← Functor.map_comp_assoc, hg, Functor.map_comp, Category.assoc, ha,
      ← Category.assoc, hdi, (hs i).w]
  have hgp : g ≫ D.p = b := by
    apply Cofan.IsColimit.hom_ext hZ'
    intro i
    change k i ≫ g ≫ D.p = k i ≫ b
    rw [← Category.assoc, hg, Category.assoc, D.injection_p, hdp]
  refine ⟨g, ⟨hga, hgp⟩, ?_⟩
  intro g' hg'
  apply Cofan.IsColimit.hom_ext hZ'
  intro i
  have hw' : s i ≫ (j i).hom = uliftYoneda.{v}.map (k i ≫ g') ≫ a := by
    rw [(hs i).w, Functor.map_comp, Category.assoc, hg'.1]
  let li := (hp i).lift (s i) (uliftYoneda.{v}.map (k i ≫ g')) hw'
  have hl : li = uliftYoneda.{v}.map (di i) := by
    apply (D.cartesian i).hom_ext
    · simp only [li, IsPullback.lift_fst, hdi]
    · calc
        li ≫ uliftYoneda.{v}.map (D.inclusion i) =
            li ≫ uliftYoneda.{v}.map (D.injection i) ≫
              uliftYoneda.{v}.map D.p := by
                rw [← Functor.map_comp, D.injection_p]
        _ = uliftYoneda.{v}.map (k i ≫ b) := by
          rw [IsPullback.lift_snd_assoc, ← Functor.map_comp, Category.assoc, hg'.2]
        _ = uliftYoneda.{v}.map (di i) ≫ uliftYoneda.{v}.map (D.inclusion i) := by
          rw [← Functor.map_comp, hdp]
  change k i ≫ g' = k i ≫ g
  apply uliftYoneda.{v}.map_injective
  rw [hg]
  exact ((hp i).lift_snd (s i) (uliftYoneda.{v}.map (k i ≫ g')) hw').symm.trans
    ((congrArg (fun l ↦ l ≫ uliftYoneda.{v}.map (D.injection i)) hl).trans
      (uliftYoneda.{v}.map_comp (di i) (D.injection i)).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_of_test_lifts {S : Scheme.{u}}
    {P A B F : (Over S)ᵒᵖ ⥤ Type (max u v)}
    (a : P ⟶ A) (b : P ⟶ B) (f : A ⟶ F) (g : B ⟶ F)
    (w : a ≫ f = b ≫ g)
    (h : ∀ (W : Over S) (x : uliftYoneda.{v}.obj W ⟶ A)
      (y : uliftYoneda.{v}.obj W ⟶ B), x ≫ f = y ≫ g →
      ∃! z : uliftYoneda.{v}.obj W ⟶ P, z ≫ a = x ∧ z ≫ b = y) :
    IsPullback a b f g := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨congrArg (fun k ↦ k.app W) w, ?_, ?_⟩
  · intro z z' hz
    let x := uliftYonedaEquiv.{v}.symm (a.app W z)
    let y := uliftYonedaEquiv.{v}.symm (b.app W z)
    have hxy : x ≫ f = y ≫ g := by
      dsimp only [x, y]
      rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp]
      exact congrArg (fun k ↦ uliftYonedaEquiv.{v}.symm (k.app W z)) w
    obtain ⟨l, hl, hu⟩ := h W.unop x y hxy
    have h₁ : uliftYonedaEquiv.{v}.symm z = l := hu _ (by
      simp only [uliftYonedaEquiv_symm_comp, x, y, and_self])
    have h₂ : uliftYonedaEquiv.{v}.symm z' = l := hu _ (by
      simp only [uliftYonedaEquiv_symm_comp, x, y, hz.1, hz.2, and_self])
    exact uliftYonedaEquiv.{v}.symm.injective (h₁.trans h₂.symm)
  · intro x y hxy
    obtain ⟨z, hz, -⟩ := h W.unop (uliftYonedaEquiv.{v}.symm x)
      (uliftYonedaEquiv.{v}.symm y) (by
        simp only [uliftYonedaEquiv_symm_comp, hxy])
    refine ⟨uliftYonedaEquiv.{v} z, ?_, ?_⟩
    · simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply] using
        congrArg (fun k ↦ uliftYonedaEquiv.{v} k) hz.1
    · simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply] using
        congrArg (fun k ↦ uliftYonedaEquiv.{v} k) hz.2

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_cartesian {S : Scheme.{u}} {I : Type (max u v)}
    {F : Sheaf (fppfTopology.over S) (Type (max u v))}
    {Fi : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {ι : ∀ i, Fi i ⟶ F}
    (H : Sheaf (fppfTopology.over S) (Type (max u v)))
    (j : ∀ i, Fi i ⟶ H) (hcol : IsColimit (Cofan.mk H j))
    (q : H ⟶ F) (hfac : ∀ i, j i ≫ q = ι i)
    {T : Over S} {t : uliftYoneda.{v}.obj T ⟶ F.obj}
    (D : OpenSheafCoproductTest Fi ι T t) :
    ∃ a : uliftYoneda.{v}.obj D.C ⟶ H.obj,
      (∀ i, uliftYoneda.{v}.map (D.injection i) ≫ a = D.sectionMap i ≫ (j i).hom) ∧
      IsPullback a (uliftYoneda.{v}.map D.p) q.hom t := by
  obtain ⟨a, ha, hp⟩ := comparison_section H j hcol D
  have hw : a ≫ q.hom = uliftYoneda.{v}.map D.p ≫ t := by
    apply coproduct_hom_ext D.V D.C D.injection D.isColimit F
    intro i
    rw [← Category.assoc, ha, Category.assoc]
    change D.sectionMap i ≫ (j i ≫ q).hom = _
    rw [hfac, (D.cartesian i).w, ← Functor.map_comp_assoc, D.injection_p]
  refine ⟨a, ha, pullback_of_test_lifts a (uliftYoneda.{v}.map D.p) q.hom t hw ?_⟩
  intro W x y hxy
  let b : W ⟶ T := uliftYoneda.{v}.preimage y
  have hb : uliftYoneda.{v}.map b = y := Functor.map_preimage _ _
  obtain ⟨g, hg, hu⟩ := comparison_lift H j hcol q hfac D a ha hp W x b (by
    rw [hb]; exact hxy)
  refine ⟨uliftYoneda.{v}.map g, ⟨hg.1, ?_⟩, ?_⟩
  · rw [← Functor.map_comp, hg.2, hb]
  · intro z hz
    let l : W ⟶ D.C := uliftYoneda.{v}.preimage z
    have hl : uliftYoneda.{v}.map l = z := Functor.map_preimage _ _
    have he : l = g := hu l ⟨by rw [hl]; exact hz.1, by
      apply uliftYoneda.{v}.map_injective
      rw [Functor.map_comp, hl, hz.2, hb]⟩
    rw [← hl, he]

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_iso {S : Scheme.{u}} {I : Type (max u v)}
    {F : Sheaf (fppfTopology.over S) (Type (max u v))}
    {Fi : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {ι : ∀ i, Fi i ⟶ F}
    (H : Sheaf (fppfTopology.over S) (Type (max u v)))
    (j : ∀ i, Fi i ⟶ H) (hcol : IsColimit (Cofan.mk H j))
    (q : H ⟶ F) (hfac : ∀ i, j i ≫ q = ι i)
    {T : Over S} {t : uliftYoneda.{v}.obj T ⟶ F.obj}
    (D : OpenSheafCoproductTest Fi ι T t) :
    ∃! e : uliftYoneda.{v}.obj D.C ≅ pullback q.hom t,
      D.ComparisonEquations j q e := by
  obtain ⟨a, ha, hp⟩ := comparison_cartesian H j hcol q hfac D
  refine ⟨hp.isoPullback, ⟨?_, hp.isoPullback_hom_snd⟩, ?_⟩
  · intro i
    rw [hp.isoPullback_hom_fst]
    exact ha i
  · intro e he
    apply Iso.ext
    apply pullback.hom_ext
    · apply coproduct_hom_ext D.V D.C D.injection D.isColimit H
      intro i
      rw [hp.isoPullback_hom_fst]
      exact (he.1 i).trans (ha i).symm
    · exact he.2.trans hp.isoPullback_hom_snd.symm

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_isPullback {S : Scheme.{u}} {I : Type (max u v)}
    {F : Sheaf (fppfTopology.over S) (Type (max u v))}
    {Fi : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {ι : ∀ i, Fi i ⟶ F}
    {H : Sheaf (fppfTopology.over S) (Type (max u v))}
    (j : ∀ i, Fi i ⟶ H) (q : H ⟶ F)
    {T : Over S} {t : uliftYoneda.{v}.obj T ⟶ F.obj}
    (D : OpenSheafCoproductTest Fi ι T t)
    (e : uliftYoneda.{v}.obj D.C ≅ pullback q.hom t)
    (he : D.ComparisonEquations j q e) :
    IsPullback (e.hom ≫ pullback.fst q.hom t) (uliftYoneda.{v}.map D.p) q.hom t := by
  exact (IsPullback.of_hasPullback q.hom t).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using he.2) (by simp) (by simp)

-- The chosen test data already supply the global openness assumptions locally.
set_option linter.unusedVariables false in
/-- The sheaf coproduct of representable open subfunctors has scheme base changes
represented by their scheme coproducts, with the canonical summand maps, over the test
scheme and compatibly with every change of test. The explicit existence hypothesis
on `OpenSheafCoproductTest` expresses that these scheme coproducts lie in the chosen site.
Source: Stacks, Spaces, Tag 02WR, first paragraph of the proof
(blueprint: lem-trf-open-sheaf-coproduct-base-change).

Proof:
1. An fppf cover is fpqc (lem-trf-fppf-covering-is-fpqc). Apply fpqc representable
   descent (lem-weil-pbc-fpqc-representable-descent), and apply its uniqueness again
   with target S to check that the descended map is over S. Thus all h_X are sheaves.
2. The scheme coproduct has clopen summands (lem-weil-pbc-scheme-coproduct-family).
   Glue the universal sections into H using lem-trf-fppf-sheaf-coproduct-partition.
   On each summand their images under q equal t(p); the summands are an fppf cover
   (lem-pc-zariski-coverings-are-fppf), so equality holds globally. Pulling this pair
   back along W → C defines the comparison.
3. Conversely, partition a section of H over W by
   lem-trf-fppf-sheaf-coproduct-partition. On each piece the equality in the fibre
   product and the given cartesian square yield a unique map into V_i. Glue these
   maps along the clopen partition to obtain W → C.
4. The two constructions are inverse: on each partition piece their component
   sections agree; conversely the inverse images of the summands recover the unique
   partition and then the unique representing maps. Descent identifies the global maps.
5. Restriction pulls back the partition and its sections, hence both constructions
   are natural in W. This gives the stated isomorphism; its summand equations and
   projection characterize it uniquely by the same partition argument.
6. After T' → T, the representing squares give unique maps V'_i → V_i. Their
   coproduct is the unique d characterized below. The comparison commutes with it
   on each summand and hence globally. Its two projections give the displayed
   naturality equations. Applying the inverse comparison identifies C' with C ×_T T'.
7. These cartesian representations for every test prove representability of q
   (def-trf-algebraic-space). Empty indices and empty summands give the unique maps
   on empty pieces; no covering condition on the V_i is used. -/
theorem openSheafCoproduct_baseChange {S : Scheme.{u}} {I : Type (max u v)}
    (F : Sheaf (fppfTopology.over S) (Type (max u v)))
    (Fi : I → Sheaf (fppfTopology.over S) (Type (max u v)))
    (ι : ∀ i, Fi i ⟶ F) (hmono : ∀ i, Mono (ι i))
    (hopen : ∀ i, AlgebraicSpace.IsRepresentableWithLift
      (fun _ _ p ↦ IsOpenImmersion p.left) (ι i).hom)
    (H : Sheaf (fppfTopology.over S) (Type (max u v)))
    (j : ∀ i, Fi i ⟶ H) (hcol : IsColimit (Cofan.mk H j))
    (q : H ⟶ F) (hfac : ∀ i, j i ≫ q = ι i)
    (hsite : ∀ (T : Over S) (t : uliftYoneda.{v}.obj T ⟶ F.obj),
      Nonempty (OpenSheafCoproductTest Fi ι T t)) :
    (∀ X : Over S, Presheaf.IsSheaf (fppfTopology.over S) (uliftYoneda.{v}.obj X)) ∧
    AlgebraicSpace.IsRepresentableLift q.hom ∧
    ∀ (T : Over S) (t : uliftYoneda.{v}.obj T ⟶ F.obj)
      (D : OpenSheafCoproductTest Fi ι T t),
      ∃! e : uliftYoneda.{v}.obj D.C ≅ pullback q.hom t,
        D.ComparisonEquations j q e ∧
        ∀ (T' : Over S) (f : T' ⟶ T)
          (D' : OpenSheafCoproductTest Fi ι T' (uliftYoneda.{v}.map f ≫ t)),
          ∃! d : D'.C ⟶ D.C,
            (∀ i, ∃! di : D'.V i ⟶ D.V i,
              uliftYoneda.{v}.map di ≫ D.sectionMap i = D'.sectionMap i ∧
              di ≫ D.inclusion i = D'.inclusion i ≫ f ∧
              D'.injection i ≫ d = di ≫ D.injection i) ∧
            d ≫ D.p = D'.p ≫ f ∧
            IsPullback d.left D'.p.left D.p.left f.left ∧
            ∀ e' : uliftYoneda.{v}.obj D'.C ≅
                pullback q.hom (uliftYoneda.{v}.map f ≫ t),
              D'.ComparisonEquations j q e' →
              (uliftYoneda.{v}.map d ≫ e.hom ≫ pullback.fst q.hom t =
                e'.hom ≫ pullback.fst q.hom (uliftYoneda.{v}.map f ≫ t)) ∧
              (uliftYoneda.{v}.map d ≫ e.hom ≫ pullback.snd q.hom t =
                e'.hom ≫ pullback.snd q.hom (uliftYoneda.{v}.map f ≫ t) ≫
                  uliftYoneda.{v}.map f)  := by
  classical
  have hcomparison {T : Over S} {t : uliftYoneda.{v}.obj T ⟶ F.obj}
      (D : OpenSheafCoproductTest Fi ι T t) := comparison_iso H j hcol q hfac D
  refine ⟨representable_isSheaf, ?_, ?_⟩
  · intro T t
    obtain ⟨D⟩ := hsite T t
    obtain ⟨e, he, -⟩ := hcomparison D
    exact ⟨D.C, D.p, e.hom ≫ pullback.fst q.hom t,
      comparison_isPullback j q D e he, trivial⟩
  · intro T t D
    obtain ⟨e, he, hu⟩ := hcomparison D
    refine ⟨e, ⟨he, ?_⟩, fun e' he' ↦ hu e' he'.1⟩
    intro T' f D'
    have hi (i : I) : D'.sectionMap i ≫ (ι i).hom =
        uliftYoneda.{v}.map (D'.inclusion i ≫ f) ≫ t := by
      rw [(D'.cartesian i).w, ← Functor.map_comp_assoc]
    let di (i : I) : D'.V i ⟶ D.V i := uliftYoneda.{v}.preimage
      ((D.cartesian i).lift (D'.sectionMap i)
        (uliftYoneda.{v}.map (D'.inclusion i ≫ f)) (hi i))
    have hdi (i : I) : uliftYoneda.{v}.map (di i) ≫ D.sectionMap i =
        D'.sectionMap i := by
      simp only [di, Functor.map_preimage, IsPullback.lift_fst]
    have hdp (i : I) : di i ≫ D.inclusion i = D'.inclusion i ≫ f := by
      apply uliftYoneda.{v}.map_injective
      simp only [di, Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd]
    have hdu (i : I) (l : D'.V i ⟶ D.V i)
        (hl : l ≫ D.inclusion i = D'.inclusion i ≫ f) : l = di i := by
      have : IsOpenImmersion (D.inclusion i).left := D.isOpen i
      apply Over.OverMorphism.ext
      apply (cancel_mono (D.inclusion i).left).mp
      exact congrArg Over.Hom.left (hl.trans (hdp i).symm)
    let hc := (coproduct_over D'.V D'.C D'.injection D'.isColimit).some
    let d : D'.C ⟶ D.C := Cofan.IsColimit.desc hc
      (fun i ↦ di i ≫ D.injection i)
    have hd (i : I) : D'.injection i ≫ d = di i ≫ D.injection i :=
      Cofan.IsColimit.fac hc _ i
    have hproj : d ≫ D.p = D'.p ≫ f := by
      apply Cofan.IsColimit.hom_ext hc
      intro i
      change D'.injection i ≫ d ≫ D.p = D'.injection i ≫ D'.p ≫ f
      rw [← Category.assoc, hd, Category.assoc, D.injection_p, hdp,
        ← D'.injection_p i, Category.assoc]
    have hnat (e' : uliftYoneda.{v}.obj D'.C ≅
          pullback q.hom (uliftYoneda.{v}.map f ≫ t))
        (he' : D'.ComparisonEquations j q e') :
        (uliftYoneda.{v}.map d ≫ e.hom ≫ pullback.fst q.hom t =
          e'.hom ≫ pullback.fst q.hom (uliftYoneda.{v}.map f ≫ t)) ∧
        (uliftYoneda.{v}.map d ≫ e.hom ≫ pullback.snd q.hom t =
          e'.hom ≫ pullback.snd q.hom (uliftYoneda.{v}.map f ≫ t) ≫
            uliftYoneda.{v}.map f) := by
      constructor
      · apply coproduct_hom_ext D'.V D'.C D'.injection D'.isColimit H
        intro i
        rw [← Functor.map_comp_assoc, hd, Functor.map_comp, Category.assoc,
          he.1 i, ← Category.assoc, hdi, he'.1 i]
      · rw [he.2, ← Category.assoc e'.hom, he'.2,
          ← Functor.map_comp, hproj, Functor.map_comp]
    have hpb : IsPullback d.left D'.p.left D.p.left f.left := by
      obtain ⟨e', he', -⟩ := hcomparison D'
      have hp := comparison_isPullback j q D e he
      have hp' := comparison_isPullback j q D' e' he'
      have hx : IsPullback (uliftYoneda.{v}.map d) (uliftYoneda.{v}.map D'.p)
          (uliftYoneda.{v}.map D.p) (uliftYoneda.{v}.map f) := by
        apply IsPullback.of_right (h₁₂ := e.hom ≫ pullback.fst q.hom t)
          (h₂₂ := t) ?_ ?_ hp
        · rw [(hnat e' he').1]
          exact hp'
        · rw [← Functor.map_comp, hproj, Functor.map_comp]
      exact (hx.of_map_of_faithful uliftYoneda.{v}).map (Over.forget S)
    refine ⟨d, ⟨?_, hproj, hpb, hnat⟩, ?_⟩
    · intro i
      refine ⟨di i, ⟨hdi i, hdp i, hd i⟩, ?_⟩
      intro l hl
      exact hdu i l hl.2.1
    · intro d' hd'
      apply Cofan.IsColimit.hom_ext hc
      intro i
      change D'.injection i ≫ d' = D'.injection i ≫ d
      obtain ⟨l, hl, -⟩ := hd'.1 i
      rw [hl.2.2, hdu i l hl.2.1, hd]

end AlgebraicGeometry.Scheme
