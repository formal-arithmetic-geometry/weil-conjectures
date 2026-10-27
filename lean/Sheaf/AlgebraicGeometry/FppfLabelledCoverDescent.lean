/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits

/-!
# Descent of a labelled fppf cover

Source: Stacks Project, Spaces, Tags 0F15 and 02WO; Morphisms, Tags 01UA and 01S1;
Sites, Tag 00VM (blueprint: lem-trf-fppf-labelled-cover-descent).
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A labelled fppf covering with empty mixed fibre products determines its clopen
image pieces, their scheme coproduct, factorizations, and unique component sections.
The proof-indexed presentation of the supplied sections avoids transport between
sheaves with equal labels. Empty labels, covering members, and pieces are allowed.

Source: Stacks Project, Spaces, Tags 0F15 and 02WO; Morphisms, Tags 01UA and 01S1;
Sites, Tag 00VM (blueprint: lem-trf-fppf-labelled-cover-descent).

Proof:
1. By def-pc-fppf-site the maps are flat, locally finitely presented, and jointly
   surjective. By lem-weil-pbc-flat-lfp-open their images are open. Apply
   lem-weil-pbc-base-change-image to an empty mixed fibre product: the inverse
   image of one member's image under the other map is empty. Thus differently
   labelled images are disjoint.
2. Unite the images within each label. These opens cover T and are pairwise
   disjoint. The complement of each is the union of the other opens, hence open;
   each piece is closed. No finiteness is used (def-weil-size-convention).
3. Base change each piece's inclusion along a member with its label. By
   lem-weil-pbc-open-immersion-base-change its projection to the member is an
   open immersion. By lem-weil-pbc-base-change-image its image is the whole
   member, so lem-weil-pbc-open-immersion-iso-onto-image makes it an isomorphism.
   Its inverse gives the required factorization, also over S.
4. On the disjoint open pieces, maps to any scheme agree on intersections.
   By lem-weil-pbc-scheme-morphism-gluing they glue uniquely. This is the
   coproduct property of the actual inclusions (def-weil-pbc-category-colimit).
5. By lem-trf-fppf-covering-base-change the original cover pulls back to each
   piece. Differently labelled members become empty and the others identify
   with their factorizations. Discarding empty members preserves the fppf
   covering. Products over a piece equal the original overlaps up to the
   projection-compatible canonical isomorphism, since its inclusion is monic
   (lem-weil-pbc-open-immersion-monomorphism; def-pc-fibre-product).
6. The matching hypothesis and the sheaf equalizer axiom of
   def-weil-pbc-sites-and-cohomology give unique sections on the pieces.
   An unused label has the empty piece, whose empty cover forces its section
   set to be a singleton. Empty members cause no change. An empty covering
   forces T empty, and an empty label type forces the covering type empty.
-/
theorem fppf_labelled_cover_descent
    {S : Scheme.{u}} (T : Over S) {A : Type v} {I : Type w}
    (U : A → Over S) (g : ∀ a, U a ⟶ T)
    (hcover : Presieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (g a).left) ∈
      fppfPrecoverage T.left)
    (label : A → I)
    (hmixed : ∀ a b, label a ≠ label b →
      IsEmpty (pullback (g a) (g b)).left)
    (G : I → Sheaf (fppfTopology.over S) (Type t))
    (s : ∀ (i : I) (a : A), label a = i → (G i).obj.obj (op (U a)))
    (hmatch : ∀ (i : I) (a b : A) (ha : label a = i) (hb : label b = i),
      (G i).obj.map (pullback.fst (g a) (g b)).op (s i a ha) =
        (G i).obj.map (pullback.snd (g a) (g b)).op (s i b hb)) :
    ∃ V : I → T.left.Opens,
      (∀ i, (V i : Set T.left) = ⋃ (a : A) (_ : label a = i), Set.range (g a).left) ∧
      (∀ i, IsClosed (V i : Set T.left)) ∧
      Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
      iSup V = ⊤ ∧
      Nonempty (IsColimit (Cofan.mk T.left (fun i ↦ (V i).ι))) ∧
      ∃ h : ∀ (i : I) (a : A) (_ : label a = i),
          (U a ⟶ Over.mk ((V i).ι ≫ T.hom)),
        (∀ (i : I) (a : A) (ha : label a = i),
          h i a ha ≫ Over.homMk (V i).ι = g a) ∧
        ∀ i, ∃! sec : (G i).obj.obj (op (Over.mk ((V i).ι ≫ T.hom))),
          ∀ (a : A) (ha : label a = i),
            (G i).obj.map (h i a ha).op sec = s i a ha := by
  classical
  obtain ⟨hcov, hprop⟩ := (ofArrows_mem_precoverage_iff _).mp hcover
  have hopen (a : A) : IsOpen (Set.range (g a).left) := by
    have : Flat (g a).left := (hprop a).1
    have : LocallyOfFinitePresentation (g a).left := (hprop a).2
    simpa using (g a).left.isOpenMap.isOpen_range
  let V (i : I) : T.left.Opens :=
    ⟨⋃ (a : A) (_ : label a = i), Set.range (g a).left,
      isOpen_iUnion fun a ↦ isOpen_iUnion fun _ ↦ hopen a⟩
  have hmem (i : I) (x : T.left) : x ∈ V i ↔
      ∃ a, label a = i ∧ x ∈ Set.range (g a).left := by
    simp only [V, TopologicalSpace.Opens.mem_mk, Set.mem_iUnion, exists_prop]
  have hdisj : Pairwise (fun i j ↦ Disjoint (V i) (V j)) := by
    intro i j hij
    apply disjoint_iff.mpr
    apply SetLike.ext
    intro x
    change (x ∈ V i ∧ x ∈ V j) ↔ False
    refine ⟨fun ⟨hi, hj⟩ ↦ ?_, False.elim⟩
    obtain ⟨a, ha, y, rfl⟩ := (hmem i x).mp hi
    obtain ⟨b, hb, z, hz⟩ := (hmem j _).mp hj
    have hp := (IsPullback.of_hasPullback (g a) (g b)).map (Over.forget S)
    obtain ⟨p, _⟩ := exists_preimage_of_isPullback hp y z hz.symm
    exact (hmixed a b (by simpa [ha, hb] using hij)).false p
  have htotal (x : T.left) : ∃ i, x ∈ V i := by
    obtain ⟨a, ha⟩ := hcov x
    exact ⟨label a, (hmem _ _).mpr ⟨a, rfl, ha⟩⟩
  have htop : iSup V = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := htotal x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hclosed (i : I) : IsClosed (V i : Set T.left) := by
    apply isOpen_compl_iff.mp
    have heq : (V i : Set T.left)ᶜ = ⋃ j : {j : I // j ≠ i}, (V j.1 : Set T.left) := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := htotal x
        have hji : j ≠ i := by rintro rfl; exact hx hj
        exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
      · intro hx hi
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        exact Set.disjoint_left.mp
          (TopologicalSpace.Opens.coe_disjoint.mpr (hdisj j.2)) hj hi
    rw [heq]
    exact isOpen_iUnion fun j ↦ (V j.1).isOpen
  have hcop : Nonempty (IsColimit (Cofan.mk T.left (fun i ↦ (V i).ι))) := by
    let C : T.left.OpenCover := Cover.mkOfCovers I (fun i ↦ (V i).toScheme)
      (fun i ↦ (V i).ι) (fun x ↦ by
        obtain ⟨i, hi⟩ := htotal x
        exact ⟨i, ⟨x, hi⟩, rfl⟩)
    have hcompat {Z : Scheme.{u}} (b : ∀ i, (V i).toScheme ⟶ Z) (i j : I) :
        pullback.fst (V i).ι (V j).ι ≫ b i =
          pullback.snd (V i).ι (V j).ι ≫ b j := by
      by_cases hij : i = j
      · subst j
        congr 1
        exact (cancel_mono (V i).ι).mp pullback.condition
      · have : IsEmpty ↥(pullback (V i).ι (V j).ι) := by
          apply isEmpty_pullback_iff.mpr
          simpa using hdisj hij
        exact (isInitialOfIsEmpty (X := _)).hom_ext _ _
    refine ⟨Cofan.IsColimit.mk _ (fun b ↦ C.glueMorphisms b.inj (hcompat b.inj)) ?_ ?_⟩
    · intro b i
      exact C.ι_glueMorphisms b.inj (hcompat b.inj) i
    · intro b m hm
      exact C.hom_ext _ _ fun i ↦ (hm i).trans (C.ι_glueMorphisms b.inj (hcompat b.inj) i).symm
  let k (i : I) (a : A) (ha : label a = i) : (U a).left ⟶ (V i).toScheme :=
    IsOpenImmersion.lift (V i).ι (g a).left (by
      rw [Scheme.Opens.range_ι]
      exact fun x hx ↦ (hmem i x).mpr ⟨a, ha, hx⟩)
  have hk (i : I) (a : A) (ha : label a = i) :
      k i a ha ≫ (V i).ι = (g a).left := IsOpenImmersion.lift_fac _ _ _
  let h (i : I) (a : A) (ha : label a = i) : U a ⟶ Over.mk ((V i).ι ≫ T.hom) :=
    Over.homMk (k i a ha) (by simp [← Category.assoc, hk, Over.w])
  have hh (i : I) (a : A) (ha : label a = i) :
      h i a ha ≫ Over.homMk (V i).ι = g a := by
    apply Over.OverMorphism.ext
    exact hk i a ha
  refine ⟨V, (fun _ ↦ rfl), hclosed, hdisj, htop, hcop, h, hh, ?_⟩
  intro i
  let B := {a : A // label a = i}
  let W : B → Over S := fun a ↦ U a.1
  let f (a : B) : W a ⟶ Over.mk ((V i).ι ≫ T.hom) := h i a.1 a.2
  have hf : Presieve.ofArrows (fun a ↦ (W a).left) (fun a ↦ (f a).left) ∈
      fppfPrecoverage (V i).toScheme := by
    apply (ofArrows_mem_precoverage_iff _).mpr
    constructor
    · intro x
      obtain ⟨a, ha, y, hy⟩ := (hmem i x.1).mp x.2
      refine Exists.intro (⟨a, ha⟩ : B) (Exists.intro y ?_)
      apply Subtype.ext
      change (V i).ι (k i a ha y) = x.1
      rw [← Scheme.Hom.comp_apply, hk i a ha, hy]
    · intro a
      have hp : IsPullback (𝟙 (U a.1).left) (k i a.1 a.2)
          (g a.1).left (V i).ι :=
        IsPullback.of_horiz_isIso_mono ⟨by simp [hk]⟩
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hp (hprop a.1)
  have hfs : Sieve.ofArrows W f ∈ (fppfTopology.over S) (Over.mk ((V i).ι ≫ T.hom)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Precoverage.generate_mem_toGrothendieck hf
  have hsheaf := (isSheaf_iff_isSheaf_of_type (fppfTopology.over S) (G i).obj).mp (G i).property
  have hs : (Presieve.ofArrows W f).IsSheafFor (G i).obj :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsheaf _ hfs)
  have hcompat : Presieve.Arrows.Compatible (G i).obj f (fun a ↦ s i a.1 a.2) := by
    intro a b Z p q hpq
    have heq : p ≫ g a.1 = q ≫ g b.1 := by
      rw [← hh i a.1 a.2, ← hh i b.1 b.2, ← Category.assoc, ← Category.assoc]
      exact congrArg (fun m ↦ m ≫ Over.homMk (V i).ι) hpq
    let l := pullback.lift p q heq
    have he := congrArg (fun z ↦ (G i).obj.map l.op z) (hmatch i a.1 b.1 a.2 b.2)
    simpa only [← Functor.map_comp_apply, ← op_comp, l, pullback.lift_fst,
      pullback.lift_snd] using he
  obtain ⟨sec, hsec, huniq⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hs
    (fun a ↦ s i a.1 a.2) hcompat
  exact ⟨sec, fun a ha ↦ hsec ⟨a, ha⟩, fun sec' hs' ↦ huniq sec' (fun a ↦ hs' a.1 a.2)⟩

end AlgebraicGeometry.Scheme
