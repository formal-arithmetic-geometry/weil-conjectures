/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Equality loci for sections of coproducts of fppf sheaves

Source: Stacks Project, Spaces, Tag 02WQ, omitted diagonal verification, expanded
using Tags 0F15 and 02WO (blueprint: lem-trf-coproduct-equality-locus).

The pullback square is the natural representing isomorphism, including its projection.
Its top map is the section pulled back along the induced coproduct projection, so its
restriction to each summand is the prescribed component equality. All representables
are lifted to the coefficient universe. The scheme coproduct is specified by a colimit
cofan, permitting every small index set for which that coproduct lies in the chosen site.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Inclusion between open subschemes over the base, used to restrict a section to
an intersection. Source: Stacks, Spaces, Tags 0F15 and 02WO
(blueprint: lem-trf-coproduct-equality-locus). -/
noncomputable def fppfEqualityOpenInclusion {S : Scheme.{u}} (T : Over S)
    {U V : T.left.Opens} (h : U ≤ V) :
    fppfPartitionOpen T U ⟶ fppfPartitionOpen T V :=
  (T.left.restrictFunctor ⋙ Over.map T.hom).map (homOfLE h)

/-- The map from the coproduct of the component equality schemes to the test scheme.
It is the colimit descent of their maps through the same-label intersections.
Source: Stacks, Spaces, Tag 02WQ, omitted diagonal verification
(blueprint: lem-trf-coproduct-equality-locus). -/
def fppfEqualityCoproductProjection {S : Scheme.{u}} {I : Type (max u v)}
    (T : Over S) (D : I → T.left.Opens) (E : I → Over S)
    (p : ∀ i, E i ⟶ fppfPartitionOpen T (D i))
    (L : Over S) (j : ∀ i, E i ⟶ L) (hL : IsColimit (Cofan.mk L j)) : L ⟶ T :=
  hL.desc (Cofan.mk T (fun i ↦ p i ≫ fppfPartitionInclusion T (D i)))

private theorem coproduct_geometry {S : Scheme.{u}} {I : Type (max u v)}
    (T : Over S) (U : I → T.left.Opens)
    (hU : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (E : I → Over S) (r : ∀ i, E i ⟶ fppfPartitionOpen T (U i))
    (L : Over S) (j : ∀ i, E i ⟶ L) (hL : IsColimit (Cofan.mk L j)) :
    (∀ i, IsOpenImmersion (j i).left) ∧
      (∀ x : L.left, ∃ i y, (j i).left y = x) := by
  classical
  let K := {i : I // Nonempty (E i).left}
  let x (i : K) : (E i.val).left := Classical.choice i.property
  have hx (i : K) : ((r i.val).left (x i)).val ∈ U i.val :=
    ((r i.val).left (x i)).property
  have hsmall : Small.{u} K := by
    apply small_of_injective (f := fun i : K ↦ ((r i.val).left (x i)).val)
    intro i k h
    apply Subtype.ext
    by_contra hik
    have hk : ((r i.val).left (x i)).val ∈ U k.val := by
      change ((r i.val).left (x i)).val = ((r k.val).left (x k)).val at h
      rw [h]
      exact hx k
    exact (hU hik).le_bot ⟨hx i, hk⟩
  let X (i : K) : Scheme.{u} := (E i.val).left
  let P := ∐ X
  let e (i : I) : (E i).left ⟶ P := by
    by_cases hi : Nonempty (E i).left
    · exact Sigma.ι X ⟨i, hi⟩
    · let : IsEmpty (E i).left := not_nonempty_iff.mp hi
      exact isInitialOfIsEmpty.to P
  have he : IsColimit (Cofan.mk P e) := by
    refine Cofan.IsColimit.mk _ (fun s ↦ Sigma.desc (fun i : K ↦ s.inj i.val)) ?_ ?_
    · intro s i
      by_cases hi : Nonempty (E i).left
      · change e i ≫ _ = _
        rw [show e i = Sigma.ι X ⟨i, hi⟩ from dif_pos hi]
        exact Sigma.ι_desc (fun k : K ↦ s.inj k.val) ⟨i, hi⟩
      · let : IsEmpty (E i).left := not_nonempty_iff.mp hi
        exact isInitialOfIsEmpty.hom_ext _ _
    · intro s m hm
      apply Sigma.hom_ext (f := X)
      intro i
      rw [Sigma.ι_desc]
      have hi := hm i.val
      change e i.val ≫ m = s.inj i.val at hi
      simpa only [e, dif_pos i.property] using hi
  have hL' : IsColimit (Cofan.mk L.left (fun i ↦ (j i).left)) :=
    (Cofan.isColimitMapCoconeEquiv (Over.forget S) _ _).toFun
      (isColimitOfPreserves (Over.forget S) hL)
  let iso : P ≅ L.left := he.coconePointUniqueUpToIso hL'
  have hj (i : I) : e i ≫ iso.hom = (j i).left :=
    he.comp_coconePointUniqueUpToIso_hom hL' ⟨i⟩
  have hjK (i : K) : Sigma.ι X i ≫ iso.hom = (j i.val).left := by
    simpa [e, i.property] using hj i.val
  constructor
  · intro i
    by_cases hi : Nonempty (E i).left
    · rw [← hjK ⟨i, hi⟩]
      infer_instance
    · let : IsEmpty (E i).left := not_nonempty_iff.mp hi
      infer_instance
  · intro z
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover X).exists_eq (iso.inv z)
    refine ⟨i.val, y, ?_⟩
    rw [← hjK]
    change iso.hom (Sigma.ι X i y) = z
    change Sigma.ι X i y = iso.inv z at hy
    rw [hy]
    exact Scheme.Hom.comp_apply iso.inv iso.hom z |>.symm.trans (by simp)

private theorem local_equality_data {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type (max u v)) {D E : Over S}
    (a b : F.obj (op D)) (p : E ⟶ D)
    (h : IsPullback (uliftYonedaEquiv.{v}.symm (F.map p.op a))
      (uliftYoneda.{v}.map p) (prod.lift (𝟙 F) (𝟙 F))
      (prod.lift (uliftYonedaEquiv.{v}.symm a) (uliftYonedaEquiv.{v}.symm b))) :
    F.map p.op a = F.map p.op b ∧ Mono p ∧
      ∀ (Z : Over S) (f : Z ⟶ D), F.map f.op a = F.map f.op b →
        ∃ g : Z ⟶ E, g ≫ p = f := by
  have hab := congrArg (fun k ↦ k ≫ prod.snd) h.w
  simp only [Category.assoc, prod.lift_snd, Category.comp_id] at hab
  have heq : F.map p.op a = F.map p.op b :=
    uliftYonedaEquiv.symm.injective
      (hab.trans (uliftYonedaEquiv_symm_map p.op b).symm)
  have : Mono (uliftYoneda.{v}.map p) := h.mono_snd_of_mono
  have hp : Mono p := (uliftYoneda.{v}).mono_of_mono_map
    (inferInstance : Mono (uliftYoneda.{v}.map p))
  refine ⟨heq, hp, ?_⟩
  intro Z f hf
  have hw : uliftYonedaEquiv.{v}.symm (F.map f.op a) ≫ prod.lift (𝟙 F) (𝟙 F) =
      uliftYoneda.{v}.map f ≫
        prod.lift (uliftYonedaEquiv.{v}.symm a) (uliftYonedaEquiv.{v}.symm b) := by
    apply prod.hom_ext <;>
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id]
    · exact (uliftYonedaEquiv_symm_map f.op a)
    · exact (congrArg uliftYonedaEquiv.symm hf).trans
        (uliftYonedaEquiv_symm_map f.op b)
  let l := h.lift (uliftYonedaEquiv.{v}.symm (F.map f.op a)) (uliftYoneda.map f) hw
  let g : Z ⟶ E := (uliftYoneda.{v}).preimage l
  refine ⟨g, (uliftYoneda.{v}).map_injective ?_⟩
  change uliftYoneda.map ((uliftYoneda.{v}).preimage l ≫ p) = _
  rw [Functor.map_comp, Functor.map_preimage]
  exact h.lift_snd _ _ hw

private theorem open_lift_over {S : Scheme.{u}} {X Y Z : Over S}
    (j : X ⟶ Y) [IsOpenImmersion j.left] (f : Z ⟶ Y)
    (hr : Set.range f.left ⊆ Set.range j.left) : ∃ g : Z ⟶ X, g ≫ j = f := by
  let g := IsOpenImmersion.lift j.left f.left hr
  have hg : g ≫ j.left = f.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk g ?_, ?_⟩
  · rw [← Over.w j, ← Category.assoc, hg, Over.w f]
  · apply Over.OverMorphism.ext
    exact hg

private theorem sheaf_sections_ext {S : Scheme.{u}} {I : Type (max u v)}
    (F : Sheaf (fppfTopology.over S) (Type (max u v)))
    {X : Over S} (Y : I → Over S) (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, IsOpenImmersion (j i).left)
    (hcov : ∀ x : X.left, ∃ i y, (j i).left y = x)
    {a b : F.obj.obj (op X)}
    (hab : ∀ i, F.obj.map (j i).op a = F.obj.map (j i).op b) : a = b := by
  let cover : X.left.OpenCover := Cover.mkOfCovers I (fun i ↦ (Y i).left)
    (fun i ↦ (j i).left) hcov hj
  have hmem : Sieve.ofArrows Y j ∈ (fppfTopology.over S) X := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage)
      _ cover.mem_grothendieckTopology
  apply (F.property.isSheafFor _ hmem).isSeparatedFor.ext
  intro Z f hf
  obtain ⟨i, g, rfl⟩ := Sieve.ofArrows.exists hf
  simpa only [op_comp, F.obj.map_comp, types_comp_apply] using congrArg
    (F.obj.map g.op) (hab i)

private theorem mapsTo_restrict {S : Scheme.{u}} {I : Type (max u v)}
    {G : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {C : Sheaf (fppfTopology.over S) (Type (max u v))} (c : ∀ i, G i ⟶ C)
    {T : Over S} (A : FppfCoproductPartition G T) (a : C.obj.obj (op T))
    (ha : A.MapsTo c a) (i : I) {Z : Over S}
    (k : Z ⟶ fppfPartitionOpen T (A.opens i)) :
    (c i).hom.app (op Z) ((G i).obj.map k.op (A.sections i)) =
      C.obj.map (k ≫ fppfPartitionInclusion T (A.opens i)).op a := by
  rw [NatTrans.naturality_apply, ha i, op_comp, Functor.map_comp]
  rfl

private theorem openInclusion_comp {S : Scheme.{u}} (T : Over S)
    {U V : T.left.Opens} (h : U ≤ V) :
    fppfEqualityOpenInclusion T h ≫ fppfPartitionInclusion T V =
      fppfPartitionInclusion T U := by
  apply Over.OverMorphism.ext
  exact T.left.homOfLE_ι h

private theorem intersection_mapsTo {S : Scheme.{u}} {I : Type (max u v)}
    {G : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {C : Sheaf (fppfTopology.over S) (Type (max u v))} (c : ∀ i, G i ⟶ C)
    {T : Over S} (A : FppfCoproductPartition G T) (a : C.obj.obj (op T))
    (ha : A.MapsTo c a) (i : I) {U : T.left.Opens} (hU : U ≤ A.opens i)
    {Z : Over S} (g : Z ⟶ fppfPartitionOpen T U) :
    (c i).hom.app (op Z) ((G i).obj.map g.op
      ((G i).obj.map (fppfEqualityOpenInclusion T hU).op (A.sections i))) =
      C.obj.map (g ≫ fppfPartitionInclusion T U).op a := by
  simpa only [op_comp, Functor.map_comp, types_comp_apply, Category.assoc,
    openInclusion_comp] using
    mapsTo_restrict c A a ha i (g ≫ fppfEqualityOpenInclusion T hU)

/-- The coproduct of the equality schemes on the same-label intersections represents
exactly the equality sheaf of the original sections. The assertion is the cartesian
square `h_L ≅ h_T ×_(C × C) C`, with its specified projection and diagonal section;
there is no algebraic-space hypothesis on any summand.
Source: Stacks, Spaces, Tag 02WQ, omitted diagonal verification, using Tags 0F15 and
02WO (blueprint: lem-trf-coproduct-equality-locus).

Proof:
1. For a map `Z → L`, the inverse images of the coproduct summands form a clopen
   partition by lem-weil-pbc-scheme-coproduct-family. On the piece labelled `i`, the
   local representing square gives equality in `G i`. Applying its coprojection
   gives equality in `C`; the sheaf condition, or the converse and uniqueness in
   lem-trf-fppf-sheaf-coproduct-partition, gives equality on `Z`.
2. Conversely, a map `f : Z → T` with equal pulled-back sections has equal labelled
   partitions by lem-trf-fppf-sheaf-coproduct-partition. Thus the inverse images of
   `A_i` and `B_i` coincide with the inverse image of their intersection. The component
   sections agree in `G i` by injectivity on sections. The local representing square
   gives a unique lift from this piece to `E i`.
3. Glue these lifts into `L` by lem-weil-pbc-scheme-morphism-gluing. Different pieces
   have empty intersection, on which scheme morphisms are unique. The resulting map
   composed with the induced projection equals `f`, by the same gluing uniqueness.
4. Any other lift has summand inverse images equal to the same labelled partition:
   each summand maps into its own `A_i`, and both collections cover disjointly.
   The local representing squares give the same maps on every piece, hence gluing
   uniqueness makes the lifts equal.
5. The forward correspondence is composition with the displayed coproduct projection,
   so it commutes with every test morphism, and its inverse is natural by uniqueness.
   A point of `h_T ×_(C × C) C` is a pair `(f,s)` with `(f*a,f*b)=(s,s)`; it is
   uniquely determined by a map `f` with `f*a=f*b`. On a summand, the comparison is
   precisely its given component equality. Empty pieces contribute nothing; for an
   empty index type the partition forces `T` empty, and the same argument applies. -/
theorem fppfSheaf_coproduct_equality_locus
    {S : Scheme.{u}} {I : Type (max u v)}
    (G : I → Sheaf (fppfTopology.over S) (Type (max u v)))
    (C : Sheaf (fppfTopology.over S) (Type (max u v)))
    (c : ∀ i, G i ⟶ C) (hc : IsColimit (Cofan.mk C c))
    (T : Over S) (a b : C.obj.obj (op T))
    (A B : FppfCoproductPartition G T) (hA : A.MapsTo c a) (hB : B.MapsTo c b)
    (E : I → Over S)
    (p : ∀ i, E i ⟶ fppfPartitionOpen T (A.opens i ⊓ B.opens i))
    (hE : ∀ i, IsPullback
      (uliftYonedaEquiv.{v}.symm ((G i).obj.map (p i).op
        ((G i).obj.map (fppfEqualityOpenInclusion T inf_le_left).op (A.sections i))))
      (uliftYoneda.{v}.map (p i))
      (prod.lift (𝟙 (G i).obj) (𝟙 (G i).obj))
      (prod.lift
        (uliftYonedaEquiv.{v}.symm
          ((G i).obj.map (fppfEqualityOpenInclusion T inf_le_left).op (A.sections i)))
        (uliftYonedaEquiv.{v}.symm
          ((G i).obj.map (fppfEqualityOpenInclusion T inf_le_right).op (B.sections i)))))
    (L : Over S) (j : ∀ i, E i ⟶ L) (hL : IsColimit (Cofan.mk L j)) :
    IsPullback
      (uliftYonedaEquiv.{v}.symm (C.obj.map
        (fppfEqualityCoproductProjection T (fun i ↦ A.opens i ⊓ B.opens i)
          E p L j hL).op a))
      (uliftYoneda.{v}.map
        (fppfEqualityCoproductProjection T (fun i ↦ A.opens i ⊓ B.opens i) E p L j hL))
      (prod.lift (𝟙 C.obj) (𝟙 C.obj))
      (prod.lift (uliftYonedaEquiv.{v}.symm a) (uliftYonedaEquiv.{v}.symm b)) := by
  classical
  have hopen (U : T.left.Opens) :
      IsOpenImmersion (fppfPartitionInclusion T U).left := inferInstanceAs
    (IsOpenImmersion U.ι)
  have hmonopen (U : T.left.Opens) : Mono (fppfPartitionInclusion T U) := by
    apply (Over.forget S).mono_of_mono_map
    exact inferInstanceAs (Mono U.ι)
  let D (i : I) := A.opens i ⊓ B.opens i
  let q := fppfEqualityCoproductProjection T D E p L j hL
  have hjq (i : I) : j i ≫ q = p i ≫ fppfPartitionInclusion T (D i) :=
    hL.fac (Cofan.mk T (fun i ↦ p i ≫ fppfPartitionInclusion T (D i))) ⟨i⟩
  have hdata (i : I) := local_equality_data (G i).obj _ _ (p i) (hE i)
  have hD : Pairwise (fun i k ↦ Disjoint (D i) (D k)) :=
    fun i k hik ↦ (A.disjoint hik).mono inf_le_left inf_le_left
  obtain ⟨hj, hcover⟩ := coproduct_geometry T D hD E p L j hL
  have heq : C.obj.map q.op a = C.obj.map q.op b := by
    apply sheaf_sections_ext C E j hj hcover
    intro i
    have hi := congrArg ((c i).hom.app (op (E i))) (hdata i).1
    rw [intersection_mapsTo c A a hA i inf_le_left,
      intersection_mapsTo c B b hB i inf_le_right] at hi
    simpa only [← types_comp_apply, ← Functor.map_comp, ← op_comp, hjq] using hi
  have hlift : ∀ (Z : Over S) (f : Z ⟶ T),
      C.obj.map f.op a = C.obj.map f.op b → ∃ g : Z ⟶ L, g ≫ q = f := by
    intro Z f hf
    have part := (fppfSheaf_coproduct_partition G).2 C c hc
    have da := part.2.2.1 T a A hA
    have db := part.2.2.1 T b B hB
    obtain ⟨ea, hea, heao⟩ := da.2.2 Z f
    obtain ⟨eb, heb, hebo⟩ := db.2.2 Z f
    have heab : ea = eb := (part.2.1 Z (C.obj.map f.op a)).unique hea (hf.symm ▸ heb)
    have hbopens (i : I) : ea.opens i = f.left ⁻¹ᵁ B.opens i := by
      rw [heab]
      exact (hebo i).1
    let W (i : I) := fppfPartitionOpen Z (ea.opens i)
    let w (i : I) : W i ⟶ Z := fppfPartitionInclusion Z (ea.opens i)
    have hfactor (i : I) : ∃ d : W i ⟶ fppfPartitionOpen T (D i),
        d ≫ fppfPartitionInclusion T (D i) = w i ≫ f := by
      apply open_lift_over
      rintro _ ⟨x, rfl⟩
      have hxa : f.left x.val ∈ A.opens i := by
        exact SetLike.le_def.mp (le_of_eq (heao i).1) x.property
      have hxb : f.left x.val ∈ B.opens i := by
        exact SetLike.le_def.mp (le_of_eq (hbopens i)) x.property
      exact ⟨⟨f.left x.val, hxa, hxb⟩, rfl⟩
    choose d hd using hfactor
    have hv (i : I) : ∃ v : W i ⟶ E i, v ≫ p i = d i := by
      apply (hdata i).2.2
      apply (part.1 i).2 (W i)
      rw [intersection_mapsTo c A a hA i inf_le_left,
        intersection_mapsTo c B b hB i inf_le_right, hd i]
      simpa only [op_comp, Functor.map_comp, types_comp_apply] using
        congrArg (C.obj.map (w i).op) hf
    choose v hv using hv
    have hw : IsColimit (Cofan.mk Z w) := by
      apply isColimitOfReflects (Over.forget S)
      apply (Cofan.isColimitMapCoconeEquiv (Over.forget S) W (Cofan.mk Z w)).symm.toFun
      exact (part.2.2.1 Z (C.obj.map f.op a) ea hea).1.some
    let g := hw.desc (Cofan.mk L (fun i ↦ v i ≫ j i))
    refine ⟨g, ?_⟩
    apply Cofan.IsColimit.hom_ext hw
    intro i
    change w i ≫ (g ≫ q) = w i ≫ f
    have hwi : w i ≫ g = v i ≫ j i :=
      hw.fac (Cofan.mk L (fun i ↦ v i ≫ j i)) ⟨i⟩
    rw [← Category.assoc, hwi, Category.assoc, hjq, ← Category.assoc, hv, hd]
  have hjmem (i : I) (x : (E i).left) : q.left ((j i).left x) ∈ A.opens i := by
    have h := congrArg (fun k : E i ⟶ T ↦ k.left x) (hjq i)
    change q.left ((j i).left x) = ((p i).left x).val at h
    rw [h]
    exact ((p i).left x).property.1
  have hlabel (i : I) (x : L.left) (hx : q.left x ∈ A.opens i) :
      x ∈ Set.range (j i).left := by
    obtain ⟨k, y, rfl⟩ := hcover x
    have hki : k = i := by
      by_contra hki
      exact (A.disjoint hki).le_bot ⟨hjmem k y, hx⟩
    subst k
    exact ⟨y, rfl⟩
  have hmono : Mono q := by
    constructor
    intro Z f g hfg
    have part := (fppfSheaf_coproduct_partition G).2 C c hc
    obtain ⟨d, hd, hdo⟩ := (part.2.2.1 T a A hA).2.2 Z (f ≫ q)
    have hw := (part.2.2.1 Z (C.obj.map (f ≫ q).op a) d hd).1.some
    apply Over.OverMorphism.ext
    apply Cofan.IsColimit.hom_ext hw
    intro i
    let W := fppfPartitionOpen Z (d.opens i)
    let w : W ⟶ Z := fppfPartitionInclusion Z (d.opens i)
    have hfactors (k : Z ⟶ L) (hk : k ≫ q = f ≫ q) :
        ∃ l : W ⟶ E i, l ≫ j i = w ≫ k := by
      let := hj i
      apply open_lift_over
      rintro _ ⟨x, rfl⟩
      apply hlabel
      have hx : q.left (f.left x.val) ∈ A.opens i :=
        SetLike.le_def.mp (le_of_eq (hdo i).1) x.property
      have he := congrArg (fun z : Z ⟶ T ↦ z.left x.val) hk
      change q.left (k.left x.val) = q.left (f.left x.val) at he
      change q.left (k.left x.val) ∈ A.opens i
      rw [he]
      exact hx
    obtain ⟨lf, hlf⟩ := hfactors f rfl
    obtain ⟨lg, hlg⟩ := hfactors g hfg.symm
    have : Mono (p i) := (hdata i).2.1
    have : Mono (j i ≫ q) := by
      rw [hjq]
      infer_instance
    have hflg : lf = lg := (cancel_mono (j i ≫ q)).mp (by
      rw [← Category.assoc, hlf, ← Category.assoc, hlg, Category.assoc,
        Category.assoc, hfg])
    have he : w ≫ f = w ≫ g := by rw [← hlf, ← hlg, hflg]
    exact congrArg Over.Hom.left he
  have hw : uliftYonedaEquiv.{v}.symm (C.obj.map q.op a) ≫
      prod.lift (𝟙 C.obj) (𝟙 C.obj) = uliftYoneda.{v}.map q ≫
        prod.lift (uliftYonedaEquiv.{v}.symm a) (uliftYonedaEquiv.{v}.symm b) := by
    apply prod.hom_ext <;>
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id]
    · exact uliftYonedaEquiv_symm_map q.op a
    · exact (congrArg uliftYonedaEquiv.symm heq).trans
        (uliftYonedaEquiv_symm_map q.op b)
  apply IsPullback.of_forall_isPullback_app
  intro Z
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun k ↦ k.app Z) hw, ?_, ?_⟩
  · intro x y hxy
    apply ULift.ext
    exact (cancel_mono q).mp (congrArg ULift.down hxy.2)
  · intro s f hsf
    have ha : s = C.obj.map f.down.op a := by
      have h := congrArg ((prod.fst : C.obj ⨯ C.obj ⟶ C.obj).app Z) hsf
      simpa only [← types_comp_apply, ← NatTrans.comp_app, prod.lift_fst,
        NatTrans.id_app, types_id_apply, uliftYonedaEquiv_symm_apply_app,
        TypeCat.Fun.toFun_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk] using h
    have hb : s = C.obj.map f.down.op b := by
      have h := congrArg ((prod.snd : C.obj ⨯ C.obj ⟶ C.obj).app Z) hsf
      simpa only [← types_comp_apply, ← NatTrans.comp_app, prod.lift_snd,
        NatTrans.id_app, types_id_apply, uliftYonedaEquiv_symm_apply_app,
        TypeCat.Fun.toFun_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk] using h
    obtain ⟨g, hg⟩ := hlift Z.unop f.down (ha.symm.trans hb)
    refine ⟨ULift.up g, ?_, ?_⟩
    · change C.obj.map g.op (C.obj.map q.op a) = s
      rw [← types_comp_apply, ← Functor.map_comp, ← op_comp, hg]
      exact ha.symm
    · exact congrArg ULift.up hg

end AlgebraicGeometry.Scheme
