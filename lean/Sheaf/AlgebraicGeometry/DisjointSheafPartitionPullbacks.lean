/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Yoneda
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Summand pullbacks recognized by a disjoint clopen sheaf partition

Source: Stacks Project, spaces.tex, Tags 0F15 and 02WO, the omitted summand
pullback verification (blueprint: lem-trf-disjoint-sheaf-partition-pullbacks).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FppfPartition

/-- The canonical open subscheme as an object over the base.
Source: Stacks Project, Tags 01IJ and 0F15
(blueprint: lem-trf-disjoint-sheaf-partition-pullbacks). -/
def openObject {S : Scheme.{u}} (T : Over S) (U : T.left.Opens) : Over S :=
  Over.mk (U.ι ≫ T.hom)

/-- The inclusion of an open subscheme, as a morphism over the base.
Source: Stacks Project, Tags 01IJ and 0F15
(blueprint: lem-trf-disjoint-sheaf-partition-pullbacks). -/
def openInclusion {S : Scheme.{u}} (T : Over S) (U : T.left.Opens) :
    openObject T U ⟶ T :=
  Over.homMk U.ι

/-- Restriction of a base morphism to the inverse image of an open subscheme.
Source: Stacks Project, Tag 01HI, lemma-restrict-map-to-opens
(blueprint: lem-trf-disjoint-sheaf-partition-pullbacks). -/
noncomputable def openRestriction {S : Scheme.{u}} {Z T : Over S} (b : Z ⟶ T) (U : T.left.Opens) :
    openObject Z (b.left ⁻¹ᵁ U) ⟶ openObject T U :=
  Over.homMk (b.left ∣_ U) (by
    change (b.left ∣_ U) ≫ U.ι ≫ T.hom = (b.left ⁻¹ᵁ U).ι ≫ Z.hom
    rw [morphismRestrict_ι_assoc, Over.w])

set_option backward.isDefEq.respectTransparency.types false in
/-- The sheaf axiom for an explicit fppf covering family (Stacks, Tag 021L). -/
private theorem sheafFor_cover {S : Scheme.{u}}
    (H : Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    {J : Type w} (T : Over S) (X : J → Over S) (f : ∀ j, X j ⟶ T)
    (hc : ∀ x : T.left, ∃ j y, (f j).left y = x)
    (hp : ∀ j, Flat (f j).left ∧ LocallyOfFinitePresentation (f j).left) :
    Presieve.IsSheafFor H.obj (Presieve.ofArrows X f) := by
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp H.property).isSheafFor
  change Sieve.ofArrows X f ∈ (Scheme.fppfTopology.over S) T
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    (Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) J
      (fun j ↦ (X j).left) (fun j ↦ (f j).left) hc hp).mem₀

/-- Uniqueness over an empty scheme, using its empty covering (Stacks, Tag 00VM). -/
private theorem empty_sections {S : Scheme.{u}}
    (H : Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    (T : Over S) [IsEmpty T.left] (x y : H.obj.obj (op T)) : x = y := by
  have hf := sheafFor_cover H T (fun j : Empty ↦ j.elim) (fun j ↦ j.elim)
    (fun x ↦ isEmptyElim x) (fun j ↦ j.elim)
  obtain ⟨a, _, ha⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hf
    (fun j ↦ j.elim) (fun j ↦ j.elim)
  exact (ha x (fun j ↦ j.elim)).trans (ha y (fun j ↦ j.elim)).symm

/-- The pointwise covering condition extracted from the supremum of opens. -/
private theorem open_cover {S : Scheme.{u}} {J : Type w} (T : Over S)
    (U : J → T.left.Opens) (hU : iSup U = ⊤) (x : T.left) : ∃ j, x ∈ U j := by
  have hx : x ∈ (⨆ j, U j) := by rw [hU]; trivial
  simpa only [TopologicalSpace.Opens.mem_iSup] using hx

/-- Unique gluing on a disjoint open cover, including the empty cover (Stacks, Tag 00VM). -/
private theorem glue {S : Scheme.{u}} {J : Type w}
    (H : Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    (T : Over S) (U : J → T.left.Opens)
    (hd : Pairwise (fun i j ↦ Disjoint (U i) (U j))) (hc : iSup U = ⊤)
    (x : ∀ i, H.obj.obj (op (openObject T (U i)))) :
    ∃! a, ∀ i, H.obj.map (openInclusion T (U i)).op a = x i := by
  have hf := sheafFor_cover H T (fun i ↦ openObject T (U i))
    (fun i ↦ openInclusion T (U i)) (fun z ↦ by
      obtain ⟨i, hi⟩ := open_cover T U hc z
      exact ⟨i, ⟨z, hi⟩, rfl⟩) (fun i ↦ by
      change Flat (U i).ι ∧ LocallyOfFinitePresentation (U i).ι
      exact ⟨inferInstance, inferInstance⟩)
  apply (Presieve.isSheafFor_arrows_iff _ _).mp hf x
  intro i j Z gi gj e
  classical
  by_cases hij : i = j
  · subst j
    have e' : gi = gj := by
      apply Over.OverMorphism.ext
      exact (cancel_mono (U i).ι).mp (congrArg Over.Hom.left e)
    rw [e']
  · have : IsEmpty Z.left := ⟨fun z ↦ by
      have ez : (gi.left z).val = (gj.left z).val :=
        congrArg (fun f ↦ f.left z) e
      have hm : (gi.left z).val ∈ U i ⊓ U j :=
        ⟨(gi.left z).property, ez.symm ▸ (gj.left z).property⟩
      rw [(hd hij).eq_bot] at hm
      exact hm⟩
    exact empty_sections H Z _ _

/-- The canonical restriction commutes with open inclusions (Stacks, Tag 01HI). -/
private theorem restriction_square {S : Scheme.{u}} {Z T : Over S}
    (b : Z ⟶ T) (U : T.left.Opens) :
    openRestriction b U ≫ openInclusion T U =
      openInclusion Z (b.left ⁻¹ᵁ U) ≫ b := by
  ext
  exact morphismRestrict_ι b.left U

/-- The section equation remains valid under restriction (Stacks, Tag 0F15). -/
private theorem restrict_image {S : Scheme.{u}} {T : Over S}
    (H G : Sheaf (Scheme.fppfTopology.over S) (Type (max u v))) (c : G ⟶ H)
    (U : T.left.Opens) (t : G.obj.obj (op (openObject T U))) (a : H.obj.obj (op T))
    (ha : c.hom.app _ t = H.obj.map (openInclusion T U).op a)
    {Z : Over S} (b : Z ⟶ T) :
    c.hom.app _ (G.obj.map (openRestriction b U).op t) =
      H.obj.map (openInclusion Z (b.left ⁻¹ᵁ U)).op (H.obj.map b.op a) := by
  rw [NatTrans.naturality_apply, ha]
  simp only [← Functor.map_comp_apply, ← op_comp, restriction_square]

/-- Disjointness forces a section of the i-th sheaf to map into the i-th open (Tag 0F15). -/
private theorem image_mem {S : Scheme.{u}} {I : Type w}
    (H : Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    (G : I → Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    (c : ∀ i, G i ⟶ H)
    (hd : ∀ i j, i ≠ j → ∀ (V : Over S)
      (s : (G i).obj.obj (op V)) (t : (G j).obj.obj (op V)),
      (c i).hom.app (op V) s = (c j).hom.app (op V) t → IsEmpty V.left)
    (T : Over S) (U : I → T.left.Opens) (hc : iSup U = ⊤)
    (t : ∀ i, (G i).obj.obj (op (openObject T (U i)))) (a : H.obj.obj (op T))
    (ha : ∀ i, (c i).hom.app _ (t i) = H.obj.map (openInclusion T (U i)).op a)
    {Z : Over S} (b : Z ⟶ T) (i : I) (s : (G i).obj.obj (op Z))
    (hs : (c i).hom.app _ s = H.obj.map b.op a) (z : Z.left) : b.left z ∈ U i := by
  classical
  obtain ⟨j, hj⟩ := open_cover T U hc (b.left z)
  by_cases hij : i = j
  · simpa [hij] using hj
  · have he := hd i j hij (openObject Z (b.left ⁻¹ᵁ U j))
      ((G i).obj.map (openInclusion Z (b.left ⁻¹ᵁ U j)).op s)
      ((G j).obj.map (openRestriction b (U j)).op (t j)) (by
        rw [NatTrans.naturality_apply, hs, restrict_image H (G j) (c j) (U j)
          (t j) a (ha j) b])
    exact (he.false ⟨z, hj⟩).elim

/-- Compare partitions pointwise, then use injectivity on sections (Stacks, Tag 0F15). -/
private theorem partition_unique {S : Scheme.{u}} {I : Type w}
    (H : Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    (G : I → Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    (c : ∀ i, G i ⟶ H)
    (hi : ∀ i (V : Over S), Function.Injective ((c i).hom.app (op V)))
    (hd : ∀ i j, i ≠ j → ∀ (V : Over S)
      (s : (G i).obj.obj (op V)) (t : (G j).obj.obj (op V)),
      (c i).hom.app (op V) s = (c j).hom.app (op V) t → IsEmpty V.left)
    (T : Over S) (U : I → T.left.Opens) (hc : iSup U = ⊤)
    (t : ∀ i, (G i).obj.obj (op (openObject T (U i)))) (a : H.obj.obj (op T))
    (ha : ∀ i, (c i).hom.app _ (t i) = H.obj.map (openInclusion T (U i)).op a)
    (V : I → T.left.Opens) (hv : iSup V = ⊤)
    (s : ∀ i, (G i).obj.obj (op (openObject T (V i))))
    (hs : ∀ i, (c i).hom.app _ (s i) = H.obj.map (openInclusion T (V i)).op a) :
    ∀ i, V i = U i ∧ HEq (s i) (t i) := by
  have e : V = U := by
    funext i
    apply le_antisymm
    · intro z hz
      exact image_mem H G c hd T U hc t a ha (openInclusion T (V i)) i
        (s i) (hs i) ⟨z, hz⟩
    · intro z hz
      exact image_mem H G c hd T V hv s a hs (openInclusion T (U i)) i
        (t i) (ha i) ⟨z, hz⟩
  subst V
  intro i
  exact ⟨rfl, heq_of_eq (hi i _ ((hs i).trans (ha i).symm))⟩

/-- Factor the base map through its summand and identify its section (Tags 01HI, 0F15). -/
private theorem factor_section {S : Scheme.{u}} {I : Type w}
    (H : Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    (G : I → Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    (c : ∀ i, G i ⟶ H)
    (hi : ∀ i (V : Over S), Function.Injective ((c i).hom.app (op V)))
    (hd : ∀ i j, i ≠ j → ∀ (V : Over S)
      (s : (G i).obj.obj (op V)) (t : (G j).obj.obj (op V)),
      (c i).hom.app (op V) s = (c j).hom.app (op V) t → IsEmpty V.left)
    (T : Over S) (U : I → T.left.Opens) (hc : iSup U = ⊤)
    (t : ∀ i, (G i).obj.obj (op (openObject T (U i)))) (a : H.obj.obj (op T))
    (ha : ∀ i, (c i).hom.app _ (t i) = H.obj.map (openInclusion T (U i)).op a)
    {Z : Over S} (b : Z ⟶ T) (i : I) (s : (G i).obj.obj (op Z))
    (hs : (c i).hom.app _ s = H.obj.map b.op a) :
    ∃ d : Z ⟶ openObject T (U i), d ≫ openInclusion T (U i) = b ∧
      (G i).obj.map d.op (t i) = s := by
  have hr : Set.range b.left ⊆ Set.range (U i).ι := by
    rw [Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact image_mem H G c hd T U hc t a ha b i s hs z
  let d : Z ⟶ openObject T (U i) :=
    Over.homMk (IsOpenImmersion.lift (U i).ι b.left hr) (by
      change IsOpenImmersion.lift (U i).ι b.left hr ≫ ((U i).ι ≫ T.hom) = Z.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
  have hf : d ≫ openInclusion T (U i) = b := by
    ext
    exact IsOpenImmersion.lift_fac _ _ hr
  refine ⟨d, hf, hi i Z ?_⟩
  rw [NatTrans.naturality_apply, ha i, ← Functor.map_comp_apply, ← op_comp, hf, hs]

/-- Recognition of the summand pullbacks from a supplied clopen partition.
Source: Stacks Project, spaces.tex, Tags 0F15 and 02WO
(blueprint: lem-trf-disjoint-sheaf-partition-pullbacks).

The `IsPullback` square uses the Yoneda transformations of the specified sections.
Its component at Z is precisely d ↦ (d ≫ inclusion, G_i(d)(a_i)); thus it states
both the displayed bijection onto pairs (b,s) with c_i(s)=H(b)(a), and its
naturality, hence the asserted isomorphism of presheaves. `ULift` merely puts
representables in the same universe as the set-valued sheaves; the value universe
`max u v` contains the scheme universe `u` and covers both `Type u` (v = 0) and
larger set universes, as in the citer lem-trf-fppf-sheaf-coproduct-partition. `HEq` compares
sections after the preceding equality of canonical open subschemes.

Proof, following the six steps of the node:
1. Open covers are fppf covers: open immersions are etale by
   lem-weil-pbc-open-immersion-etale, hence flat and locally finitely presented
   by def-weil-etale-morphism. The empty cover and the sheaf equalizer axiom
   (def-weil-pbc-sites-and-cohomology) give unique sections on empty schemes.
2. The images c_i(a_i) agree on empty pairwise intersections; on self
   intersections use functoriality. The sheaf axiom glues them uniquely to a.
3. For a second partition V, on U_i ∩ V_j the two images equal a. Disjointness
   of the sheaf maps makes this intersection empty when i ≠ j. Covering gives
   U_i ⊆ V_i and conversely. Equal opens define the same open subscheme by
   def-weil-open-immersion; injectivity then identifies the sections.
4. Given (b,s) in the fibre set, pull the opens U_j back to Z and use
   lem-weil-pbc-morphism-factors-through-open-subscheme to obtain q_j.
   Naturality identifies c_i(s) and c_j(q_j^*a_j) there. All pieces except i
   are empty, so b factors uniquely through U_i. Injectivity gives s=d^*a_i.
5. Conversely d gives the stated pair by naturality. Unique factorization
   proves the inverse identities. Precomposition by r sends this pair to
   (r ≫ d ≫ inclusion, G_i(r)(G_i(d)(a_i))), proving naturality.
6. For arbitrary b the inverse images remain clopen, disjoint, and covering;
   the q_i^*a_i map to b^*a. Step 3 gives uniqueness on Z, and Step 2 gives
   converse gluing. Empty pieces use Step 1. For an empty index set the cover
   forces T empty, and any scheme mapping to T is empty as well. -/
theorem disjoint_sheaf_partition_pullbacks
    {S : Scheme.{u}} {I : Type w}
    (H : Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    (G : I → Sheaf (Scheme.fppfTopology.over S) (Type (max u v)))
    (c : ∀ i, G i ⟶ H)
    (_hinj : ∀ (i : I) (V : Over S), Function.Injective ((c i).hom.app (op V)))
    (_hdisj : ∀ (i j : I), i ≠ j → ∀ (V : Over S)
      (s : (G i).obj.obj (op V)) (t : (G j).obj.obj (op V)),
      (c i).hom.app (op V) s = (c j).hom.app (op V) t → IsEmpty V.left)
    (T : Over S) (U : I → T.left.Opens)
    (_hclosed : ∀ i, IsClosed (U i : Set T.left))
    (_hpairwise : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (_hcover : iSup U = ⊤)
    (a_i : ∀ i, (G i).obj.obj (op (openObject T (U i)))) :
    ∃ a : H.obj.obj (op T),
      (∀ i, (c i).hom.app (op (openObject T (U i))) (a_i i) =
        H.obj.map (openInclusion T (U i)).op a) ∧
      (∀ a' : H.obj.obj (op T),
        (∀ i, (c i).hom.app (op (openObject T (U i))) (a_i i) =
          H.obj.map (openInclusion T (U i)).op a') → a' = a) ∧
      (∀ (V : I → T.left.Opens), (∀ i, IsClosed (V i : Set T.left)) →
        Pairwise (fun i j ↦ Disjoint (V i) (V j)) → iSup V = ⊤ →
        ∀ (t : ∀ i, (G i).obj.obj (op (openObject T (V i)))),
        (∀ i, (c i).hom.app (op (openObject T (V i))) (t i) =
          H.obj.map (openInclusion T (V i)).op a) →
        ∀ i, V i = U i ∧ HEq (t i) (a_i i)) ∧
      (∀ i, IsPullback
        (uliftYoneda.{v}.map (openInclusion T (U i)))
        (uliftYonedaEquiv.{v}.symm (a_i i))
        (uliftYonedaEquiv.{v}.symm a) (c i).hom) ∧
      (∀ (Z : Over S) (b : Z ⟶ T),
        (∀ i, IsClosed (b.left ⁻¹ᵁ U i : Set Z.left)) ∧
        Pairwise (fun i j ↦ Disjoint (b.left ⁻¹ᵁ U i) (b.left ⁻¹ᵁ U j)) ∧
        (⨆ i, b.left ⁻¹ᵁ U i) = ⊤ ∧
        (∀ i, (c i).hom.app (op (openObject Z (b.left ⁻¹ᵁ U i)))
          ((G i).obj.map (openRestriction b (U i)).op (a_i i)) =
          H.obj.map (openInclusion Z (b.left ⁻¹ᵁ U i)).op (H.obj.map b.op a)) ∧
        (∀ (V : I → Z.left.Opens), (∀ i, IsClosed (V i : Set Z.left)) →
          Pairwise (fun i j ↦ Disjoint (V i) (V j)) → iSup V = ⊤ →
          ∀ (t : ∀ i, (G i).obj.obj (op (openObject Z (V i)))),
          (∀ i, (c i).hom.app (op (openObject Z (V i))) (t i) =
            H.obj.map (openInclusion Z (V i)).op (H.obj.map b.op a)) →
          ∀ i, V i = b.left ⁻¹ᵁ U i ∧
            HEq (t i) ((G i).obj.map (openRestriction b (U i)).op (a_i i)))) := by
  obtain ⟨a, ha, hu⟩ := glue H T U _hpairwise _hcover
    (fun i ↦ (c i).hom.app _ (a_i i))
  have hsec : ∀ i, (c i).hom.app _ (a_i i) =
      H.obj.map (openInclusion T (U i)).op a := fun i ↦ (ha i).symm
  refine ⟨a, hsec, ?_, ?_, ?_, ?_⟩
  · intro a' ha'
    exact hu a' (fun i ↦ (ha' i).symm)
  · intro V _ _ hv t ht
    exact partition_unique H G c _hinj _hdisj T U _hcover a_i a hsec V hv t ht
  · intro i
    apply IsPullback.of_forall_isPullback_app
    intro Z
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · ext d
      change H.obj.map (d.down ≫ openInclusion T (U i)).op a =
        (c i).hom.app _ ((G i).obj.map d.down.op (a_i i))
      rw [NatTrans.naturality_apply, hsec i, op_comp, Functor.map_comp_apply]
    · intro d e h
      apply ULift.ext
      apply Over.OverMorphism.ext
      apply (cancel_mono (U i).ι).mp
      exact congrArg (fun q ↦ q.down.left) h.1
    · intro b s hs
      change H.obj.map b.down.op a = (c i).hom.app _ s at hs
      obtain ⟨d, hd, ht⟩ := factor_section H G c _hinj _hdisj T U _hcover a_i a
        hsec b.down i s hs.symm
      exact ⟨ULift.up d, congrArg ULift.up hd, ht⟩
  · intro Z b
    have hc : (⨆ i, b.left ⁻¹ᵁ U i) = ⊤ := b.left.iSup_preimage_eq_top _hcover
    have hs : ∀ i, (c i).hom.app _
        ((G i).obj.map (openRestriction b (U i)).op (a_i i)) =
        H.obj.map (openInclusion Z (b.left ⁻¹ᵁ U i)).op (H.obj.map b.op a) :=
      fun i ↦ restrict_image H (G i) (c i) (U i) (a_i i) a (hsec i) b
    refine ⟨fun i ↦ (_hclosed i).preimage b.left.continuous, ?_, hc, hs, ?_⟩
    · intro i j hij
      apply disjoint_iff.mpr
      rw [← Hom.preimage_inf, (_hpairwise hij).eq_bot]
      exact b.left.preimage_bot
    · intro V _ _ hv t ht
      exact partition_unique H G c _hinj _hdisj Z (fun i ↦ b.left ⁻¹ᵁ U i) hc
        (fun i ↦ (G i).obj.map (openRestriction b (U i)).op (a_i i))
        (H.obj.map b.op a) hs V hv t ht

end AlgebraicGeometry.Scheme.FppfPartition
