/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Sites.SmallSheafCoproductLabels
import Sheaf.AlgebraicGeometry.FppfLabelledCoverDescent
import Sheaf.AlgebraicGeometry.DisjointSheafPartitionPullbacks
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Clopen partitions from coproducts of fppf sheaves

Source: Stacks Project, Spaces, Tags 0F15 and 02WO, and Sites, Tag 00WI
(blueprint: lem-trf-fppf-sheaf-coproduct-partition).

The auxiliary data record encodes the opens and their component sections. Coproduct
existence is asserted without assuming a sheafification instance on the big site.
The coefficient and index universe `max u v` includes the scheme universe `u`.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The open subscheme as an object over the base. Source: Stacks, Spaces, Tag 0F15
(blueprint: lem-trf-fppf-sheaf-coproduct-partition). -/
def fppfPartitionOpen {S : Scheme.{u}} (T : Over S) (U : T.left.Opens) : Over S :=
  Over.mk (U.ι ≫ T.hom)

/-- The inclusion of a partition piece over the base. Source: Stacks, Spaces, Tag 0F15
(blueprint: lem-trf-fppf-sheaf-coproduct-partition). -/
def fppfPartitionInclusion {S : Scheme.{u}} (T : Over S) (U : T.left.Opens) :
    fppfPartitionOpen T U ⟶ T :=
  Over.homMk U.ι

/-- Restriction of a test morphism to the inverse image of an open piece.
Source: Stacks, Spaces, Tags 0F15 and 02WO
(blueprint: lem-trf-fppf-sheaf-coproduct-partition). -/
noncomputable def fppfPartitionRestriction {S : Scheme.{u}} {Z T : Over S} (b : Z ⟶ T)
    (U : T.left.Opens) :
    fppfPartitionOpen Z (b.left ⁻¹ᵁ U) ⟶ fppfPartitionOpen T U :=
  Over.homMk (b.left ∣_ U)
    (by
      change (b.left ∣_ U) ≫ U.ι ≫ T.hom = (b.left ⁻¹ᵁ U).ι ≫ Z.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w])

/-- A clopen partition of a test scheme with a section in each summand sheaf.
Empty opens and empty index types are permitted. Source: Stacks, Spaces, Tags 0F15
and 02WO (blueprint: lem-trf-fppf-sheaf-coproduct-partition). -/
structure FppfCoproductPartition {S : Scheme.{u}} {I : Type (max u v)}
    (G : I → Sheaf (fppfTopology.over S) (Type (max u v))) (T : Over S) where
  /-- The open subschemes of the partition. -/
  opens : I → T.left.Opens
  /-- Each piece is also closed. -/
  isClosed : ∀ i, IsClosed (opens i : Set T.left)
  /-- Distinct pieces are disjoint. -/
  disjoint : Pairwise (fun i j ↦ Disjoint (opens i) (opens j))
  /-- The pieces cover the test scheme. -/
  covers : iSup opens = ⊤
  /-- The component section on each piece. -/
  sections : ∀ i, (G i).obj.obj (op (fppfPartitionOpen T (opens i)))

/-- The component sections have the prescribed image in the coproduct sheaf.
Source: Stacks, Spaces, Tag 0F15
(blueprint: lem-trf-fppf-sheaf-coproduct-partition). -/
def FppfCoproductPartition.MapsTo {S : Scheme.{u}} {I : Type (max u v)}
    {G : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {C : Sheaf (fppfTopology.over S) (Type (max u v))} (c : ∀ i, G i ⟶ C)
    {T : Over S} (d : FppfCoproductPartition G T) (a : C.obj.obj (op T)) : Prop :=
  ∀ i, (c i).hom.app (op (fppfPartitionOpen T (d.opens i))) (d.sections i) =
    C.obj.map (fppfPartitionInclusion T (d.opens i)).op a

private abbrev partitionCoverage (S : Scheme.{u}) :=
  fppfPrecoverage.comap (Over.forget S)

private theorem partitionCoverage_site (S : Scheme.{u}) :
    (partitionCoverage S).IsSiteForCoverings := by
  let J := partitionCoverage S
  have : fppfPrecoverage.HasIsos := by
    exact ⟨fun f ↦ zariskiPrecoverage_le_fppfPrecoverage _
      (Precoverage.mem_coverings_of_isIso f)⟩
  refine ⟨inferInstance, ?_, ?_⟩
  · intro X R T hR hT
    exact J.toPretopology.transitive R (fun _ f hf ↦ T f hf) hR
      (fun _ f hf ↦ hT _ f hf)
  · intro A X U a ha Y b
    refine ⟨fun i ↦ pullback b (a i), fun i ↦ pullback.fst _ _,
      fun i ↦ pullback.snd _ _, fun i ↦ IsPullback.of_hasPullback _ _, ?_⟩
    exact Precoverage.mem_coverings_of_isPullback a ha b _ _
      (fun i ↦ IsPullback.of_hasPullback _ _)

private theorem partitionCoverage_topology (S : Scheme.{u}) :
    (partitionCoverage S).toGrothendieck = fppfTopology.over S :=
  (over_toGrothendieck_eq_toGrothendieck_comap_forget fppfPrecoverage S).symm

private theorem partitionCoverage_empty (S : Scheme.{u}) (T : Over S) :
    (⊥ : Presieve T) ∈ partitionCoverage S T ↔ IsEmpty T.left := by
  constructor
  · intro h
    refine ⟨fun x ↦ ?_⟩
    change (⊥ : Presieve T).map (Over.forget S) ∈ fppfPrecoverage T.left at h
    rw [Presieve.map_bot] at h
    obtain ⟨Y, g, hg, _⟩ := JointlySurjective.exists_eq
      (K := precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) ⊥ h x
    simp at hg
  · intro h
    have := h
    change (⊥ : Presieve T).map (Over.forget S) ∈ fppfPrecoverage T.left
    rw [Presieve.map_bot]
    exact bot_mem_precoverage _ _

private theorem partition_exists {S : Scheme.{u}} {I : Type*}
    (G : I → Sheaf (fppfTopology.over S) (Type (max u v)))
    (C : Sheaf (fppfTopology.over S) (Type (max u v))) (c : ∀ i, G i ⟶ C)
    (hinj : ∀ i T, Function.Injective ((c i).hom.app (op T)))
    (hdisj : ∀ i j, i ≠ j → ∀ (T : Over S)
      (s : (G i).obj.obj (op T)) (t : (G j).obj.obj (op T)),
      (c i).hom.app (op T) s = (c j).hom.app (op T) t → IsEmpty T.left)
    (hlocal : ∀ (T : Over S) (a : C.obj.obj (op T)),
      ∃ R : Presieve T, R.map (Over.forget S) ∈ fppfPrecoverage T.left ∧
        ∀ (W : Over S) (f : W ⟶ T), R f →
          ∃ i, ∃ s : (G i).obj.obj (op W),
            (c i).hom.app (op W) s = C.obj.map f.op a)
    (T : Over S) (a : C.obj.obj (op T)) :
    ∃ (V : I → T.left.Opens), (∀ i, IsClosed (V i : Set T.left)) ∧
      Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧ iSup V = ⊤ ∧
      ∃ sections : ∀ i, (G i).obj.obj (op (fppfPartitionOpen T (V i))),
        (∀ i, (c i).hom.app (op (fppfPartitionOpen T (V i))) (sections i) =
          C.obj.map (fppfPartitionInclusion T (V i)).op a) ∧
        Nonempty (IsColimit (Cofan.mk T.left (fun i ↦ (V i).ι))) := by
  classical
  obtain ⟨R, hR, hlocal⟩ := hlocal T a
  let A := R.uncurry
  let U : A → Over S := fun x ↦ x.1.1
  let g : ∀ x : A, U x ⟶ T := fun x ↦ x.1.2
  have hg (x : A) := hlocal (U x) (g x) x.2
  choose label sec hsec using hg
  have hcover : Presieve.ofArrows (fun x ↦ (U x).left) (fun x ↦ (g x).left) ∈
      fppfPrecoverage T.left := by
    have he : Presieve.ofArrows U g = R := by
      funext W f
      apply propext
      constructor
      · rintro ⟨x⟩
        exact x.2
      · intro hf
        exact Presieve.ofArrows.mk (show A from ⟨⟨W, f⟩, hf⟩)
    have hm := Presieve.map_ofArrows (F := Over.forget S) g
    rw [he] at hm
    exact hm ▸ hR
  have heq (x y : A) :
      (c (label x)).hom.app (op (pullback (g x) (g y)))
          ((G (label x)).obj.map (pullback.fst (g x) (g y)).op (sec x)) =
        (c (label y)).hom.app (op (pullback (g x) (g y)))
          ((G (label y)).obj.map (pullback.snd (g x) (g y)).op (sec y)) := by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hsec, hsec,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      pullback.condition]
  let s : ∀ (i : I) (x : A), label x = i → (G i).obj.obj (op (U x)) :=
    fun i x h ↦ h ▸ sec x
  have hsimage (i : I) (x : A) (hx : label x = i) :
      (c i).hom.app (op (U x)) (s i x hx) = C.obj.map (g x).op a := by
    subst i
    exact hsec x
  obtain ⟨V, _, hclosed, hpair, hcov, hcolim, h, hfac, hdesc⟩ :=
    fppf_labelled_cover_descent T U g hcover label
      (fun x y hxy ↦ hdisj _ _ hxy _ _ _ (heq x y)) G s (by
        intro i x y hx hy
        apply hinj i _
        rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
          hsimage, hsimage, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
          ← op_comp, ← op_comp, pullback.condition])
  choose sections hsections huniq using hdesc
  obtain ⟨a', hamap, hauniq, _, _, _⟩ :=
    FppfPartition.disjoint_sheaf_partition_pullbacks C G c hinj hdisj T V
      hclosed hpair hcov sections
  have haa : a = a' := by
    apply (((isSheaf_iff_isSheaf_of_type _ _).mp C.property).isSheafFor R
      (by
        change Sieve.functorPushforward (Over.forget S) (Sieve.generate R) ∈ fppfTopology T.left
        rw [← Sieve.generate_map_eq_functorPushforward]
        exact Precoverage.generate_mem_toGrothendieck hR)).isSeparatedFor.ext
    intro W f hf
    let x : A := ⟨⟨W, f⟩, hf⟩
    have hf' := hfac (label x) x rfl
    have hs := hsections (label x) x rfl
    have hh : (c (label x)).hom.app (op (Over.mk ((V (label x)).ι ≫ T.hom)))
        (sections (label x)) = C.obj.map (Over.homMk (V (label x)).ι).op a' :=
      hamap (label x)
    have hn := (c (label x)).hom.naturality_apply (h (label x) x rfl).op
      (sections (label x))
    dsimp [s] at hs
    rw [hs, hsec x, hh, ← Functor.map_comp_apply, ← op_comp, hf'] at hn
    exact hn
  exact ⟨V, hclosed, hpair, hcov, sections, haa ▸ hamap, hcolim⟩

private theorem small_partition_coproduct {S : Scheme.{u}} {I : Type (max u v)}
    (G : I → Sheaf (fppfTopology.over S) (Type (max u v))) :
    ∃ (C : Sheaf (fppfTopology.over S) (Type (max u v))) (c : ∀ i, G i ⟶ C),
      Nonempty (IsColimit (Cofan.mk C c)) ∧
      (∀ i T, Function.Injective ((c i).hom.app (op T))) ∧
      (∀ i j, i ≠ j → ∀ (T : Over S)
        (s : (G i).obj.obj (op T)) (t : (G j).obj.obj (op T)),
        (c i).hom.app (op T) s = (c j).hom.app (op T) t → IsEmpty T.left) ∧
      (∀ (T : Over S) (a : C.obj.obj (op T)),
        ∃ R : Presieve T, R.map (Over.forget S) ∈ fppfPrecoverage T.left ∧
          ∀ (W : Over S) (f : W ⟶ T), R f →
            ∃ i, ∃ s : (G i).obj.obj (op W),
              (c i).hom.app (op W) s = C.obj.map f.op a) := by
  classical
  let J := fppfTopology.over S
  let F := sheafCompose J uliftFunctor.{u + 1, max u v}
  let G' := fun i ↦ F.obj (G i)
  have htop := partitionCoverage_topology S
  have hex := small_sheaf_coproduct_labels (partitionCoverage S)
    (partitionCoverage_site S) (I := I)
  rw [htop] at hex
  obtain ⟨H, eta, c', hceta, _, hcolim, _, hinj, _, hlocal, hmix, _, _⟩ := hex G'
  have hdisj : ∀ i j, i ≠ j → ∀ (T : Over S)
      (s : (G' i).obj.obj (op T)) (t : (G' j).obj.obj (op T)),
      (c' i).hom.app (op T) s = (c' j).hom.app (op T) t → IsEmpty T.left := by
    intro i j hij T s t he
    exact (partitionCoverage_empty S T).mp (hmix T i j s t hij he)
  have hloc : ∀ (T : Over S) (a : H.obj.obj (op T)),
      ∃ R : Presieve T, R.map (Over.forget S) ∈ fppfPrecoverage T.left ∧
        ∀ (W : Over S) (f : W ⟶ T), R f →
          ∃ i, ∃ s : (G' i).obj.obj (op W),
            (c' i).hom.app (op W) s = H.obj.map f.op a := by
    intro T a
    obtain ⟨R, hR, hr⟩ := hlocal T a
    exact ⟨R, hR, fun W f hf ↦ by
      obtain ⟨i, s, hs⟩ := hr W f hf
      exact ⟨i, s, (hceta i W s).trans hs⟩⟩
  have hsmall (T : Over S) : Small.{max u v} (H.obj.obj (op T)) := by
    have hparts := partition_exists.{u, max (u + 1) v, max u v} G' H c' hinj hdisj hloc T
    choose V hclosed hpair hcover sec hsec hcol using hparts
    let encode : H.obj.obj (op T) → FppfCoproductPartition G T := fun a ↦
      ⟨V a, hclosed a, hpair a, hcover a, fun i ↦ (sec a i).down⟩
    apply small_of_injective (f := encode)
    intro a b hab
    obtain ⟨z, _, hz, _, _, _⟩ :=
      FppfPartition.disjoint_sheaf_partition_pullbacks.{u, max (u + 1) v, max u v}
        H G' c' hinj hdisj T
        (encode a).opens (encode a).isClosed (encode a).disjoint (encode a).covers
        (fun i ↦ ULift.up ((encode a).sections i))
    apply (hz a (hsec a)).trans
    apply (hz b ?_).symm
    change ∀ i, (c' i).hom.app (op (fppfPartitionOpen T ((encode a).opens i)))
      (ULift.up ((encode a).sections i)) =
      H.obj.map (fppfPartitionInclusion T ((encode a).opens i)).op b
    rw [hab]
    exact hsec b
  have : FunctorToTypes.Small.{max u v} H.obj := fun (T : (Over S)ᵒᵖ) ↦ hsmall T.unop
  let Q := FunctorToTypes.shrink.{max u v} H.obj
  have hQ : Presheaf.IsSheaf J Q := by
    apply (isSheaf_iff_isSheaf_of_type _ _).mpr
    apply Presieve.isSheaf_of_nat_equiv (fun {T} ↦ equivShrink (H.obj.obj (op T)))
      (fun {_ _} f x ↦ by simp [FunctorToTypes.shrink])
    exact (isSheaf_iff_isSheaf_of_type _ _).mp H.property
  let C : Sheaf J (Type (max u v)) := ⟨Q, hQ⟩
  let e : H ≅ F.obj C :=
    ObjectProperty.isoMk _ (NatIso.ofComponents
      (fun T ↦ (Equiv.trans (equivShrink (H.obj.obj T)) Equiv.ulift.{u + 1, max u v}.symm).toIso)
      (by
        intro T W f
        apply ConcreteCategory.hom_ext
        intro x
        change ULift.up ((equivShrink (H.obj.obj W)) (H.obj.map f x)) =
          ULift.up ((equivShrink (H.obj.obj W))
            (H.obj.map f ((equivShrink (H.obj.obj T)).symm
              ((equivShrink (H.obj.obj T)) x))))
        simp))
  let c : ∀ i, G i ⟶ C := fun i ↦ F.preimage (c' i ≫ e.hom)
  have hc (i : I) : F.map (c i) = c' i ≫ e.hom := F.map_preimage _
  have hecol : IsColimit (Cofan.mk (F.obj C) (fun i ↦ F.map (c i))) := by
    refine Cofan.IsColimit.mk _
      (fun t ↦ e.inv ≫ Cofan.IsColimit.desc hcolim.some (fun i ↦ t.inj i)) ?_ ?_
    · intro t i
      change F.map (c i) ≫ e.inv ≫ _ = _
      rw [hc]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact Cofan.IsColimit.fac hcolim.some _ i
    · intro t m hm
      apply (cancel_epi e.hom).mp
      simp only [Iso.hom_inv_id_assoc]
      apply Cofan.IsColimit.hom_ext hcolim.some
      intro i
      change c' i ≫ e.hom ≫ m = c' i ≫ Cofan.IsColimit.desc hcolim.some _
      rw [← Category.assoc, ← hc]
      exact (hm i).trans (Cofan.IsColimit.fac hcolim.some _ i).symm
  have hcol : IsColimit (Cofan.mk C c) := by
    refine Cofan.IsColimit.mk _
      (fun t ↦ F.preimage (Cofan.IsColimit.desc hecol (fun i ↦ F.map (t.inj i))))
      ?_ ?_
    · intro t i
      apply F.map_injective
      rw [F.map_comp, F.map_preimage]
      exact Cofan.IsColimit.fac hecol _ i
    · intro t m hm
      apply F.map_injective
      rw [F.map_preimage]
      apply Cofan.IsColimit.hom_ext hecol
      intro i
      change F.map (c i) ≫ F.map m = _
      have hmi : c i ≫ m = t.inj i := hm i
      rw [← F.map_comp, hmi]
      exact (Cofan.IsColimit.fac hecol (fun j ↦ F.map (t.inj j)) i).symm
  have happ (i : I) (T : Over S) (s : (G i).obj.obj (op T)) :
      ULift.up ((c i).hom.app (op T) s) =
        e.hom.hom.app (op T) ((c' i).hom.app (op T) (ULift.up s)) :=
    congrArg (fun f : F.obj (G i) ⟶ F.obj C ↦
      f.hom.app (op T) (ULift.up s)) (hc i)
  have heinj (T : Over S) : Function.Injective (e.hom.hom.app (op T)) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (op T))).1
  refine ⟨C, c, ⟨hcol⟩, ?_, ?_, ?_⟩
  · intro i T s t hst
    apply ULift.up_injective
    apply hinj i T
    apply heinj T
    rw [← happ, ← happ, hst]
  · intro i j hij T s t hst
    apply hdisj i j hij T (ULift.up s) (ULift.up t)
    apply heinj T
    rw [← happ, ← happ, hst]
  · intro T a
    obtain ⟨R, hR, hr⟩ := hloc T (e.inv.hom.app (op T) (ULift.up a))
    refine ⟨R, hR, ?_⟩
    intro W f hf
    obtain ⟨i, s, hs⟩ := hr W f hf
    refine ⟨i, s.down, ?_⟩
    apply ULift.up_injective
    rw [happ]
    change e.hom.hom.app (op W) ((c' i).hom.app (op W) s) = _
    rw [hs, e.hom.hom.naturality_apply]
    have heid := congrArg (fun k : F.obj C ⟶ F.obj C ↦
      k.hom.app (op T) (ULift.up a)) e.inv_hom_id
    exact congrArg ((F.obj C).obj.map f.op) heid

/-- Coproducts of fppf sheaves exist, with monic coprojections, and their sections
correspond uniquely to clopen partitions with component sections. The summand squares
are cartesian, the correspondence commutes with arbitrary test morphisms, and an empty
coproduct has one section precisely on empty schemes.
Source: Stacks, Spaces, Tags 0F15 and 02WO; Sites, Tags 00WI and 00WK
(blueprint: lem-trf-fppf-sheaf-coproduct-partition).

Proof:
1. Form the labelled coproduct presheaf and sheafify it, using
   lem-trf-sieve-set-sheafification-exists. The adjunction identifies maps from its
   sheafification with families of maps from the summands, proving the colimit property.
2. By lem-weil-pbc-site-sheafification-sections-local every section locally has a label.
   Local equality of two images forces equal labels unless the test scheme is empty;
   for equal labels the sheaf condition gives equal sections. This proves monicity,
   injectivity on sections, and emptiness of mixed intersections. Every sheaf has one
   section on the empty scheme, by its empty covering.
3. The images of the labelled covering members are open by lem-weil-pbc-flat-lfp-open.
   Members with distinct labels have empty fibre product. Surjective base change
   (lem-weil-pbc-surjective-base-change) then shows that their images are disjoint.
4. Unite the images of each label. They cover the test scheme and are pairwise disjoint.
   Each complement is the union of the other opens, so each piece is closed. Scheme
   morphism gluing (lem-weil-pbc-scheme-morphism-gluing) gives the scheme coproduct.
5. On each piece glue its local labelled sections, using injectivity on sections for
   agreement. The sheaf condition gives the required equality with the original section.
6. Compare with another partition on all intersections. Mixed intersections are empty,
   forcing the opens to coincide; injectivity then identifies their component sections.
7. A pair consisting of a test map and a summand section with equal images factors
   uniquely through the corresponding open: all other inverse image pieces are empty.
   This factorization is natural in the test object and proves the cartesian square.
8. Inverse images of the opens and restrictions of the sections give the partition
   after any test morphism, by uniqueness. Conversely the images of any component
   sections glue uniquely, since their mixed overlaps are empty.
9. For an empty index type the coproduct presheaf has no sections. Local representatives
   force an empty covering, hence an empty test scheme. On the empty scheme the empty
   covering gives exactly one section. -/
theorem fppfSheaf_coproduct_partition {S : Scheme.{u}} {I : Type (max u v)}
    (G : I → Sheaf (fppfTopology.over S) (Type (max u v))) :
    (∃ (C : Sheaf (fppfTopology.over S) (Type (max u v))) (c : ∀ i, G i ⟶ C),
      Nonempty (IsColimit (Cofan.mk C c))) ∧
    (∀ (C : Sheaf (fppfTopology.over S) (Type (max u v))) (c : ∀ i, G i ⟶ C),
      IsColimit (Cofan.mk C c) →
      (∀ i, Mono (c i) ∧ ∀ T : Over S, Function.Injective ((c i).hom.app (op T))) ∧
      (∀ (T : Over S) (a : C.obj.obj (op T)),
        ∃! d : FppfCoproductPartition G T, d.MapsTo c a) ∧
      (∀ (T : Over S) (a : C.obj.obj (op T)) (d : FppfCoproductPartition G T),
        d.MapsTo c a →
        (Nonempty (IsColimit (Cofan.mk T.left (fun i ↦ (d.opens i).ι)))) ∧
        (∀ i, IsPullback
          (uliftYoneda.{v}.map (fppfPartitionInclusion T (d.opens i)))
          (uliftYonedaEquiv.{v}.symm (d.sections i))
          (uliftYonedaEquiv.{v}.symm a) (c i).hom) ∧
        (∀ (Z : Over S) (b : Z ⟶ T),
          ∃ e : FppfCoproductPartition G Z,
            e.MapsTo c (C.obj.map b.op a) ∧
            ∀ i, e.opens i = b.left ⁻¹ᵁ d.opens i ∧
              HEq (e.sections i)
                ((G i).obj.map (fppfPartitionRestriction b (d.opens i)).op (d.sections i)))) ∧
      (∀ (T : Over S) (d : FppfCoproductPartition G T),
        ∃! a : C.obj.obj (op T), d.MapsTo c a) ∧
      (IsEmpty I → ∀ T : Over S,
        (IsEmpty T.left → Nonempty (Unique (C.obj.obj (op T)))) ∧
        (Nonempty T.left → IsEmpty (C.obj.obj (op T))))) := by
  classical
  obtain ⟨C₀, c₀, hcol₀, hinj₀, hdisj₀, hlocal₀⟩ := small_partition_coproduct G
  refine ⟨⟨C₀, c₀, hcol₀⟩, ?_⟩
  intro C c hcol
  let e : C₀ ≅ C := hcol₀.some.coconePointUniqueUpToIso hcol
  have hc (i : I) : c₀ i ≫ e.hom = c i :=
    hcol₀.some.comp_coconePointUniqueUpToIso_hom hcol ⟨i⟩
  have happ (i : I) (T : Over S) (s : (G i).obj.obj (op T)) :
      e.hom.hom.app (op T) ((c₀ i).hom.app (op T) s) =
        (c i).hom.app (op T) s :=
    ConcreteCategory.congr_hom
      (congrArg (fun f : G i ⟶ C ↦ f.hom.app (op T)) (hc i)) s
  have heinj (T : Over S) : Function.Injective (e.hom.hom.app (op T)) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (op T))).1
  have hinj (i : I) (T : Over S) : Function.Injective ((c i).hom.app (op T)) := by
    intro s t hst
    exact hinj₀ i T (heinj T (by rw [happ, happ, hst]))
  have hdisj : ∀ i j, i ≠ j → ∀ (T : Over S)
      (s : (G i).obj.obj (op T)) (t : (G j).obj.obj (op T)),
      (c i).hom.app (op T) s = (c j).hom.app (op T) t → IsEmpty T.left := by
    intro i j hij T s t hst
    exact hdisj₀ i j hij T s t (heinj T (by rw [happ, happ, hst]))
  have hlocal : ∀ (T : Over S) (a : C.obj.obj (op T)),
      ∃ R : Presieve T, R.map (Over.forget S) ∈ fppfPrecoverage T.left ∧
        ∀ (W : Over S) (f : W ⟶ T), R f →
          ∃ i, ∃ s : (G i).obj.obj (op W),
            (c i).hom.app (op W) s = C.obj.map f.op a := by
    intro T a
    obtain ⟨R, hR, hr⟩ := hlocal₀ T (e.inv.hom.app (op T) a)
    refine ⟨R, hR, ?_⟩
    intro W f hf
    obtain ⟨i, s, hs⟩ := hr W f hf
    refine ⟨i, s, ?_⟩
    rw [← happ, hs, e.hom.hom.naturality_apply]
    have heid := ConcreteCategory.congr_hom
      (congrArg (fun k : C ⟶ C ↦ k.hom.app (op T)) e.inv_hom_id) a
    exact congrArg (C.obj.map f.op) heid
  have hex (T : Over S) (a : C.obj.obj (op T)) :
      ∃ d : FppfCoproductPartition G T, d.MapsTo c a ∧
        Nonempty (IsColimit (Cofan.mk T.left (fun i ↦ (d.opens i).ι))) := by
    obtain ⟨V, hv, hp, hc, s, hs, hcol⟩ := partition_exists G C c hinj hdisj hlocal T a
    exact ⟨⟨V, hv, hp, hc, s⟩, hs, hcol⟩
  have hdata (T : Over S) (d : FppfCoproductPartition G T) :=
    FppfPartition.disjoint_sheaf_partition_pullbacks C G c hinj hdisj T
      d.opens d.isClosed d.disjoint d.covers d.sections
  have hdeq (T : Over S) (a : C.obj.obj (op T))
      (d e : FppfCoproductPartition G T) (hd : d.MapsTo c a) (he : e.MapsTo c a) :
      e = d := by
    obtain ⟨a', ha', huniq, hpart, _, _⟩ := hdata T d
    have haa : a = a' := huniq a hd
    have hi := hpart e.opens e.isClosed e.disjoint e.covers e.sections (haa ▸ he)
    have hopens : e.opens = d.opens := funext fun i ↦ (hi i).1
    have hsec : HEq e.sections d.sections := by
      cases d
      cases e
      dsimp only at hopens hi ⊢
      cases hopens
      exact heq_of_eq (funext fun i ↦ eq_of_heq (hi i).2)
    cases d
    cases e
    dsimp only at hopens hsec ⊢
    cases hopens
    cases hsec
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, hinj i⟩
    refine ⟨fun {Z} f g hfg ↦ ?_⟩
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext T
    apply ConcreteCategory.hom_ext
    intro x
    exact hinj i T.unop
      (ConcreteCategory.congr_hom
        (congrArg (fun k : Z ⟶ C ↦ k.hom.app T) hfg) x)
  · intro T a
    obtain ⟨d, hd, _⟩ := hex T a
    exact ⟨d, hd, fun e he ↦ hdeq T a d e hd he⟩
  · intro T a d hd
    obtain ⟨d', hd', hcol'⟩ := hex T a
    have heq := hdeq T a d d' hd hd'
    subst d'
    obtain ⟨a', ha', huniq, _, hpb, hbase⟩ := hdata T d
    have haa : a = a' := huniq a hd
    subst a'
    refine ⟨hcol', hpb, ?_⟩
    intro Z b
    obtain ⟨hclosed, hpair, hcov, hs, _⟩ := hbase Z b
    refine ⟨⟨fun i ↦ b.left ⁻¹ᵁ d.opens i, hclosed, hpair, hcov,
      fun i ↦ (G i).obj.map (fppfPartitionRestriction b (d.opens i)).op (d.sections i)⟩,
      hs, fun i ↦ ⟨rfl, HEq.rfl⟩⟩
  · intro T d
    obtain ⟨a, ha, huniq, _⟩ := hdata T d
    exact ⟨a, ha, huniq⟩
  · intro hI T
    have := hI
    constructor
    · intro hT
      have hempty : (⊥ : Sieve T) ∈ fppfTopology.over S T := by
        rw [← partitionCoverage_topology S]
        simpa using Precoverage.generate_mem_toGrothendieck
          ((partitionCoverage_empty S T).mpr hT)
      have hsheaf := ((isSheaf_iff_isSheaf_of_type _ _).mp C.property) ⊥ hempty
      let x : Presieve.FamilyOfElements C.obj (⊥ : Sieve T).arrows :=
        fun W f hf ↦ False.elim hf
      have hx : x.Compatible := by intro W V Z g h f k hf; exact False.elim hf
      obtain ⟨a, ha, huniq⟩ := hsheaf x hx
      exact ⟨⟨⟨a⟩, fun b ↦ huniq b (by intro W f hf; exact False.elim hf)⟩⟩
    · intro hT
      refine ⟨fun a ↦ ?_⟩
      obtain ⟨d, _, _⟩ := hex T a
      have hc := d.covers
      rw [iSup_of_empty] at hc
      obtain ⟨x⟩ := hT
      have hx : x ∈ (⊥ : T.left.Opens) := hc.symm ▸ (show x ∈ (⊤ : T.left.Opens) from trivial)
      exact hx

end AlgebraicGeometry.Scheme
