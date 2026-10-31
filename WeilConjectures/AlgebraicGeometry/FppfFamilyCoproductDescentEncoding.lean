/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeCoverDescentDatum
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Encoding family scheme descent by its coproduct

Source: Stacks Project, Descent, Tags 023V and 023X; Topologies, Tags 021P and 022B
(blueprint: lem-trf-fppf-family-coproduct-descent-encoding).

The comparison cofans record the canonical coproduct identifications, including their
projections, without making an additional choice of coproduct for the overlap families.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical double-product cofan. Its legs preserve the two projections by construction.
Source: Stacks Project, Descent, Tag 023X
(blueprint: lem-trf-fppf-family-coproduct-descent-encoding). -/
noncomputable def schemeCoproductPairCofan
    {I J : Type (u + 1)} {T : Scheme.{u}} {X : I → Scheme.{u}} {Y : J → Scheme.{u}}
    (f : ∀ i, X i ⟶ T) (g : ∀ j, Y j ⟶ T)
    [HasCoproduct X] [HasCoproduct Y] :
    Cofan (fun ij : I × J ↦ pullback (f ij.1) (g ij.2)) :=
  Cofan.mk (pullback (Sigma.desc f) (Sigma.desc g))
    (fun ij ↦ pullback.map (f ij.1) (g ij.2) (Sigma.desc f) (Sigma.desc g)
      (Sigma.ι X ij.1) (Sigma.ι Y ij.2) (𝟙 T)
      (by simp only [Category.comp_id, Sigma.ι_desc])
      (by simp only [Category.comp_id, Sigma.ι_desc]))

/-- The canonical triple-product cofan, with left-associated fibre products. Its legs retain
all three coordinates, so its projections are the canonical ones of the double-product cofans.
Source: Stacks Project, Descent, Tag 023X
(blueprint: lem-trf-fppf-family-coproduct-descent-encoding). -/
noncomputable def schemeCoproductTripleCofan
    {I J K : Type (u + 1)} {T : Scheme.{u}}
    {X : I → Scheme.{u}} {Y : J → Scheme.{u}} {Z : K → Scheme.{u}}
    (f : ∀ i, X i ⟶ T) (g : ∀ j, Y j ⟶ T) (h : ∀ k, Z k ⟶ T)
    [HasCoproduct X] [HasCoproduct Y] [HasCoproduct Z] :
    Cofan (fun ijk : (I × J) × K ↦
      pullback (pullback.fst (f ijk.1.1) (g ijk.1.2) ≫ f ijk.1.1) (h ijk.2)) :=
  Cofan.mk
    (pullback (pullback.fst (Sigma.desc f) (Sigma.desc g) ≫ Sigma.desc f) (Sigma.desc h))
    (fun ijk ↦ pullback.map
      (pullback.fst (f ijk.1.1) (g ijk.1.2) ≫ f ijk.1.1) (h ijk.2)
      (pullback.fst (Sigma.desc f) (Sigma.desc g) ≫ Sigma.desc f) (Sigma.desc h)
      ((schemeCoproductPairCofan f g).ι.app ⟨ijk.1⟩) (Sigma.ι Z ijk.2) (𝟙 T)
      (by simp [schemeCoproductPairCofan, pullback.map, Category.assoc])
      (by simp only [Category.comp_id, Sigma.ι_desc]))

/-- The coproduct of the local schemes, with its induced map to the coproduct of the bases.
Source: Stacks Project, Descent, Tag 023X
(blueprint: lem-trf-fppf-family-coproduct-descent-encoding). -/
noncomputable def SchemeCoverDescentDatum.coproductScheme
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)] : Over (∐ U) :=
  Over.mk (CategoryTheory.Limits.Sigma.map (fun i ↦ (F.localScheme i).hom))

/-- Include a represented local point into the coproduct of the local schemes.
Source: Stacks Project, Descent, Tag 023X
(blueprint: lem-trf-fppf-family-coproduct-descent-encoding). -/
noncomputable def SchemeCoverDescentDatum.coproductPoint
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B : Scheme.{u}} (i : I) (a : B ⟶ U i)
    (x : (F.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 B))))) :
    Over.mk (a ≫ Sigma.ι U i) ⟶
      F.coproductScheme :=
  Over.homMk
    (((F.representation i).homEquiv.symm x).left ≫
      Sigma.ι (fun i ↦ (F.localScheme i).left) i)
    (by
      change (((F.representation i).homEquiv.symm x).left ≫
        Sigma.ι (fun i ↦ (F.localScheme i).left) i) ≫
          CategoryTheory.Limits.Sigma.map (fun i ↦ (F.localScheme i).hom) = a ≫ Sigma.ι U i
      rw [Category.assoc, Sigma.ι_map]
      simpa only [Over.map_obj_left, Over.mk_left, Over.map_obj_hom, Over.mk_hom,
        Category.id_comp, ← Category.assoc] using
        congrArg (fun k ↦ k ≫ Sigma.ι U i)
          (Over.w ((F.representation i).homEquiv.symm x)))

private theorem coproduct_support_small {I : Type (u + 1)}
    (X : I → Scheme.{u}) [HasCoproduct X] : Small.{u} {i // Nonempty (X i)} := by
  classical
  let x (i : {i // Nonempty (X i)}) : X i := i.property.some
  let a (i : I) : (∐ X) ⟶ (∐ X) ⨿ (∐ X) :=
    Sigma.desc fun j ↦ if j = i then Sigma.ι X j ≫ coprod.inl
      else Sigma.ι X j ≫ coprod.inr
  apply small_of_injective (f := fun i : {i // Nonempty (X i)} ↦ Sigma.ι X i.val (x i))
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun z ↦ a i.val z) hij
  have hi : Sigma.ι X i.val ≫ a i.val = Sigma.ι X i.val ≫ coprod.inl := by
    simp [a]
  have hj : Sigma.ι X j.val ≫ a i.val = Sigma.ι X j.val ≫ coprod.inr := by
    simp [a, Ne.symm hne]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hi, hj] at he
  exact inl_ne_inr _ _ _ _ he

private noncomputable def cofanNonemptySupport {I : Type (u + 1)}
    {X : I → Scheme.{u}} (c : Cofan X) (hc : IsColimit c) :
    IsColimit (Cofan.mk c.pt (fun i : {i // Nonempty (X i)} ↦ c.inj i.val)) := by
  classical
  let extend (s : Cofan (fun i : {i // Nonempty (X i)} ↦ X i.val)) : Cofan X :=
    Cofan.mk s.pt fun i ↦ if h : Nonempty (X i) then s.inj ⟨i, h⟩
      else @IsInitial.to _ _ _ (@isInitialOfIsEmpty (X i) ⟨fun x ↦ h ⟨x⟩⟩) s.pt
  refine Cofan.IsColimit.mk _ (fun s ↦ hc.desc (extend s)) ?_ ?_
  · intro s i
    simp [extend, i.property]
  · intro s m hm
    apply hc.hom_ext
    rintro ⟨i⟩
    change c.inj i ≫ m = c.inj i ≫ hc.desc (extend s)
    rw [show c.inj i ≫ hc.desc (extend s) = (extend s).inj i from
      hc.fac (extend s) ⟨i⟩]
    by_cases h : Nonempty (X i)
    · simpa [extend, h] using hm ⟨i, h⟩
    · have : IsEmpty (X i) := ⟨fun x ↦ h ⟨x⟩⟩
      exact isInitialOfIsEmpty.hom_ext _ _

private theorem coproduct_geometry {I : Type (u + 1)}
    (X : I → Scheme.{u}) [HasCoproduct X] :
    (∀ i, IsOpenImmersion (Sigma.ι X i)) ∧
    (∀ z : (∐ X : Scheme.{u}), ∃ i x, Sigma.ι X i x = z) ∧
    (∀ i j, i ≠ j → Disjoint (Set.range (Sigma.ι X i)) (Set.range (Sigma.ι X j))) := by
  classical
  have := coproduct_support_small X
  let Y := fun i : {i // Nonempty (X i)} ↦ X i.val
  let hc := cofanNonemptySupport (Cofan.mk (∐ X) (Sigma.ι X)) (coproductIsCoproduct X)
  let e : (∐ Y) ≅ (∐ X) := (coproductIsCoproduct Y).coconePointUniqueUpToIso hc
  have he (i : {i // Nonempty (X i)}) : Sigma.ι Y i ≫ e.hom = Sigma.ι X i.val :=
    (coproductIsCoproduct Y).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have hop (i : I) : IsOpenImmersion (Sigma.ι X i) := by
    by_cases h : Nonempty (X i)
    · rw [← he ⟨i, h⟩]
      infer_instance
    · have : IsEmpty (X i) := ⟨fun x ↦ h ⟨x⟩⟩
      infer_instance
  refine ⟨hop, ?_, ?_⟩
  · intro z
    obtain ⟨i, x, hx⟩ := (sigmaOpenCover Y).exists_eq (e.inv z)
    refine ⟨i.val, x, ?_⟩
    have := congrArg (fun z ↦ e.hom z) hx
    change (Sigma.ι Y i ≫ e.hom) x = (e.inv ≫ e.hom) z at this
    rw [he, Iso.inv_hom_id] at this
    exact this
  · intro i j hij
    rw [Set.disjoint_iff_forall_ne]
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    have hx : Nonempty (X i) := ⟨x⟩
    have hy : Nonempty (X j) := ⟨y⟩
    have hxy' : Sigma.ι Y ⟨i, hx⟩ x = Sigma.ι Y ⟨j, hy⟩ y := by
      apply e.hom.homeomorph.injective
      simpa [← Scheme.Hom.comp_apply, he] using hxy
    have hidx := (sigmaι_eq_iff Y _ _ _ _).mp hxy'
    exact hij (congrArg (fun z ↦ z.1.val) hidx)

private noncomputable def cofanOfNonemptySupport {I : Type (u + 1)}
    {X : I → Scheme.{u}} (c : Cofan X)
    (hc : IsColimit (Cofan.mk c.pt (fun i : {i // Nonempty (X i)} ↦ c.inj i.val))) :
    IsColimit c := by
  classical
  refine Cofan.IsColimit.mk c
    (fun s ↦ hc.desc (Cofan.mk s.pt (fun i ↦ s.inj i.val))) ?_ ?_
  · intro s i
    by_cases h : Nonempty (X i)
    · exact hc.fac _ ⟨⟨i, h⟩⟩
    · have : IsEmpty (X i) := ⟨fun x ↦ h ⟨x⟩⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  · intro s m hm
    apply hc.hom_ext
    intro i
    exact (hm i.as.val).trans (hc.fac (Cofan.mk s.pt (fun i ↦ s.inj i.val)) i).symm

private theorem disjointCofan_isColimit {I : Type (u + 1)}
    {X : I → Scheme.{u}} {S : Scheme.{u}} (a : ∀ i, X i ⟶ S)
    (ha : ∀ i, IsOpenImmersion (a i))
    (hcov : ∀ z : S, ∃ i x, a i x = z)
    (hd : ∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j))) :
    Nonempty (IsColimit (Cofan.mk S a)) := by
  classical
  have (i : I) := ha i
  let point (i : {i // Nonempty (X i)}) : S := a i.val i.property.some
  have hinj : Function.Injective point := by
    intro i j he
    apply Subtype.ext
    by_contra hij
    exact Set.disjoint_iff_forall_ne.mp (hd i.val j.val hij)
      ⟨i.property.some, rfl⟩ ⟨j.property.some, rfl⟩ he
  have : Small.{u} {i // Nonempty (X i)} := small_of_injective hinj
  apply Nonempty.map (cofanOfNonemptySupport (Cofan.mk S a))
  apply nonempty_isColimit_cofanMk_of (fun i : {i // Nonempty (X i)} ↦ a i.val)
  · ext z
    change (z ∈ ⨆ i : {i // Nonempty (X i)}, (a i.val).opensRange) ↔ True
    rw [iff_true]
    simp only [TopologicalSpace.Opens.mem_iSup, Scheme.Hom.mem_opensRange]
    obtain ⟨i, x, hx⟩ := hcov z
    exact ⟨⟨i, ⟨x⟩⟩, x, hx⟩
  · intro i j hij
    change Disjoint (a i.val).opensRange (a j.val).opensRange
    rw [disjoint_iff]
    apply TopologicalSpace.Opens.ext
    exact Set.disjoint_iff_inter_eq_empty.mp
      (hd i.val j.val (fun h ↦ hij (Subtype.ext h)))

private theorem cofan_geometry {I : Type (u + 1)} {X : I → Scheme.{u}}
    (c : Cofan X) (hc : IsColimit c) :
    (∀ i, IsOpenImmersion (c.inj i)) ∧
    (∀ z : c.pt, ∃ i x, c.inj i x = z) ∧
    (∀ i j, i ≠ j → Disjoint (Set.range (c.inj i)) (Set.range (c.inj j))) := by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  let e : (∐ X) ≅ c.pt := (coproductIsCoproduct X).coconePointUniqueUpToIso hc
  have he (i : I) : Sigma.ι X i ≫ e.hom = c.inj i :=
    (coproductIsCoproduct X).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  obtain ⟨hop, hcov, hd⟩ := coproduct_geometry X
  have (i : I) := hop i
  refine ⟨fun i ↦ ?_, ?_, ?_⟩
  · rw [← he]; infer_instance
  · intro z
    obtain ⟨i, x, hx⟩ := hcov (e.inv z)
    refine ⟨i, x, ?_⟩
    have hh := congrArg (fun z ↦ e.hom z) hx
    change (Sigma.ι X i ≫ e.hom) x = (e.inv ≫ e.hom) z at hh
    rw [he, Iso.inv_hom_id] at hh
    exact hh
  · intro i j hij
    rw [Set.disjoint_iff_forall_ne]
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    apply Set.disjoint_iff_forall_ne.mp (hd i j hij) ⟨x, rfl⟩ ⟨y, rfl⟩
    apply e.hom.homeomorph.injective
    change e.hom (Sigma.ι X i x) = e.hom (Sigma.ι X j y)
    simpa only [← Scheme.Hom.comp_apply, he] using hxy

private theorem schemeCofan_universal {I : Type (u + 1)} {X : I → Scheme.{u}}
    (c : Cofan X) (hc : IsColimit c) : IsUniversalColimit c := by
  obtain ⟨hop, hcov, hd⟩ := cofan_geometry c hc
  intro F' c' α f h hα H
  let Y (i : I) := F'.obj ⟨i⟩
  let a (i : I) := c'.ι.app ⟨i⟩
  have hp (i : I) := H ⟨i⟩
  have hr (i : I) : Set.range (a i) = f ⁻¹' Set.range (c.inj i) := by
    change Set.range (c'.ι.app ⟨i⟩) = _
    rw [← (hp i).isoPullback_hom_fst]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (show Function.Surjective (hp i).isoPullback.hom from
        (hp i).isoPullback.hom.homeomorph.surjective), Set.image_univ]
    exact Scheme.Pullback.range_fst _ _
  have hop' (i : I) : IsOpenImmersion (a i) :=
    MorphismProperty.of_isPullback (hp i).flip (hop i)
  have hh : Nonempty (IsColimit (Cofan.mk c'.pt a)) := by
    apply disjointCofan_isColimit a hop'
    · intro z
      obtain ⟨i, x, hx⟩ := hcov (f z)
      have hz : z ∈ Set.range (a i) := by rw [hr]; exact ⟨x, hx⟩
      obtain ⟨y, hy⟩ := hz
      exact ⟨i, y, hy⟩
    · intro i j hij
      change Disjoint (Set.range (a i)) (Set.range (a j))
      rw [hr i, hr j]
      exact (hd i j hij).preimage f
  refine ⟨{ desc := fun s ↦ hh.some.desc (Cofan.mk s.pt (fun i ↦ s.ι.app ⟨i⟩))
            fac := ?_, uniq := ?_ }⟩
  · intro s j
    exact hh.some.fac (Cofan.mk s.pt (fun i ↦ s.ι.app ⟨i⟩)) j
  · intro s m hm
    apply hh.some.hom_ext
    intro j
    exact (hm j).trans (hh.some.fac (Cofan.mk s.pt (fun i ↦ s.ι.app ⟨i⟩)) j).symm

private theorem pairCofan_isColimit
    {I J : Type (u + 1)} {T : Scheme.{u}} {X : I → Scheme.{u}} {Y : J → Scheme.{u}}
    (f : ∀ i, X i ⟶ T) (g : ∀ j, Y j ⟶ T)
    [HasCoproduct X] [HasCoproduct Y] :
    Nonempty (IsColimit (schemeCoproductPairCofan f g)) := by
  refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
    (a := Cofan.mk (∐ X) (Sigma.ι X)) (b := Cofan.mk (∐ Y) (Sigma.ι Y))
    (schemeCofan_universal _ (coproductIsCoproduct X))
    (schemeCofan_universal _ (coproductIsCoproduct Y)) f g (Sigma.desc f) (Sigma.desc g)
    (fun i j ↦ pullback.cone (f i) (g j)) (fun i j ↦ pullback.isLimit (f i) (g j))
    (pullback.cone _ _) (pullback.isLimit _ _) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals intros; simp [schemeCoproductPairCofan, pullback.map]

private theorem tripleCofan_isColimit
    {I J K : Type (u + 1)} {T : Scheme.{u}}
    {X : I → Scheme.{u}} {Y : J → Scheme.{u}} {Z : K → Scheme.{u}}
    (f : ∀ i, X i ⟶ T) (g : ∀ j, Y j ⟶ T) (h : ∀ k, Z k ⟶ T)
    [HasCoproduct X] [HasCoproduct Y] [HasCoproduct Z] :
    Nonempty (IsColimit (schemeCoproductTripleCofan f g h)) := by
  refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
    (a := schemeCoproductPairCofan f g) (b := Cofan.mk (∐ Z) (Sigma.ι Z))
    (schemeCofan_universal _ (pairCofan_isColimit f g).some)
    (schemeCofan_universal _ (coproductIsCoproduct Z))
    (fun ij ↦ pullback.fst (f ij.1) (g ij.2) ≫ f ij.1) h
    (pullback.fst (Sigma.desc f) (Sigma.desc g) ≫ Sigma.desc f) (Sigma.desc h)
    (fun ij k ↦ pullback.cone (pullback.fst (f ij.1) (g ij.2) ≫ f ij.1) (h k))
    (fun ij k ↦ pullback.isLimit _ _) (pullback.cone _ _) (pullback.isLimit _ _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals intros; simp [schemeCoproductTripleCofan, schemeCoproductPairCofan, pullback.map]

private noncomputable def localPointsEquiv
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) {B : Scheme.{u}} (i : I) (a : B ⟶ U i) :
    (Over.mk a ⟶ F.localScheme i) ≃
      (F.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 B)))) :=
  (Iso.homCongr (Over.isoMk (Iso.refl B) (by simp) :
    Over.mk a ≅ (Over.map a).obj (Over.mk (𝟙 B))) (Iso.refl _)).trans
      (F.representation i).homEquiv

private noncomputable def localTransport
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) {B : Scheme.{u}} (i j : I)
    (a : B ⟶ U i) (b : B ⟶ U j) (h : a ≫ f i = b ≫ f j)
    (x : Over.mk a ⟶ F.localScheme i) : Over.mk b ⟶ F.localScheme j :=
  (localPointsEquiv F j b).symm
    ((F.data.hom (a ≫ f i) a b rfl h.symm).hom.app (op (Over.mk (𝟙 B)))
      (localPointsEquiv F i a x))

private theorem localTransport_self
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) {B : Scheme.{u}} (i : I)
    (a : B ⟶ U i) (x : Over.mk a ⟶ F.localScheme i) :
    localTransport F i i a a rfl x = x := by
  unfold localTransport
  rw [F.data.hom_self (a ≫ f i) a rfl]
  exact (localPointsEquiv F i a).symm_apply_apply x

private theorem localTransport_comp
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) {B : Scheme.{u}} (i j k : I)
    (a : B ⟶ U i) (b : B ⟶ U j) (c : B ⟶ U k)
    (h : a ≫ f i = b ≫ f j) (h' : b ≫ f j = c ≫ f k)
    (x : Over.mk a ⟶ F.localScheme i) :
    localTransport F j k b c h' (localTransport F i j a b h x) =
      localTransport F i k a c (h.trans h') x := by
  unfold localTransport
  rw [(localPointsEquiv F j b).apply_symm_apply]
  have e := F.data.hom_comp (a ≫ f i) a b c rfl h.symm (h.trans h').symm
  have en : F.data.hom (b ≫ f j) b c rfl h'.symm =
      F.data.hom (a ≫ f i) b c h.symm (h.trans h').symm := by congr 1; exact h.symm
  rw [en]
  congr 1
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun t ↦ t.hom) e) (op (Over.mk (𝟙 B)))) _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localTransport_natural
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) {B C : Scheme.{u}} (g : C ⟶ B) (i j : I)
    (a : B ⟶ U i) (b : B ⟶ U j) (h : a ≫ f i = b ≫ f j)
    (x : Over.mk a ⟶ F.localScheme i) :
    localTransport F i j (g ≫ a) (g ≫ b) (by simp only [Category.assoc]; rw [h])
      ((Over.homMk g rfl : Over.mk (g ≫ a) ⟶ Over.mk a) ≫ x) =
    (Over.homMk g rfl : Over.mk (g ≫ b) ⟶ Over.mk b) ≫ localTransport F i j a b h x := by
  have hp := F.data.pullHom_hom g (a ≫ f i) (g ≫ (a ≫ f i)) rfl
    a b rfl h.symm (g ≫ a) (g ≫ b) rfl rfl
  have hp' := congrArg (fun t ↦ t.hom.app (op (Over.mk (𝟙 C)))) hp
  dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Pseudofunctor.mapComp'] at hp'
  dsimp [GrothendieckTopology.pseudofunctorOver] at hp'
  simp only [Category.id_comp, Category.comp_id] at hp'
  unfold localTransport
  dsimp [localPointsEquiv, Iso.homCongr]
  simp only [Category.comp_id]
  apply (F.representation j).homEquiv.injective
  simp only [Functor.RepresentableBy.homEquiv_comp, Equiv.apply_symm_apply]
  simp only [GrothendieckTopology.overMapPullbackComp_inv_app_hom_app,
    GrothendieckTopology.overMapPullbackComp_hom_app_hom_app] at hp'
  have hn := (F.data.hom (a ≫ f i) a b rfl h.symm).hom.naturality
    (Over.homMk g rfl : Over.mk (g ≫ (𝟙 B)) ⟶ Over.mk (𝟙 B)).op
  have hpa : F.data.hom (g ≫ (a ≫ f i)) (g ≫ a) (g ≫ b)
      (by simp only [Category.assoc]) (by simp only [Category.assoc]; rw [h]) =
      F.data.hom ((g ≫ a) ≫ f i) (g ≫ a) (g ≫ b) rfl
        (by simp only [Category.assoc]; rw [h]) := by congr 1
  rw [hpa] at hp'
  rw [← hp']
  simp only [ConcreteCategory.comp_apply, ← Functor.map_comp_apply, ← op_comp]
  have ei : (Over.mapComp g a).inv.app (Over.mk (𝟙 C)) ≫
      (Over.isoMk (Iso.refl C) (by simp) : Over.mk (g ≫ a) ≅
        (Over.map (g ≫ a)).obj (Over.mk (𝟙 C))).inv ≫
      (Over.homMk g rfl : Over.mk (g ≫ a) ⟶ Over.mk a) =
      (Over.map a).map
        (Over.homMk g (by simp) : (Over.map g).obj (Over.mk (𝟙 C)) ⟶
          Over.mk (𝟙 B)) ≫
      (Over.isoMk (Iso.refl B) (by simp) : Over.mk a ≅
        (Over.map a).obj (Over.mk (𝟙 B))).inv := by
    ext; simp
  have ej : (Over.isoMk (Iso.refl C) (by simp) : Over.mk (g ≫ b) ≅
        (Over.map (g ≫ b)).obj (Over.mk (𝟙 C))).hom ≫
      (Over.mapComp g b).hom.app (Over.mk (𝟙 C)) ≫
      (Over.map b).map
        (Over.homMk g (by simp) : (Over.map g).obj (Over.mk (𝟙 C)) ⟶
          Over.mk (𝟙 B)) =
      (Over.homMk g rfl : Over.mk (g ≫ b) ⟶ Over.mk b) ≫
      (Over.isoMk (Iso.refl B) (by simp) : Over.mk b ≅
        (Over.map b).obj (Over.mk (𝟙 B))).hom := by
    ext; simp
  rw [ei]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have hn' := ConcreteCategory.congr_hom hn
    ((F.data.obj i).obj.map (Over.isoMk (Iso.refl B) (by simp) :
      Over.mk a ≅ (Over.map a).obj (Over.mk (𝟙 B))).inv.op
        ((F.representation i).homEquiv x))
  change (F.data.hom (a ≫ f i) a b rfl h.symm).hom.app
      (op ((Over.map g).obj (Over.mk (𝟙 C))))
        ((F.data.obj i).obj.map ((Over.map a).map
          (Over.homMk g (by simp) : (Over.map g).obj (Over.mk (𝟙 C)) ⟶
            Over.mk (𝟙 B))).op _) = _ at hn'
  have hr := congrArg
    (fun t ↦ (F.data.obj j).obj.map
      ((Over.isoMk (Iso.refl C) (by simp) : Over.mk (g ≫ b) ≅
        (Over.map (g ≫ b)).obj (Over.mk (𝟙 C))).hom ≫
        (Over.mapComp g b).hom.app (Over.mk (𝟙 C))).op t) hn'
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at hr
  refine hr.trans ?_
  change (F.data.obj j).obj.map _ ((F.data.obj j).obj.map _
    ((F.data.obj j).obj.map ((Over.map b).map
      (Over.homMk g (by simp) : (Over.map g).obj (Over.mk (𝟙 C)) ⟶
        Over.mk (𝟙 B))).op _)) = _
  simp only [← Functor.map_comp_apply, ← op_comp, ej]
  rfl

private theorem coproduct_precomp_ext
    {I : Type (u + 1)} {X : I → Scheme.{u}} [HasCoproduct X]
    {B Z : Scheme.{u}} (a : B ⟶ ∐ X) (r s : B ⟶ Z)
    (h : ∀ i, pullback.fst a (Sigma.ι X i) ≫ r =
      pullback.fst a (Sigma.ι X i) ≫ s) : r = s := by
  let c := Cofan.mk B (fun i ↦ pullback.fst a (Sigma.ι X i))
  have hc : Nonempty (IsColimit c) :=
    schemeCofan_universal (Cofan.mk (∐ X) (Sigma.ι X)) (coproductIsCoproduct X)
      c
      (Discrete.natTrans (fun i ↦ pullback.snd a (Sigma.ι X i.as))) a
      (by ext; simp [c, pullback.condition]) (.of_discrete _)
      (fun i ↦ IsPullback.of_hasPullback a (Sigma.ι X i.as))
  exact hc.some.hom_ext (fun i ↦ h i.as)

private theorem coproduct_map_cartesian
    {I : Type (u + 1)} {X Y : I → Scheme.{u}}
    [HasCoproduct X] [HasCoproduct Y] (g : ∀ i, X i ⟶ Y i) (i : I) :
    IsPullback (Sigma.ι X i) (g i) (CategoryTheory.Limits.Sigma.map g) (Sigma.ι Y i) := by
  classical
  obtain ⟨hx, hxc, hxd⟩ := coproduct_geometry X
  obtain ⟨hy, hyc, hyd⟩ := coproduct_geometry Y
  have (j : I) := hx j
  have (j : I) := hy j
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback (g i) (Sigma.ι X i) (Sigma.ι Y i)
    (CategoryTheory.Limits.Sigma.map g) (by simp)
  ext z
  change ((CategoryTheory.Limits.Sigma.map g) z ∈ Set.range (Sigma.ι Y i)) ↔
    z ∈ Set.range (Sigma.ι X i)
  obtain ⟨j, x, rfl⟩ := hxc z
  have he : (CategoryTheory.Limits.Sigma.map g) (Sigma.ι X j x) =
      Sigma.ι Y j (g j x) := by
    change (Sigma.ι X j ≫ CategoryTheory.Limits.Sigma.map g) x = _
    rw [Sigma.ι_map]; rfl
  rw [he]
  by_cases e : j = i
  · subst j; exact ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ ⟨g i x, rfl⟩⟩
  · constructor
    · intro ⟨y, he⟩
      exact False.elim (Set.disjoint_iff_forall_ne.mp (hyd j i e)
        ⟨g j x, rfl⟩ ⟨y, rfl⟩ he.symm)
    · intro ⟨y, he⟩
      exact False.elim (Set.disjoint_iff_forall_ne.mp (hxd j i e)
        ⟨x, rfl⟩ ⟨y, rfl⟩ he.symm)

private theorem coproduct_fppf
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T) [HasCoproduct U] :
    Presieve.singleton (Sigma.desc f) ∈ Scheme.fpqcPrecoverage T := by
  obtain ⟨hop, hc, hd⟩ := coproduct_geometry U
  let cover : (∐ U : Scheme.{u}).OpenCover :=
    { I₀ := I
      X := U
      f := Sigma.ι U
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun z ↦ by obtain ⟨i, x, hx⟩ := hc z; exact ⟨i, x, hx⟩, hop⟩ }
  have hf := (Scheme.ofArrows_mem_precoverage_iff _).mp hcov
  have hflat : Flat (Sigma.desc f) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @Flat) cover
    intro i
    simpa only [cover, Sigma.ι_desc] using (hf.2 i).1
  have hfp : LocallyOfFinitePresentation (Sigma.desc f) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) cover
    intro i
    simpa only [cover, Sigma.ι_desc] using (hf.2 i).2
  apply Scheme.fppfPrecoverage_le_fpqcPrecoverage _
  apply (Scheme.singleton_mem_precoverage_iff _ _).mpr
  refine ⟨?_, hflat, hfp⟩
  intro z
  obtain ⟨i, x, hx⟩ := hf.1 z
  refine ⟨Sigma.ι U i x, ?_⟩
  change (Sigma.ι U i ≫ Sigma.desc f) x = z
  simpa only [Sigma.ι_desc] using hx

private noncomputable def includeLocalPoint
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B : Scheme.{u}} (i : I) (a : B ⟶ U i) (x : Over.mk a ⟶ F.localScheme i) :
    Over.mk (a ≫ Sigma.ι U i) ⟶ F.coproductScheme :=
  Over.homMk (x.left ≫ Sigma.ι (fun i ↦ (F.localScheme i).left) i) (by
    change (x.left ≫ Sigma.ι (fun i ↦ (F.localScheme i).left) i) ≫
      CategoryTheory.Limits.Sigma.map (fun i ↦ (F.localScheme i).hom) = _
    rw [Category.assoc, Sigma.ι_map, ← Category.assoc, Over.w x]
    rfl)

private theorem coproduct_structure_comp
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)] :
    F.coproductScheme.hom ≫ Sigma.desc f =
      Sigma.desc (fun i ↦ (F.localScheme i).hom ≫ f i) := by
  apply Sigma.hom_ext
  intro i
  simp [SchemeCoverDescentDatum.coproductScheme]

private noncomputable def familyAction
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)] :
    pullback (Sigma.desc (fun i ↦ (F.localScheme i).hom ≫ f i)) (Sigma.desc f) ⟶
      (∐ fun i ↦ (F.localScheme i).left) :=
  (pairCofan_isColimit (fun i ↦ (F.localScheme i).hom ≫ f i) f).some.desc
    (Cofan.mk _ fun ij ↦
      (localTransport F ij.1 ij.2
        (pullback.fst ((F.localScheme ij.1).hom ≫ f ij.1) (f ij.2) ≫
          (F.localScheme ij.1).hom)
        (pullback.snd ((F.localScheme ij.1).hom ≫ f ij.1) (f ij.2))
        (by rw [Category.assoc, pullback.condition])
        (Over.homMk (pullback.fst _ _) rfl)).left ≫
        Sigma.ι (fun i ↦ (F.localScheme i).left) ij.2)

private theorem localTransport_left_congr
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) {B : Scheme.{u}} (i j : I)
    {a a' : B ⟶ U i} {b b' : B ⟶ U j}
    (h : a ≫ f i = b ≫ f j) (h' : a' ≫ f i = b' ≫ f j)
    (x : Over.mk a ⟶ F.localScheme i) (x' : Over.mk a' ⟶ F.localScheme i)
    (ha : a = a') (hb : b = b') (hx : x.left = x'.left) :
    (localTransport F i j a b h x).left = (localTransport F i j a' b' h' x').left := by
  subst a' b'
  have : x = x' := Over.OverMorphism.ext hx
  subst x'
  rfl

private theorem familyAction_component
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B : Scheme.{u}} (i j : I) (a : B ⟶ U i) (b : B ⟶ U j)
    (h : a ≫ f i = b ≫ f j) (x : Over.mk a ⟶ F.localScheme i) :
    pullback.lift (x.left ≫ Sigma.ι (fun i ↦ (F.localScheme i).left) i)
      (b ≫ Sigma.ι U j) (by
        simp only [Category.assoc, Sigma.ι_desc]
        rw [← Category.assoc, Over.w x]
        exact h) ≫ familyAction F =
      (localTransport F i j a b h x).left ≫
        Sigma.ι (fun i ↦ (F.localScheme i).left) j := by
  let l := pullback.lift x.left b (by rw [← Category.assoc, Over.w x]; exact h)
  have hl : pullback.lift (x.left ≫ Sigma.ι (fun i ↦ (F.localScheme i).left) i)
      (b ≫ Sigma.ι U j) (by
        simp only [Category.assoc, Sigma.ι_desc]
        rw [← Category.assoc, Over.w x]
        exact h) =
      l ≫ (schemeCoproductPairCofan
        (fun i ↦ (F.localScheme i).hom ≫ f i) f).inj (i, j) := by
    apply pullback.hom_ext <;> simp [l, schemeCoproductPairCofan, pullback.map]
  rw [hl, Category.assoc]
  rw [show (schemeCoproductPairCofan
      (fun i ↦ (F.localScheme i).hom ≫ f i) f).inj (i, j) ≫ familyAction F = _ from
    (pairCofan_isColimit (fun i ↦ (F.localScheme i).hom ≫ f i) f).some.fac _ ⟨(i, j)⟩]
  have hn := localTransport_natural F l i j
    (pullback.fst ((F.localScheme i).hom ≫ f i) (f j) ≫ (F.localScheme i).hom)
    (pullback.snd ((F.localScheme i).hom ≫ f i) (f j))
    (by rw [Category.assoc, pullback.condition]) (Over.homMk (pullback.fst _ _) rfl)
  have ea : l ≫ pullback.fst ((F.localScheme i).hom ≫ f i) (f j) ≫
      (F.localScheme i).hom = a := by simp [l]
  have eb : l ≫ pullback.snd ((F.localScheme i).hom ≫ f i) (f j) = b := by simp [l]
  have ex : (Over.homMk l rfl : Over.mk (l ≫
      (pullback.fst ((F.localScheme i).hom ≫ f i) (f j) ≫ (F.localScheme i).hom)) ⟶
      Over.mk (pullback.fst ((F.localScheme i).hom ≫ f i) (f j) ≫
        (F.localScheme i).hom)) ≫ Over.homMk (pullback.fst _ _) rfl =
      (Over.homMk x.left (by simp [l]) : Over.mk (l ≫
        (pullback.fst ((F.localScheme i).hom ≫ f i) (f j) ≫ (F.localScheme i).hom)) ⟶
        F.localScheme i) := by ext; simp [l]
  rw [ex] at hn
  have hn' := congrArg (fun z ↦ z.left) hn
  dsimp only [Over.comp_left, Over.homMk_left] at hn'
  have hh := congrArg (fun z ↦ z ≫ Sigma.ι (fun i ↦ (F.localScheme i).left) j) hn'.symm
  refine (Category.assoc _ _ _).symm.trans (hh.trans ?_)
  exact congrArg (fun z ↦ z ≫ Sigma.ι (fun i ↦ (F.localScheme i).left) j)
    (localTransport_left_congr F i j _ h _ x ea eb rfl)


private theorem familyAction_over
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)] :
    familyAction F ≫ F.coproductScheme.hom =
      pullback.snd (Sigma.desc (fun i ↦ (F.localScheme i).hom ≫ f i)) (Sigma.desc f) := by
  apply (pairCofan_isColimit (fun i ↦ (F.localScheme i).hom ≫ f i) f).some.hom_ext
  rintro ⟨⟨i, j⟩⟩
  dsimp only [familyAction]
  rw [← Category.assoc, IsColimit.fac]
  change (_ ≫ Sigma.ι (fun i ↦ (F.localScheme i).left) j) ≫
    CategoryTheory.Limits.Sigma.map (fun i ↦ (F.localScheme i).hom) = _
  rw [Category.assoc, Sigma.ι_map, ← Category.assoc, Over.w]
  simp [schemeCoproductPairCofan, pullback.map]

private noncomputable def familyTransport
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B : Scheme.{u}} (a b : B ⟶ ∐ U) (h : a ≫ Sigma.desc f = b ≫ Sigma.desc f)
    (x : Over.mk a ⟶ F.coproductScheme) : Over.mk b ⟶ F.coproductScheme :=
  Over.homMk
    (pullback.lift x.left b (by
      rw [← coproduct_structure_comp F, ← Category.assoc, Over.w x]; exact h) ≫
      familyAction F)
    (by rw [Category.assoc, familyAction_over, pullback.lift_snd]; rfl)

private theorem familyTransport_natural
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B C : Scheme.{u}} (g : C ⟶ B) (a b : B ⟶ ∐ U)
    (h : a ≫ Sigma.desc f = b ≫ Sigma.desc f)
    (x : Over.mk a ⟶ F.coproductScheme) :
    familyTransport F (g ≫ a) (g ≫ b) (by simp only [Category.assoc]; rw [h])
      ((Over.homMk g rfl : Over.mk (g ≫ a) ⟶ Over.mk a) ≫ x) =
      (Over.homMk g rfl : Over.mk (g ≫ b) ⟶ Over.mk b) ≫
        familyTransport F a b h x := by
  ext
  change pullback.lift (g ≫ x.left) (g ≫ b) _ ≫ familyAction F =
    g ≫ pullback.lift x.left b _ ≫ familyAction F
  apply Eq.trans (b := (g ≫ pullback.lift x.left b
    (by rw [← coproduct_structure_comp F, ← Category.assoc, Over.w x]; exact h)) ≫
      familyAction F)
  · congr 1
    apply pullback.hom_ext <;> simp
  · exact Category.assoc _ _ _

private theorem familyTransport_component
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B : Scheme.{u}} (i j : I) (a : B ⟶ U i) (b : B ⟶ U j)
    (h : a ≫ f i = b ≫ f j) (x : Over.mk a ⟶ F.localScheme i) :
    familyTransport F (a ≫ Sigma.ι U i) (b ≫ Sigma.ι U j)
      (by simp only [Category.assoc, Sigma.ι_desc]; exact h) (includeLocalPoint F i a x) =
      includeLocalPoint F j b (localTransport F i j a b h x) := by
  ext
  exact familyAction_component F i j a b h x

private noncomputable def localPointLift
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B C : Scheme.{u}} (g : C ⟶ B) (a : B ⟶ ∐ U) (i : I) (ai : C ⟶ U i)
    (x : Over.mk a ⟶ F.coproductScheme) (ha : g ≫ a = ai ≫ Sigma.ι U i) :
    Over.mk ai ⟶ F.localScheme i :=
  Over.homMk ((coproduct_map_cartesian (fun i ↦ (F.localScheme i).hom) i).lift
    (g ≫ x.left) ai (by
      change (g ≫ x.left) ≫ F.coproductScheme.hom = _
      rw [Category.assoc, Over.w x]
      exact ha)) (by simp)

private theorem localPointLift_fac
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B C : Scheme.{u}} (g : C ⟶ B) (a : B ⟶ ∐ U) (i : I) (ai : C ⟶ U i)
    (x : Over.mk a ⟶ F.coproductScheme) (ha : g ≫ a = ai ≫ Sigma.ι U i) :
    (localPointLift F g a i ai x ha).left ≫
      Sigma.ι (fun i ↦ (F.localScheme i).left) i = g ≫ x.left := by
  exact IsPullback.lift_fst _ _ _ _

private theorem familyTransport_left_congr
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B : Scheme.{u}} {a b a' b' : B ⟶ ∐ U}
    (h : a ≫ Sigma.desc f = b ≫ Sigma.desc f)
    (h' : a' ≫ Sigma.desc f = b' ≫ Sigma.desc f)
    (x : Over.mk a ⟶ F.coproductScheme) (x' : Over.mk a' ⟶ F.coproductScheme)
    (ha : a = a') (hb : b = b') (hx : x.left = x'.left) :
    (familyTransport F a b h x).left = (familyTransport F a' b' h' x').left := by
  subst a' b'
  have : x = x' := Over.OverMorphism.ext hx
  subst x'
  rfl

private theorem familyTransport_restrict
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B C : Scheme.{u}} (g : C ⟶ B) (a b : B ⟶ ∐ U)
    (h : a ≫ Sigma.desc f = b ≫ Sigma.desc f)
    (x : Over.mk a ⟶ F.coproductScheme)
    (i j : I) (ai : C ⟶ U i) (bj : C ⟶ U j)
    (ha : g ≫ a = ai ≫ Sigma.ι U i) (hb : g ≫ b = bj ≫ Sigma.ι U j)
    (hij : ai ≫ f i = bj ≫ f j) (xi : Over.mk ai ⟶ F.localScheme i)
    (hx : g ≫ x.left = xi.left ≫ Sigma.ι (fun i ↦ (F.localScheme i).left) i) :
    g ≫ (familyTransport F a b h x).left =
      (localTransport F i j ai bj hij xi).left ≫
        Sigma.ι (fun i ↦ (F.localScheme i).left) j := by
  have hn := congrArg (fun z ↦ z.left) (familyTransport_natural F g a b h x)
  calc
    _ = (familyTransport F (g ≫ a) (g ≫ b)
        (by simp only [Category.assoc]; rw [h])
        ((Over.homMk g rfl : Over.mk (g ≫ a) ⟶ Over.mk a) ≫ x)).left := hn.symm
    _ = (familyTransport F (ai ≫ Sigma.ι U i) (bj ≫ Sigma.ι U j)
        (by simp only [Category.assoc, Sigma.ι_desc]; exact hij)
        (includeLocalPoint F i ai xi)).left :=
      familyTransport_left_congr F _ _ _ _ ha hb hx
    _ = _ := congrArg (fun z ↦ z.left) (familyTransport_component F i j ai bj hij xi)

private theorem coproduct_triple_ext
    {I : Type (u + 1)} {U : I → Scheme.{u}} [HasCoproduct U]
    {B Z : Scheme.{u}} (a b c : B ⟶ ∐ U) (r s : B ⟶ Z)
    (H : ∀ (C : Scheme.{u}) (g : C ⟶ B) (i j k : I)
      (ai : C ⟶ U i) (bj : C ⟶ U j) (ck : C ⟶ U k),
      g ≫ a = ai ≫ Sigma.ι U i → g ≫ b = bj ≫ Sigma.ι U j →
      g ≫ c = ck ≫ Sigma.ι U k → g ≫ r = g ≫ s) : r = s := by
  apply coproduct_precomp_ext a
  intro i
  let g₁ := pullback.fst a (Sigma.ι U i)
  let ai := pullback.snd a (Sigma.ι U i)
  apply coproduct_precomp_ext (g₁ ≫ b)
  intro j
  let g₂ := pullback.fst (g₁ ≫ b) (Sigma.ι U j)
  let bj := pullback.snd (g₁ ≫ b) (Sigma.ι U j)
  apply coproduct_precomp_ext (g₂ ≫ g₁ ≫ c)
  intro k
  let g₃ := pullback.fst (g₂ ≫ g₁ ≫ c) (Sigma.ι U k)
  let ck := pullback.snd (g₂ ≫ g₁ ≫ c) (Sigma.ι U k)
  simpa only [Category.assoc] using H _ (g₃ ≫ g₂ ≫ g₁) i j k
    (g₃ ≫ g₂ ≫ ai) (g₃ ≫ bj) ck
    (by simp only [g₁, ai, Category.assoc, pullback.condition])
    (by simp only [g₂, bj, Category.assoc, pullback.condition])
    (by simp only [g₃, ck, Category.assoc, pullback.condition])

private theorem local_base_eq
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    [HasCoproduct U] {B C : Scheme.{u}} (g : C ⟶ B) {a b : B ⟶ ∐ U}
    (h : a ≫ Sigma.desc f = b ≫ Sigma.desc f)
    {i j : I} {ai : C ⟶ U i} {bj : C ⟶ U j}
    (ha : g ≫ a = ai ≫ Sigma.ι U i) (hb : g ≫ b = bj ≫ Sigma.ι U j) :
    ai ≫ f i = bj ≫ f j := by
  have hh := congrArg (fun z ↦ g ≫ z) h
  rw [← Category.assoc, ← Category.assoc, ha, hb] at hh
  simpa only [Category.assoc, Sigma.ι_desc] using hh

private theorem familyTransport_self
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B : Scheme.{u}} (a : B ⟶ ∐ U) (x : Over.mk a ⟶ F.coproductScheme) :
    familyTransport F a a rfl x = x := by
  ext
  apply coproduct_precomp_ext a
  intro i
  let g := pullback.fst a (Sigma.ι U i)
  let ai := pullback.snd a (Sigma.ι U i)
  have ha : g ≫ a = ai ≫ Sigma.ι U i := pullback.condition
  let xi := localPointLift F g a i ai x ha
  rw [familyTransport_restrict F g a a rfl x i i ai ai ha ha rfl xi
    (localPointLift_fac F g a i ai x ha).symm, localTransport_self]
  exact localPointLift_fac F g a i ai x ha

private theorem familyTransport_comp
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    {B : Scheme.{u}} (a b c : B ⟶ ∐ U)
    (h : a ≫ Sigma.desc f = b ≫ Sigma.desc f)
    (h' : b ≫ Sigma.desc f = c ≫ Sigma.desc f)
    (x : Over.mk a ⟶ F.coproductScheme) :
    familyTransport F b c h' (familyTransport F a b h x) =
      familyTransport F a c (h.trans h') x := by
  ext
  apply coproduct_triple_ext a b c
  intro C g i j k ai bj ck ha hb hc
  let xi := localPointLift F g a i ai x ha
  have hx := (localPointLift_fac F g a i ai x ha).symm
  have hij := local_base_eq g h ha hb
  have hjk := local_base_eq g h' hb hc
  have hxy := familyTransport_restrict F g a b h x i j ai bj ha hb hij xi hx
  rw [familyTransport_restrict F g b c h' (familyTransport F a b h x)
    j k bj ck hb hc hjk (localTransport F i j ai bj hij xi) hxy,
    familyTransport_restrict F g a c (h.trans h') x i k ai ck ha hc
      (hij.trans hjk) xi hx, localTransport_comp]

private noncomputable def familyDescentDatum
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)] :
    Over.DescentDatum (Sigma.desc f) F.coproductScheme where
  transport := familyTransport F
  transport_homMk_comp := familyTransport_natural F
  transport_self := familyTransport_self F
  transport_transport := familyTransport_comp F

private theorem localPointsEquiv_symm_left
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) {B : Scheme.{u}} (i : I) (a : B ⟶ U i)
    (x : (F.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 B))))) :
    ((localPointsEquiv F i a).symm x).left =
      ((F.representation i).homEquiv.symm x).left := by
  simp [localPointsEquiv, Iso.homCongr]

private theorem transport_represented_left
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) {B : Scheme.{u}} (p : B ⟶ T) (i j : I)
    (a : B ⟶ U i) (b : B ⟶ U j) (ha : a ≫ f i = p) (hb : b ≫ f j = p)
    (x : (F.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 B))))) :
    (localTransport F i j a b (ha.trans hb.symm) ((localPointsEquiv F i a).symm x)).left =
      ((F.representation j).homEquiv.symm
        ((F.data.hom p a b ha hb).hom.app (op (Over.mk (𝟙 B))) x)).left := by
  subst p
  unfold localTransport
  rw [Equiv.apply_symm_apply, localPointsEquiv_symm_left F j b]
  rfl


private theorem familyTransport_represented
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    (B : Scheme.{u}) (p : B ⟶ T) (i j : I) (a : B ⟶ U i) (b : B ⟶ U j)
    (ha : a ≫ f i = p) (hb : b ≫ f j = p)
    (x : (F.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 B))))) :
    ((familyDescentDatum F).transport (a ≫ Sigma.ι U i) (b ≫ Sigma.ι U j)
      (by simp only [Category.assoc, Sigma.ι_desc]; exact ha.trans hb.symm)
      (F.coproductPoint i a x)).left =
      ((F.representation j).homEquiv.symm
        ((F.data.hom p a b ha hb).hom.app (op (Over.mk (𝟙 B))) x)).left ≫
        Sigma.ι (fun i ↦ (F.localScheme i).left) j := by
  have hx : F.coproductPoint i a x =
      includeLocalPoint F i a ((localPointsEquiv F i a).symm x) := by
    ext
    change ((F.representation i).homEquiv.symm x).left ≫ _ =
      ((localPointsEquiv F i a).symm x).left ≫ _
    rw [localPointsEquiv_symm_left F i a]
  change (familyTransport F (a ≫ Sigma.ι U i) (b ≫ Sigma.ι U j)
    (by simp only [Category.assoc, Sigma.ι_desc]; exact ha.trans hb.symm)
    (F.coproductPoint i a x)).left = _
  rw [hx, familyTransport_component F i j a b (ha.trans hb.symm)]
  exact congrArg (fun z ↦ z ≫ Sigma.ι (fun i ↦ (F.localScheme i).left) j)
    (transport_represented_left F p i j a b ha hb x)

private theorem realization_cartesian
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    (W : Over T) (q : ∀ i, (F.localScheme i).left ⟶ W.left)
    (hq : ∀ i, IsPullback (q i) (F.localScheme i).hom W.hom (f i)) :
    IsPullback (Sigma.desc q) F.coproductScheme.hom W.hom (Sigma.desc f) := by
  have H := IsUniversalColimit.isPullback_of_isColimit_left
    (a := Cofan.mk (∐ U) (Sigma.ι U))
    (schemeCofan_universal _ (coproductIsCoproduct U)) f (Sigma.desc f) W.hom
    q (fun i ↦ (F.localScheme i).hom) hq
    (coproductIsCoproduct (fun i ↦ (F.localScheme i).left))
  have he : Sigma.desc (fun i ↦ (F.localScheme i).hom ≫ Sigma.ι U i) =
      F.coproductScheme.hom := by
    apply Sigma.hom_ext
    intro i
    simp [SchemeCoverDescentDatum.coproductScheme]
  change IsPullback (Sigma.desc q)
    (Sigma.desc (fun i ↦ (F.localScheme i).hom ≫ Sigma.ι U i)) W.hom (Sigma.desc f) at H
  rwa [he] at H

private theorem local_invariance
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) (W : Over T)
    (q : ∀ i, (F.localScheme i).left ⟶ W.left)
    (hq : ∀ (B : Scheme.{u}) (p : B ⟶ T) (i j : I) (a : B ⟶ U i) (b : B ⟶ U j)
      (ha : a ≫ f i = p) (hb : b ≫ f j = p)
      (x : (F.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 B))))),
      ((F.representation j).homEquiv.symm
        ((F.data.hom p a b ha hb).hom.app (op (Over.mk (𝟙 B))) x)).left ≫ q j =
        ((F.representation i).homEquiv.symm x).left ≫ q i)
    {B : Scheme.{u}} (i j : I) (a : B ⟶ U i) (b : B ⟶ U j)
    (h : a ≫ f i = b ≫ f j) (x : Over.mk a ⟶ F.localScheme i) :
    (localTransport F i j a b h x).left ≫ q j = x.left ≫ q i := by
  have H := hq B (a ≫ f i) i j a b rfl h.symm (localPointsEquiv F i a x)
  rw [← transport_represented_left F (a ≫ f i) i j a b rfl h.symm,
    Equiv.symm_apply_apply] at H
  rw [← localPointsEquiv_symm_left F i a, Equiv.symm_apply_apply] at H
  exact H

private theorem global_invariance
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)]
    (W : Over T) (q : ∀ i, (F.localScheme i).left ⟶ W.left)
    (hq : ∀ {B : Scheme.{u}} (i j : I) (a : B ⟶ U i) (b : B ⟶ U j)
      (h : a ≫ f i = b ≫ f j) (x : Over.mk a ⟶ F.localScheme i),
      (localTransport F i j a b h x).left ≫ q j = x.left ≫ q i)
    (B : Scheme.{u}) (a b : B ⟶ ∐ U)
    (h : a ≫ Sigma.desc f = b ≫ Sigma.desc f) (x : Over.mk a ⟶ F.coproductScheme) :
    ((familyDescentDatum F).transport a b h x).left ≫ Sigma.desc q =
      x.left ≫ Sigma.desc q := by
  change (familyTransport F a b h x).left ≫ Sigma.desc q = _
  apply coproduct_triple_ext a b b
  intro C g i j k ai bj ck ha hb hc
  let xi := localPointLift F g a i ai x ha
  have hx := (localPointLift_fac F g a i ai x ha).symm
  have hij := local_base_eq g h ha hb
  rw [← Category.assoc, familyTransport_restrict F g a b h x i j ai bj ha hb hij xi hx,
    Category.assoc, Sigma.ι_desc, ← Category.assoc, hx, Category.assoc, Sigma.ι_desc]
  exact hq i j ai bj hij xi

private theorem fixed_realization_iff
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (F : SchemeCoverDescentDatum f) [HasCoproduct U]
    [HasCoproduct (fun i ↦ (F.localScheme i).left)] (W : Over T) :
    (∃ q : (∐ fun i ↦ (F.localScheme i).left) ⟶ W.left,
      IsPullback q F.coproductScheme.hom W.hom (Sigma.desc f) ∧
      ∀ (B : Scheme.{u}) (a b : B ⟶ ∐ U) (h : a ≫ Sigma.desc f = b ≫ Sigma.desc f)
        (x : Over.mk a ⟶ F.coproductScheme),
        ((familyDescentDatum F).transport a b h x).left ≫ q = x.left ≫ q) ↔
    (∃ q : ∀ i, (F.localScheme i).left ⟶ W.left,
      (∀ i, IsPullback (q i) (F.localScheme i).hom W.hom (f i)) ∧
      ∀ (B : Scheme.{u}) (p : B ⟶ T) (i j : I) (a : B ⟶ U i) (b : B ⟶ U j)
        (ha : a ≫ f i = p) (hb : b ≫ f j = p)
        (x : (F.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 B))))),
        ((F.representation j).homEquiv.symm
          ((F.data.hom p a b ha hb).hom.app (op (Over.mk (𝟙 B))) x)).left ≫ q j =
          ((F.representation i).homEquiv.symm x).left ≫ q i) := by
  constructor
  · rintro ⟨q, hq, hinv⟩
    refine ⟨fun i ↦ Sigma.ι (fun i ↦ (F.localScheme i).left) i ≫ q, ?_, ?_⟩
    · intro i
      have hp := (coproduct_map_cartesian (fun i ↦ (F.localScheme i).hom) i).paste_horiz hq
      simpa only [Sigma.ι_desc] using hp
    · intro B p i j a b ha hb x
      have H := hinv B (a ≫ Sigma.ι U i) (b ≫ Sigma.ι U j)
        (by simp only [Category.assoc, Sigma.ι_desc]; exact ha.trans hb.symm)
        (F.coproductPoint i a x)
      rw [familyTransport_represented F B p i j a b ha hb x] at H
      simpa only [SchemeCoverDescentDatum.coproductPoint, Over.homMk_left,
        Category.assoc] using H
  · rintro ⟨q, hq, hinv⟩
    exact ⟨Sigma.desc q, realization_cartesian F W q hq,
      global_invariance F W q (local_invariance F W q hinv)⟩

/-- Family scheme descent is encoded by the coproduct, preserving its transports and every
fixed global realization. Source: Stacks Project, Descent, Tags 023V and 023X; Topologies,
Tags 021P and 022B (blueprint: lem-trf-fppf-family-coproduct-descent-encoding).

Proof:
1. The open, pairwise disjoint coprojections cover each coproduct. Their inverse images in
   a double product are the component products, by the open-fibre-product lemma. Glue the
   inverse component identifications, using scheme-morphism gluing; the composites are
   identities by gluing uniqueness and the coproduct universal property. Repeat for triples.
   The legs of the cofans retain the projections, so all projection identifications agree.
2. Under these identifications assemble the local transitions and their inverses by the
   coproduct universal property. Their projection equations make the result a transport on
   the coproduct local scheme over the coproduct base.
3. On each triple component the singleton cocycle is the given component cocycle. Coproduct
   uniqueness proves it globally. The invertible cocycle implies identity transport.
4. The inverse image of the i-th base component is precisely the i-th local scheme, because
   the coproduct components are disjoint. Restriction of transport is the given transition.
5. The coproduct map is flat on stalks, since every stalk is in a component. For each affine
   base open, base-change the fppf covering and use finite affine refinement (Tag 021P).
   Its finitely many affine opens are also opens of the coproduct and cover that base open.
   This is the fpqc covering condition (Tag 022B), even for an infinite family.
6. For a fixed W/T, restrict a Cartesian realization and invariant map on the coproduct to
   its components. Conversely assemble the local realization maps by the coproduct property.
   The product cofans show the square is Cartesian and transport invariance is precisely
   component invariance. Thus the same W realizes either datum, and effectivity is equivalent.
7. An empty covering forces T empty. Both coproducts and any W/T are empty; the maps are
   unique and the affine-open covering test uses zero affine opens. Empty summands likewise
   impose no extra compatibility. These arguments use scheme coproducts, open fibre products,
   scheme-morphism gluing, flatness, fppf base change, and finite affine refinement, exactly
   the proof dependencies of this node. -/
theorem fppf_family_coproduct_descent_encoding
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T)
    (F : SchemeCoverDescentDatum f)
    [HasCoproduct U] [HasCoproduct (fun i ↦ (F.localScheme i).left)] :
    Nonempty (IsColimit (schemeCoproductPairCofan f f)) ∧
    Nonempty (IsColimit (schemeCoproductPairCofan
      (fun i ↦ (F.localScheme i).hom ≫ f i) f)) ∧
    Nonempty (IsColimit (schemeCoproductPairCofan f
      (fun i ↦ (F.localScheme i).hom ≫ f i))) ∧
    Nonempty (IsColimit (schemeCoproductTripleCofan f f f)) ∧
    Nonempty (IsColimit (schemeCoproductTripleCofan
      (fun i ↦ (F.localScheme i).hom ≫ f i) f f)) ∧
    Nonempty (IsColimit (schemeCoproductTripleCofan f
      (fun i ↦ (F.localScheme i).hom ≫ f i) f)) ∧
    Nonempty (IsColimit (schemeCoproductTripleCofan f f
      (fun i ↦ (F.localScheme i).hom ≫ f i))) ∧
    ∃ D : Over.DescentDatum (Sigma.desc f)
      F.coproductScheme,
      (∀ i, IsPullback (Sigma.ι (fun i ↦ (F.localScheme i).left) i)
        (F.localScheme i).hom F.coproductScheme.hom (Sigma.ι U i)) ∧
      (∀ (B : Scheme.{u}) (p : B ⟶ T) (i j : I) (a : B ⟶ U i) (b : B ⟶ U j)
        (ha : a ≫ f i = p) (hb : b ≫ f j = p)
        (x : (F.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 B))))),
        (D.transport (a ≫ Sigma.ι U i) (b ≫ Sigma.ι U j)
          (by simp only [Category.assoc, Sigma.ι_desc]; exact ha.trans hb.symm)
          (F.coproductPoint i a x)).left =
        ((F.representation j).homEquiv.symm
          ((F.data.hom p a b ha hb).hom.app (op (Over.mk (𝟙 B))) x)).left ≫
          Sigma.ι (fun i ↦ (F.localScheme i).left) j) ∧
      Presieve.singleton (Sigma.desc f) ∈ Scheme.fpqcPrecoverage T ∧
      (∀ W : Over T,
        (∃ q : (∐ fun i ↦ (F.localScheme i).left) ⟶ W.left,
          IsPullback q F.coproductScheme.hom W.hom (Sigma.desc f) ∧
          ∀ (B : Scheme.{u}) (a b : B ⟶ ∐ U) (h : a ≫ Sigma.desc f = b ≫ Sigma.desc f)
            (x : Over.mk a ⟶ F.coproductScheme),
            (D.transport a b h x).left ≫ q = x.left ≫ q) ↔
        (∃ q : ∀ i, (F.localScheme i).left ⟶ W.left,
          (∀ i, IsPullback (q i) (F.localScheme i).hom W.hom (f i)) ∧
          ∀ (B : Scheme.{u}) (p : B ⟶ T) (i j : I) (a : B ⟶ U i) (b : B ⟶ U j)
            (ha : a ≫ f i = p) (hb : b ≫ f j = p)
            (x : (F.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 B))))),
            ((F.representation j).homEquiv.symm
              ((F.data.hom p a b ha hb).hom.app (op (Over.mk (𝟙 B))) x)).left ≫ q j =
              ((F.representation i).homEquiv.symm x).left ≫ q i)) ∧
      (F.IsEffective ↔ D.IsEffective) := by
  refine ⟨pairCofan_isColimit f f,
    pairCofan_isColimit (fun i ↦ (F.localScheme i).hom ≫ f i) f,
    pairCofan_isColimit f (fun i ↦ (F.localScheme i).hom ≫ f i),
    tripleCofan_isColimit f f f,
    tripleCofan_isColimit (fun i ↦ (F.localScheme i).hom ≫ f i) f f,
    tripleCofan_isColimit f (fun i ↦ (F.localScheme i).hom ≫ f i) f,
    tripleCofan_isColimit f f (fun i ↦ (F.localScheme i).hom ≫ f i),
    familyDescentDatum F,
    fun i ↦ coproduct_map_cartesian (fun i ↦ (F.localScheme i).hom) i,
    familyTransport_represented F, coproduct_fppf f hcov, fixed_realization_iff F, ?_⟩
  constructor
  · rintro ⟨W, q, hq, hinv⟩
    obtain ⟨q', hq', hinv'⟩ := (fixed_realization_iff F W).mpr ⟨q, hq, hinv⟩
    exact ⟨W, q', hq', fun a b h x ↦ hinv' _ a b h x⟩
  · rintro ⟨W, q, hq, hinv⟩
    obtain ⟨q', hq', hinv'⟩ := (fixed_realization_iff F W).mp
      ⟨q, hq, fun B a b h x ↦ hinv a b h x⟩
    exact ⟨W, q', hq', hinv'⟩

end AlgebraicGeometry
