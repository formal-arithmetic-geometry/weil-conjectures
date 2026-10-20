/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
public import Sheaf.AlgebraicGeometry.SchemeUniverseEnlargement
public import Sheaf.AlgebraicGeometry.UniverseEnlargedEtaleRealization
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProEtaleUniverseLiftCover
import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcValuativeDescent
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme

/-!
# Representability of pro-etale local systems of sets

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 7.3.1(1),(3)
and Lemma 7.3.9, implication Loc_X to Cov_X
(blueprint: lem-a1-proetale-local-system-representability).

The site is `X.ProEt`, with object universe `u + 1`, morphism universe `u`, and set
values in `Type (u + 1)`. The representing scheme lives in universe `u + 1` over
the canonical enlargement of `X`. This permits arbitrary sets of local sheets in
the sheaf universe. The original site is retained, and its objects and arrows are
enlarged only when evaluating the representing functor of points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The canonical functor from the original small pro-etale site to schemes over
the enlarged base, sending a structure map to its canonical universe enlargement.
Source: Bhatt--Scholze, Definition 7.3.1 and Lemma 7.3.9, functor of points;
Stacks Tag 01JA, affine gluing for universe enlargement
(blueprint: lem-a1-proetale-local-system-representability). -/
@[irreducible]
noncomputable def proEtaleUniverseLiftToOver (X : Scheme.{u}) :
    X.ProEt ⥤ Over (schemeUniverseLift.{u, u + 1} X) :=
  ProEt.forget X ⋙ Over.post AlgebraicSpace.schemeUniverseLiftFunctor

private theorem fpqc_cover_of_proEtale_coversTop (X : Scheme.{u})
    {I : Type (u + 1)} (U : I → X.ProEt)
    (hcover : (ProEt.topology X).CoversTop U) :
    Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ fpqcPrecoverage X := by
  classical
  let T : X.ProEt := ProEt.mk (𝟙 X)
  let J := proetalePrecoverage.comap (ProEt.forget X ⋙ Over.forget X)
  have h := hcover T
  change Sieve.ofObjects U T ∈ J.toGrothendieck T at h
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at h
  obtain ⟨R, hR, hle⟩ := h
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨V, rfl⟩ := hR
  have hV : Presieve.ofArrows (fun i ↦ (V.X i).left) (fun i ↦ (V.f i).left) ∈
      proetalePrecoverage X := by
    have hv := V.mem₀
    change (V.presieve₀.map (ProEt.forget X ⋙ Over.forget X)) ∈
      proetalePrecoverage X at hv
    rw [Presieve.map_ofArrows] at hv
    exact hv
  have hW := proetalePrecoverage_le_fpqcPrecoverage X hV
  let W : PreZeroHypercover X :=
    { I₀ := V.I₀, X := fun i ↦ (V.X i).left, f := fun i ↦ (V.f i).left }
  let D : PreZeroHypercover X :=
    { I₀ := I, X := fun i ↦ (U i).left, f := fun i ↦ (U i).hom }
  have hqc : QuasiCompactCover W :=
    (presieve₀_mem_qcPrecoverage_iff).1 hW.1
  have hfactor (i : V.I₀) : ∃ j : I, Nonempty (V.X i ⟶ U j) :=
    hle _ _ (Presieve.ofArrows.mk i)
  let r : W.Hom D :=
    { s₀ := fun i ↦ (hfactor i).choose
      h₀ := fun i ↦ (hfactor i).choose_spec.some.left
      w₀ := by
        intro i
        change (hfactor i).choose_spec.some.left ≫ (U ((hfactor i).choose)).hom =
          (V.f i).left
        have hw := MorphismProperty.Over.w (hfactor i).choose_spec.some
        have hv := MorphismProperty.Over.w (V.f i)
        change (V.f i).left ≫ 𝟙 X = (V.X i).hom at hv
        exact hw.trans (hv.symm.trans (Category.comp_id _)) }
  have : QuasiCompactCover D := QuasiCompactCover.of_hom r
  refine ⟨presieve₀_mem_qcPrecoverage_iff.2 this, ?_⟩
  rw [ofArrows_mem_precoverage_iff]
  refine ⟨?_, fun i ↦ inferInstance⟩
  intro x
  obtain ⟨i, y, hy⟩ := ((ofArrows_mem_precoverage_iff _).1 hW.2).1 x
  refine ⟨r.s₀ i, r.h₀ i y, ?_⟩
  change (r.h₀ i ≫ D.f (r.s₀ i)) y = x
  rw [r.w₀ i]
  exact hy

private theorem coproduct_map_eq_component
    (B W : Scheme.{u}) (S : Type u) [ConnectedSpace W]
    (b : W ⟶ B) (f : W ⟶ ∐ fun _ : S ↦ B)
    (hf : f ≫ Sigma.desc (fun _ : S ↦ 𝟙 B) = b) :
    ∃ s : S, f = b ≫ Sigma.ι (fun _ : S ↦ B) s := by
  classical
  obtain ⟨e, he⟩ := (coproductCopiesMorphismsClopen B W S b).2.2.2.1
  let c := e ⟨f, hf⟩
  let s := c (Classical.arbitrary W)
  have hr : Set.range f ⊆ Set.range (Sigma.ι (fun _ : S ↦ B) s) := by
    rintro _ ⟨x, rfl⟩
    change x ∈ f ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ B) s).opensRange
    change x ∈ (↑((⟨f, hf⟩ : {f : W ⟶ ∐ fun _ : S ↦ B |
      f ≫ Sigma.desc (fun _ : S ↦ 𝟙 B) = b}) : W ⟶ ∐ fun _ : S ↦ B) ⁻¹ᵁ
        (Sigma.ι (fun _ : S ↦ B) s).opensRange : Set W)
    rw [he ⟨f, hf⟩ s]
    exact c.isLocallyConstant.apply_eq_of_preconnectedSpace x (Classical.arbitrary W)
  let g := IsOpenImmersion.lift (Sigma.ι (fun _ : S ↦ B) s) f hr
  have hg : g ≫ Sigma.ι (fun _ : S ↦ B) s = f := IsOpenImmersion.lift_fac _ _ _
  have gb : g = b := by
    have h := congrArg (fun k ↦ k ≫ Sigma.desc (fun _ : S ↦ 𝟙 B)) hg
    simpa only [Category.assoc, Sigma.ι_desc, Category.comp_id, hf] using h
  exact ⟨s, by rw [← hg, gb]⟩

private theorem coproductCopies_valuative (B : Scheme.{u}) (S : Type u) :
    ValuativeCriterion (Sigma.desc (fun _ : S ↦ 𝟙 B)) := by
  intro D
  obtain ⟨s, hs⟩ := coproduct_map_eq_component B (Spec (.of D.K)) S
    (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂) D.i₁ D.commSq.w
  let l : D.commSq.LiftStruct :=
    ⟨D.i₂ ≫ Sigma.ι (fun _ : S ↦ B) s, by simpa [Category.assoc] using hs.symm,
      by simp⟩
  refine ⟨{ default := l, uniq := ?_ }⟩
  intro m
  obtain ⟨t, ht⟩ := coproduct_map_eq_component B (Spec (.of D.R)) S D.i₂ m.l m.fac_right
  have hst : s = t := by
    have h : (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂) ≫
        Sigma.ι (fun _ : S ↦ B) s =
        (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂) ≫
          Sigma.ι (fun _ : S ↦ B) t := by
      rw [← hs, ← m.fac_left, ht, Category.assoc]
    let x : Spec (.of D.K) := Classical.arbitrary _
    have hp := congrArg (fun k : Spec (.of D.K) ⟶ ∐ fun _ : S ↦ B ↦ k x) h
    exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : S ↦ B) s t _ _).mp hp)
  apply CommSq.LiftStruct.ext
  exact ht.trans (congrArg (fun t ↦ D.i₂ ≫ Sigma.ι (fun _ : S ↦ B) t) hst.symm)

private theorem coproductCopies_separated (B : Scheme.{u}) (S : Type u) :
    IsSeparated (Sigma.desc (fun _ : S ↦ 𝟙 B)) := by
  classical
  let D : Scheme.{u} := ∐ fun _ : S ↦ B
  let p : D ⟶ B := Sigma.desc (fun _ : S ↦ 𝟙 B)
  let P := pullback p p
  let a : P ⟶ D := pullback.fst p p
  let b : P ⟶ D := pullback.snd p p
  let t : P ⟶ B := a ≫ p
  have hb : b ≫ p = t := pullback.condition.symm
  obtain ⟨e, he⟩ := (coproductCopiesMorphismsClopen B P S t).2.2.2.1
  let c := e ⟨a, rfl⟩
  let d := e ⟨b, hb⟩
  have mem (f : P ⟶ D) (hf : f ≫ p = t) (s : S) (x : P) :
      x ∈ f ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ B) s).opensRange ↔ e ⟨f, hf⟩ x = s := by
    exact Set.ext_iff.mp (he ⟨f, hf⟩ s) x
  have hr : Set.range (pullback.diagonal p) = {x : P | c x = d x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      let s := c ((pullback.diagonal p) y)
      have ha : (pullback.diagonal p) y ∈
          a ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ B) s).opensRange := (mem a rfl s _).mpr rfl
      have hab : a ((pullback.diagonal p) y) = b ((pullback.diagonal p) y) := by
        change (pullback.diagonal p ≫ a) y = (pullback.diagonal p ≫ b) y
        simp [a, b]
      have hb' : (pullback.diagonal p) y ∈
          b ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ B) s).opensRange := by
        change b ((pullback.diagonal p) y) ∈ (Sigma.ι (fun _ : S ↦ B) s).opensRange
        rwa [← hab]
      exact ((mem b hb s _).mp hb').symm
    · intro hx
      let s := c x
      let V : P.Opens := (a ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ B) s).opensRange) ⊓
        (b ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ B) s).opensRange)
      have hxV : x ∈ V := ⟨(mem a rfl s x).mpr rfl, (mem b hb s x).mpr hx.symm⟩
      have ra : Set.range (V.ι ≫ a) ⊆ Set.range (Sigma.ι (fun _ : S ↦ B) s) := by
        rintro _ ⟨z, rfl⟩
        exact z.property.1
      have rb : Set.range (V.ι ≫ b) ⊆ Set.range (Sigma.ι (fun _ : S ↦ B) s) := by
        rintro _ ⟨z, rfl⟩
        exact z.property.2
      let la := IsOpenImmersion.lift (Sigma.ι (fun _ : S ↦ B) s) (V.ι ≫ a) ra
      let lb := IsOpenImmersion.lift (Sigma.ι (fun _ : S ↦ B) s) (V.ι ≫ b) rb
      have hla : la ≫ Sigma.ι (fun _ : S ↦ B) s = V.ι ≫ a :=
        IsOpenImmersion.lift_fac _ _ _
      have hlb : lb ≫ Sigma.ι (fun _ : S ↦ B) s = V.ι ≫ b :=
        IsOpenImmersion.lift_fac _ _ _
      have hab : V.ι ≫ a = V.ι ≫ b := by
        have hla' : la = V.ι ≫ t := by
          simpa [p, Category.assoc] using congrArg (fun k ↦ k ≫ p) hla
        have hlb' : lb = V.ι ≫ t := by
          simpa [p, Category.assoc, hb] using congrArg (fun k ↦ k ≫ p) hlb
        rw [← hla, ← hlb, hla', hlb']
      have hfac : (V.ι ≫ a) ≫ pullback.diagonal p = V.ι := by
        apply pullback.hom_ext
        · simp [a, Category.assoc]
        · simpa [b, Category.assoc] using hab
      refine ⟨a x, ?_⟩
      exact congrArg (fun k : V.toScheme ⟶ P ↦ k ⟨x, hxV⟩) hfac
  have hp : Etale p := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rw [hr]
  exact ⟨(c.isLocallyConstant.prodMk d.isLocallyConstant) {st : S × S | st.1 ≠ st.2}⟩

private theorem closedDiagonal_of_separatedPresheaf
    {B : Scheme.{u}} (P : (Over B)ᵒᵖ ⥤ Type u)
    (h : AlgebraicSpace.IsSeparatedPresheafMap (terminal.from P)) :
    AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 P) (𝟙 P)) := by
  let t := terminal.from P
  let e : pullback t t ≅ P ⨯ P :=
    { hom := prod.lift (pullback.fst t t) (pullback.snd t t)
      inv := pullback.lift prod.fst prod.snd (Subsingleton.elim _ _)
      hom_inv_id := by apply pullback.hom_ext <;> simp
      inv_hom_id := by apply prod.hom_ext <;> simp }
  intro T a
  obtain ⟨V, p, q, hp, hclosed⟩ := h T (a ≫ e.inv)
  refine ⟨V, p, q, ?_, hclosed⟩
  apply hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  · simp
  · simp
  · dsimp [AlgebraicSpace.diagonalPresheafMap, e, t]
    apply prod.hom_ext <;> simp
  · simp

private theorem valuativeCriterion_of_presheafIso
    {B : Scheme.{u}} {P : (Over B)ᵒᵖ ⥤ Type u} (Z : Over B)
    (e : yoneda.obj Z ≅ P) (h : AlgebraicSpace.HasFullValuativeLifting P) :
    ValuativeCriterion Z.hom := by
  intro D
  let T : Over B := Over.mk D.i₂
  let V : Over B := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂)
  let j : V ⟶ T := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))) rfl
  let a : V ⟶ Z := Over.homMk D.i₁ D.commSq.w
  obtain ⟨t, ht, hu⟩ := h D.R D.K D.i₂ (e.hom.app (op V) a)
  let l : T ⟶ Z := e.inv.app (op T) t
  have hj : j ≫ l = a := by
    change (yoneda.obj Z).map j.op (e.inv.app (op T) t) = a
    rw [← NatTrans.naturality_apply, ht]
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app (op V)) a
  let lift : D.commSq.LiftStruct :=
    ⟨l.left, congrArg Over.Hom.left hj, l.w⟩
  refine ⟨{ default := lift, uniq := ?_ }⟩
  intro m
  have hm : e.hom.app (op T) (Over.homMk m.l m.fac_right) = t := by
    apply hu
    rw [← NatTrans.naturality_apply]
    congr 1
    apply Over.OverMorphism.ext
    exact m.fac_left
  have hml : Over.homMk m.l m.fac_right = l := by
    dsimp [l]
    rw [← hm]
    exact (ConcreteCategory.congr_hom (e.hom_inv_id_app (op T)) _).symm
  apply CommSq.LiftStruct.ext
  exact congrArg Over.Hom.left hml

private theorem closedRepresentable_yonedaMap {B : Scheme.{u}}
    {Z W : Over B} (f : Z ⟶ W) [IsClosedImmersion f.left] :
    AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (yoneda.map f) := by
  intro T a
  let g : T ⟶ W := yoneda.preimage a
  refine ⟨pullback f g, pullback.snd f g, yoneda.map (pullback.fst f g), ?_, ?_⟩
  · simpa only [g, Functor.map_preimage] using (IsPullback.of_hasPullback f g).map yoneda
  · have h := (IsPullback.of_hasPullback f g).map (Over.forget B)
    exact MorphismProperty.of_isPullback h (inferInstance : IsClosedImmersion f.left)

private theorem separatedPresheaf_of_presheafIso {B : Scheme.{u}}
    {P : (Over B)ᵒᵖ ⥤ Type u} (Z : Over B) [IsSeparated Z.hom]
    (e : yoneda.obj Z ≅ P) :
    AlgebraicSpace.IsSeparatedPresheafMap (terminal.from P) := by
  let d : Z ⟶ Z ⨯ Z := prod.lift (𝟙 Z) (𝟙 Z)
  have hd : d.left ≫ (Over.prodLeftIsoPullback Z Z).hom =
      pullback.diagonal Z.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst, pullback.diagonal_fst]
      change (d ≫ prod.fst).left = Over.Hom.left (𝟙 Z)
      simp [d]
    · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd, pullback.diagonal_snd]
      change (d ≫ prod.snd).left = Over.Hom.left (𝟙 Z)
      simp [d]
  have : IsClosedImmersion d.left := by
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion
      d.left (Over.prodLeftIsoPullback Z Z).hom, hd]
    infer_instance
  let t := terminal.from P
  let ep : pullback t t ≅ P ⨯ P :=
    { hom := prod.lift (pullback.fst t t) (pullback.snd t t)
      inv := pullback.lift prod.fst prod.snd (Subsingleton.elim _ _)
      hom_inv_id := by apply pullback.hom_ext <;> simp
      inv_hom_id := by apply prod.hom_ext <;> simp }
  let c : yoneda.obj (Z ⨯ Z) ≅ pullback t t :=
    asIso (prodComparison yoneda Z Z) ≪≫ prod.mapIso e e ≪≫ ep.symm
  intro T a
  obtain ⟨V, p, q, hp, hc⟩ := closedRepresentable_yonedaMap d T (a ≫ c.inv)
  refine ⟨V, p, q ≫ e.hom, ?_, hc⟩
  apply hp.of_iso (Iso.refl _) e (Iso.refl _) c
  · simp
  · simp
  · apply (cancel_mono ep.hom).mp
    change (yoneda.map d ≫ (prodComparison yoneda Z Z ≫
      prod.map e.hom e.hom ≫ ep.inv)) ≫ ep.hom =
        (e.hom ≫ AlgebraicSpace.diagonalPresheafMap t) ≫ ep.hom
    rw [Category.assoc, Category.assoc, Category.assoc, ep.inv_hom_id, Category.comp_id]
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, prodComparison_fst_assoc]
      rw [← yoneda.map_comp_assoc]
      have hdf : d ≫ prod.fst = 𝟙 Z := prod.lift_fst _ _
      rw [hdf, yoneda.map_id, Category.id_comp]
      dsimp only [ep, AlgebraicSpace.diagonalPresheafMap]
      simp only [prod.lift_fst, pullback.lift_fst, Category.comp_id]
    · simp only [Category.assoc, prod.map_snd, prodComparison_snd_assoc]
      rw [← yoneda.map_comp_assoc]
      have hds : d ≫ prod.snd = 𝟙 Z := prod.lift_snd _ _
      rw [hds, yoneda.map_id, Category.id_comp]
      dsimp only [ep, AlgebraicSpace.diagonalPresheafMap]
      simp only [prod.lift_snd, pullback.lift_snd, Category.comp_id]
  · simp

private theorem fullValuativeLifting_of_presheafIso
    {B : Scheme.{u}} {P : (Over B)ᵒᵖ ⥤ Type u} (Z : Over B)
    (e : yoneda.obj Z ≅ P) (h : ValuativeCriterion Z.hom) :
    AlgebraicSpace.HasFullValuativeLifting P := by
  intro R _ _ _ K _ _ _ b a
  let T : Over B := Over.mk b
  let V : Over B := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b)
  let j : V ⟶ T := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl
  let g : V ⟶ Z := e.inv.app (op V) a
  let D : ValuativeCommSq Z.hom :=
    { R := R, K := K, i₁ := g.left, i₂ := b, commSq := ⟨g.w⟩ }
  obtain ⟨hD⟩ := h D
  let l : T ⟶ Z := Over.homMk hD.default.l hD.default.fac_right
  have hl : j ≫ l = g := by
    apply Over.OverMorphism.ext
    exact hD.default.fac_left
  refine ⟨e.hom.app (op T) l, ?_, ?_⟩
  · change P.map j.op (e.hom.app (op T) l) = a
    rw [← NatTrans.naturality_apply]
    change e.hom.app (op V) (j ≫ l) = a
    rw [hl]
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app (op V)) a
  · intro m hm
    let n : T ⟶ Z := e.inv.app (op T) m
    have hn : j ≫ n = g := by
      change (yoneda.obj Z).map j.op (e.inv.app (op T) m) = _
      rw [← NatTrans.naturality_apply, hm]
    let lift : D.commSq.LiftStruct :=
      ⟨n.left, congrArg Over.Hom.left hn, n.w⟩
    have hn' : n = l := by
      apply Over.OverMorphism.ext
      exact congrArg CommSq.LiftStruct.l (hD.uniq lift)
    have he := ConcreteCategory.congr_hom (e.inv_hom_id_app (op T)) m
    change e.hom.app (op T) n = m at he
    rw [← he, hn']

/-- A sheaf of arbitrary sets trivialized by a pro-etale cover is represented by
an etale geometric covering. The presheaf isomorphism gives bijections with
`Hom_X(U,Z)` natural in every object and arrow of the original site. The predicate
`ValuativeCriterion` asserts both existence and uniqueness of lifts for every
valuation ring and its fraction field. No quasi-compactness, finiteness, properness
or nonemptiness is required.

Source: Bhatt--Scholze, Definition 7.3.1(1),(3), p. 66, and Lemma 7.3.9,
pp. 67--68, Loc_X to Cov_X
(blueprint: lem-a1-proetale-local-system-representability).

Proof (the eight steps of the current DAG node, with universe transport explicit):
1. Apply `lem-weil-pbc-proetale-locally-classical-etale-cover` to the given
   trivializations. Its arbitrary-set locally constant case gives an etale sheaf G
   and F isomorphic to its comparison inverse image, without contractible refinement.
2. By `lem-a1-etale-sheaf-algebraic-space-realization`, realize G by an etale
   algebraic space E over X. The comparison identifies F with its pro-etale functor
   of points and identifies restriction with the actual base changes E_{U_i}.
   The separate size-explicit realization theorem constructs the presentation over
   the canonical enlarged base and identifies its actual local base changes.
3. The constant sheaf with value S is the coproduct of S copies of the terminal
   sheaf, by the constant-presheaf and sheafification adjunctions. Comparison inverse
   image preserves the terminal object and coproducts, using
   `lem-weil-pbc-left-adjoint-preserves-colimits`. It therefore preserves arbitrary
   constant set sheaves, including empty and infinite ones.
4. Combine step 2, step 3 and the trivializations. Full faithfulness from
   `det-pe-classical-sheaves-unit` lifts the isomorphisms to etale sheaves. Then
   `lem-galois-constant-sheaf-sets-representable` identifies the constants with the
   functors of D_i, the coproducts of S_i copies of U_i. Full faithfulness of
   etale-space realization yields actual isomorphisms E_{U_i} with D_i over U_i.
5. The self-product of D_i is the coproduct indexed by S_i times S_i. Its diagonal
   is the union of equal-index components and its complement the other components,
   so it is closed. A valuation-ring generic map selects one component. The base
   map into that component extends it, uniquely because Spec of a domain is
   connected. When S_i is empty there is no generic map. Use
   `lem-weil-pbc-scheme-coproduct-family` and the fibre-product construction.
6. Extract an fpqc family from CoversTop by a precoverage refinement and the
   quasi-compact-cover refinement lemma. Transport that family by canonical
   universe enlargement.
   Transport the separatedness
   and full valuation lifting property of step 5 along the actual isomorphisms
   E_{U_i} with D_i from step 4. Every scheme base change of their diagonals is a
   closed immersion by `lem-weil-pbc-closed-immersion-base-change`. Apply
   `lem-a1-space-fpqc-separated-valuative-descent` to descend both properties to E.
   This does not assert descent of arbitrary schemes.
7. Apply `lem-a1-separated-etale-space-scheme` to the etale space with closed
   diagonal. It is a scheme Z etale over X, without any quasi-compactness
   assumption. Retain the locally Noetherian hypothesis in the statement.
8. Compose the functor-of-points isomorphisms. Evaluation gives the requested
   bijections, and presheaf naturality gives compatibility with every site arrow.
   Transporting diagrams and their lifts across the representing isomorphism
   preserves exactly existence and uniqueness. No bound on the sheet sets is used.
-/
theorem proEtale_localSystem_representability (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (I : Type (u + 1)) (U : I → X.ProEt)
    (hcover : (ProEt.topology X).CoversTop U) (S : I → Type (u + 1))
    (htriv : ∀ i : I, Nonempty
      (((proEtaleSetRestriction X (U i)).obj F) ≅
        (constantSheaf (ProEt.topology (U i).left) (Type (u + 1))).obj (S i))) :
    ∃ (Z : Scheme.{u + 1}) (q : Z ⟶ schemeUniverseLift.{u, u + 1} X),
      Etale q ∧
      Nonempty (F.obj ≅ (proEtaleUniverseLiftToOver X).op ⋙ yoneda.obj (Over.mk q)) ∧
      ValuativeCriterion q := by
  obtain ⟨G, ⟨eF⟩⟩ := ((proEtale_locallyClassical_etaleCover X F).2.1
    ⟨I, U, hcover, fun i ↦ ⟨S i, htriv i⟩⟩).2
  obtain ⟨E, ⟨eE⟩, hlocal⟩ :=
    AlgebraicSpace.etaleSheaf_universeEnlarged_realization X G
  have hfpqc := fpqc_cover_universeLift X (fun i ↦ (U i).left)
    (fun i ↦ (U i).hom) (fpqc_cover_of_proEtale_coversTop X U hcover)
  have hproperties := AlgebraicSpace.closedDiagonal_and_fullValuativeLifting_of_fpqc_cover
    E.obj (fun i ↦ schemeUniverseLift.{u, u + 1} (U i).left)
    (fun i ↦ schemeUniverseLiftMap.{u, u + 1} (U i).hom) hfpqc (by
      intro i
      obtain ⟨ei⟩ := htriv i
      obtain ⟨eD⟩ := hlocal (U i) (S i)
        ⟨(proEtaleSetRestriction X (U i)).mapIso eF.symm ≪≫ ei⟩
      let D : Over (schemeUniverseLift.{u, u + 1} (U i).left) :=
        Over.mk (Sigma.desc (fun _ : S i ↦ 𝟙 (schemeUniverseLift.{u, u + 1} (U i).left)))
      have : IsSeparated D.hom :=
        coproductCopies_separated (schemeUniverseLift.{u, u + 1} (U i).left) (S i)
      exact ⟨separatedPresheaf_of_presheafIso D eD,
        fullValuativeLifting_of_presheafIso D eD
          (coproductCopies_valuative (schemeUniverseLift.{u, u + 1} (U i).left) (S i))⟩)
  obtain ⟨Z, ⟨eZ⟩, hZ⟩ := AlgebraicSpace.exists_scheme_of_separated_etale E.obj
    E.property (closedDiagonal_of_separatedPresheaf E.obj.obj.obj hproperties.1)
  refine ⟨Z.left, Z.hom, hZ, ?_, valuativeCriterion_of_presheafIso Z eZ hproperties.2⟩
  refine ⟨(sheafToPresheaf _ _).mapIso eF ≪≫ eE ≪≫ ?_⟩
  change (ProEt.forget X ⋙ Over.post AlgebraicSpace.schemeUniverseLiftFunctor).op ⋙
    E.obj.obj.obj ≅ (proEtaleUniverseLiftToOver X).op ⋙ yoneda.obj Z
  unfold proEtaleUniverseLiftToOver
  exact Functor.isoWhiskerLeft _ eZ.symm

end AlgebraicGeometry.Scheme
