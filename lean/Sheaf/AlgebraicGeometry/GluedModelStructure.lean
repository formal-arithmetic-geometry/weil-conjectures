/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Gluing
import Sheaf.AlgebraicGeometry.DescendedOverlapGlueData

/-!
# Descended charts with compatible local maps

Source: Stacks Project, Descent, Tag 0AP4, construction of the descended overlaps.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/-- An fpqc singleton is flat and surjective, hence an epimorphism (Stacks Tag 02VW). -/
private theorem epi_of_fpqc_singleton {A B : Scheme.{u}} (r : A ⟶ B)
    (hr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage B) : Epi r := by
  obtain ⟨hsurj, hflat⟩ := (Scheme.singleton_mem_precoverage_iff (P := @Flat) r).mp hr.2
  have : Surjective r := ⟨hsurj⟩
  have : Flat r := hflat
  exact Flat.epi_of_flat_of_surjective r

/-- Descended local models admit covering open embeddings for which the local maps agree.

Source: Stacks Project, Descent, Tag 0AP4, proof before the final global map is glued.
(blueprint: lem-pd-glued-model-compatible-charts).

Proof: On U_i take the inverse image of U_k under the inclusion into V. The restricted
transports agree with D, and inverse transport shows that this open is invariant under E_i.
The cartesian square identifies U_i with W_i ×_Y X. Its projection q_i is an fpqc cover
by base change of p, and transport invariance identifies E_i with the canonical datum.
Descent of opens (03N0) gives an open W_ik of W_i pulling back to U_i ∩ U_k.
The identity on U_i ∩ U_k is compatible with both restricted data, so full faithfulness
of fpqc descent (02W0) descends it to an isomorphism W_ik ≅ W_ki over Y.
Descend the inverse as well; faithfulness proves the inverse identities and triple cocycle.
Uniqueness of the descended opens identifies the domains on triple intersections.
Glue these schemes and transitions using Scheme.GlueData. Its chart inclusions are open
immersions and jointly surjective. The maps W_i → Y agree on the descended overlaps,
so their multicoequalizer descent defines a map from the glued scheme to Y.
The local composites q_i ≫ j_i agree on U_i ∩ U_k by the gluing relation for W_ik:
both factor through its descended transition. The pullback of the inclusions U_i → V
and U_k → V is precisely this intersection, giving the displayed overlap equation.
No global map from V is constructed here. If I is empty, hcover forces V empty;
the empty gluing and its unique map to Y satisfy the assertions vacuously. -/
theorem exists_glued_model_structure
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y)
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type u} (U : I → V.left.Opens)
    (hcover : ∀ x : V.left, ∃ i, x ∈ U i)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (W : I → Over Y) (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hinv : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ q i = a.left ≫ q i) :
    ∃ (W₀ : Over Y) (j : ∀ i, (W i).left ⟶ W₀.left),
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w) ∧
      (∀ i, j i ≫ W₀.hom = (W i).hom) ∧
      (∀ i k, pullback.fst (U i).ι (U k).ι ≫ q i ≫ j i =
        pullback.snd (U i).ι (U k).ι ≫ q k ≫ j k) := by
  have _cover := hcover
  obtain ⟨Z, f, t, hf, hdiag, ht, ⟨t', ht', hcoc⟩, hlift⟩ :=
    exists_descended_overlap_glue_data hp D U E hcompat W q hcart hinv
  have hq (i : I) : Presieve.singleton (q i) ∈ Scheme.fpqcPrecoverage (W i).left := by
    rw [← Presieve.ofArrows_pUnit.{0}] at hp ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} => p) hp
      (W i).hom (fun _ => q i) (fun _ => (U i).ι ≫ V.hom) (fun _ => hcart i)
  have hbase (i k : I) : f i k ≫ (W i).hom = t i k ≫ f k i ≫ (W k).hom := by
    obtain ⟨r, hr, hr₂⟩ := hlift i k
    have hqr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage (Z (i, k)) := by
      have hqi := hq i
      rw [← Presieve.ofArrows_pUnit.{0}] at hqi ⊢
      exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} => q i) hqi
        (f i k) (fun _ => r) (fun _ => pullback.fst (U i).ι (U k).ι) (fun _ => hr)
    have : Epi r := epi_of_fpqc_singleton r hqr
    apply (cancel_epi r).mp
    calc
      r ≫ f i k ≫ (W i).hom =
          pullback.fst (U i).ι (U k).ι ≫ q i ≫ (W i).hom := by
        simpa only [Category.assoc] using congrArg (fun a => a ≫ (W i).hom) hr.w
      _ = pullback.fst (U i).ι (U k).ι ≫ (U i).ι ≫ V.hom ≫ p := by
        rw [(hcart i).w]; simp only [Category.assoc]
      _ = pullback.snd (U i).ι (U k).ι ≫ (U k).ι ≫ V.hom ≫ p := by
        rw [pullback.condition_assoc]
      _ = pullback.snd (U i).ι (U k).ι ≫ q k ≫ (W k).hom := by
        rw [(hcart k).w]; simp only [Category.assoc]
      _ = r ≫ t i k ≫ f k i ≫ (W k).hom := by
        simpa only [Category.assoc] using congrArg (fun a => a ≫ (W k).hom) hr₂.symm
  let G : Scheme.GlueData := {
    J := I
    U := fun i => (W i).left
    V := Z
    f := f
    f_open := hf
    f_mono := fun i k => by
      have := hf i k
      infer_instance
    f_id := hdiag
    t := t
    t_id := ht
    t' := t'
    t_fac := ht'
    cocycle := hcoc }
  have : HasMulticoequalizer G.toGlueData.diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram G
  let a : G.glued ⟶ Y := Multicoequalizer.desc G.toGlueData.diagram Y
    (fun i => (W i).hom) (fun ik => hbase ik.1 ik.2)
  refine ⟨Over.mk a, G.ι, ?_, ?_, ?_, ?_⟩
  · intro i
    exact G.ι_isOpenImmersion i
  · intro w
    exact G.ι_jointly_surjective w
  · intro i
    exact Multicoequalizer.π_desc G.toGlueData.diagram Y
      (fun i => (W i).hom) (fun ik => hbase ik.1 ik.2) i
  · intro i k
    obtain ⟨r, hr, hr₂⟩ := hlift i k
    have hr₁ := hr.w
    calc
      pullback.fst (U i).ι (U k).ι ≫ q i ≫ G.ι i =
          r ≫ f i k ≫ G.ι i := by
        simpa only [Category.assoc] using congrArg (fun a => a ≫ G.ι i) hr₁.symm
      _ = r ≫ t i k ≫ f k i ≫ G.ι k := by
        rw [← G.glue_condition i k]
      _ = pullback.snd (U i).ι (U k).ι ≫ q k ≫ G.ι k := by
        simpa only [Category.assoc] using congrArg (fun a => a ≫ G.ι k) hr₂


end CategoryTheory.Over.DescentDatum
