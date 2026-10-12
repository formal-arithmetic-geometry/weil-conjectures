/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.AlgebraicGeometry.EtaleCoproductCechRestriction

/-!
# Čech complex of a finite affine étale covering and its disjoint union

Source: Stacks Project, `literature/stacks-project/etale-cohomology.tex`,
Lemma Tag 03OZ (blueprint: lem-sc-etale-standard-cover-cech).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry

private theorem cech_projection_ext
    {C : Type*} [Category C] {I : Type*} {B : C}
    {U : I → C} {f : ∀ i, U i ⟶ B} (S : SiteCechComplex U f)
    {p : ℕ} {t : Fin (p + 1) → I} {Z : C}
    (a b : Z ⟶ S.W p t) (h : ∀ k, a ≫ S.pr p t k = b ≫ S.pr p t k) :
    a = b := by
  have hc (k) : (b ≫ S.pr p t k) ≫ f (t k) =
      (b ≫ S.pr p t 0) ≫ f (t 0) := by
    simp only [Category.assoc, S.comm]
  obtain ⟨c, _, hu⟩ := S.universal p t Z (fun k => b ≫ S.pr p t k) hc
  exact (hu a h).trans (hu b (fun _ => rfl)).symm

/-- A finite affine étale covering may be replaced by its disjoint-union cover, and
this replacement identifies the associated Čech complexes of every abelian sheaf.
Source: Stacks Project, Lemma Tag 03OZ (blueprint: lem-sc-etale-standard-cover-cech).

Proof: the finite coproduct is affine and its induced map is étale and surjective;
etale maps are flat, and a flat map with surjective spectrum is faithfully flat.
The fibre products of the coproduct distribute over the finite family of fibre products.
The sheaf equalizer axiom for the coproduct summands gives the product of section groups,
and the distribution isomorphisms commute with all face maps, hence induce an isomorphism
of Čech complexes. -/
theorem etale_standard_cover_cech
    (A : CommRingCat.{u}) (X : Scheme.{u})
    (hX : X = AlgebraicGeometry.Spec A) (I : Type u) [Finite I]
    (U : I → X.Etale)
    (hU : ∀ i : I, IsAffine (U i).left)
    (f : ∀ i : I, U i ⟶ Scheme.Etale.mk (𝟙 X))
    (hcover : Sieve.ofArrows U f ∈ X.smallEtaleTopology _)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ (V : X.Etale) (fV : V ⟶ Scheme.Etale.mk (𝟙 X)),
      V.left = (∐ fun i : I => (U i).left) ∧
      IsAffine V.left ∧ Surjective V.hom ∧ Etale V.hom ∧
      RingHom.FaithfullyFlat ((Scheme.Γ.map V.hom.op).hom) ∧
      ∃ (S₁ : CategoryTheory.SiteCechComplex U f)
        (S₂ : CategoryTheory.SiteCechComplex (fun _ : Fin 1 => V)
          (fun _ : Fin 1 => fV)),
        Nonempty (S₂.complex F.obj ≅ S₁.complex F.obj) := by
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.isDefEq.respectTransparency false in
  classical
  have hUi (i : I) : IsAffine (U i).left := hU i
  have hXi : IsAffine X := by rw [hX]; infer_instance
  let u : ∀ i : I, (U i).left ⟶ X := fun i => (U i).hom
  have hu : Etale (Sigma.desc u) :=
    IsZariskiLocalAtSource.sigmaDesc (fun i => (U i).prop)
  let V : X.Etale := Scheme.Etale.mk (Sigma.desc u)
  let fV : V ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk (Sigma.desc u) (by
      change Sigma.desc u ≫ 𝟙 X = Sigma.desc u
      simp)
  have hf (i : I) : (f i).left = (U i).hom := by
    have h := (f i).w
    change (f i).left ≫ 𝟙 X = (U i).hom at h
    exact (Category.comp_id _).symm.trans h
  have hs : Surjective (Sigma.desc u) := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mp hcover
    change (⋃ i, Set.range ((f i).left : (U i).left ⟶ X)) = Set.univ at h
    simp only [hf] at h
    exact h
  have hVa : IsAffine V.left := by
    change IsAffine (∐ fun i : I => (U i).left)
    infer_instance
  have hff : RingHom.FaithfullyFlat ((Scheme.Γ.map V.hom.op).hom) := by
    change RingHom.FaithfullyFlat (Sigma.desc u).appTop.hom
    exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (Sigma.desc u)).mp
      ⟨inferInstance, hs⟩
  refine ⟨V, fV, rfl, inferInstance, hs, hu, hff, ?_⟩
  let K := X.smallEtaleTopology.toPrecoverage
  obtain ⟨S₁⟩ := SiteCechComplex.exists_of_covering K hcover
  have hcoverV : Sieve.ofArrows (fun _ : Fin 1 => V) (fun _ => fV) ∈
      X.smallEtaleTopology _ := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    change (⋃ _ : Fin 1, Set.range (Sigma.desc u)) = Set.univ
    simpa only [Set.iUnion_const] using (range_eq_univ (Sigma.desc u))
  obtain ⟨S₂⟩ := SiteCechComplex.exists_of_covering K hcoverV
  let c : ∀ i : I, U i ⟶ V := fun i =>
    MorphismProperty.Over.homMk (Sigma.ι (fun i => (U i).left) i)
      (Sigma.ι_desc u i)
  have hc : IsColimit (Cofan.mk V.left (fun i => (c i).left)) := by
    change IsColimit (Cofan.mk (∐ fun i => (U i).left)
      (fun i => Sigma.ι (fun i => (U i).left) i))
    exact coproductIsCoproduct _
  have hw (i : I) : c i ≫ fV = f i := by
    apply MorphismProperty.Over.Hom.ext
    change Sigma.ι (fun i => (U i).left) i ≫ Sigma.desc u = (f i).left
    exact (Sigma.ι_desc u i).trans (hf i).symm
  have hg_exists (p : ℕ) (t : Fin (p + 1) → I) :
      ∃ b : S₁.W p t ⟶ S₂.W p (fun _ => 0),
        ∀ k, b ≫ S₂.pr p (fun _ => 0) k = S₁.pr p t k ≫ c (t k) := by
    obtain ⟨b, hb, _⟩ := S₂.universal p (fun _ => 0) (S₁.W p t)
      (fun k => S₁.pr p t k ≫ c (t k)) (fun k => by
        simp only [Category.assoc, hw, S₁.comm])
    exact ⟨b, hb⟩
  let g (p : ℕ) (t : Fin (p + 1) → I) := (hg_exists p t).choose
  have hg (p t k) := (hg_exists p t).choose_spec k
  have hg_face (p : ℕ) (t : Fin (p + 2) → I) (j : Fin (p + 2)) :
      S₁.indexMap t j.succAbove ≫ g p (t ∘ j.succAbove) =
        g (p + 1) t ≫ S₂.indexMap (fun _ => 0) j.succAbove := by
    apply cech_projection_ext S₂
    intro k
    simp only [Category.assoc]
    rw [hg, ← Category.assoc, S₁.indexMap_pr]
    have h₂ := S₂.indexMap_pr (fun _ : Fin (p + 2) => 0) j.succAbove k
    change S₂.indexMap (fun _ => 0) j.succAbove ≫ S₂.pr p (fun _ => 0) k =
      S₂.pr (p + 1) (fun _ => 0) (j.succAbove k) at h₂
    rw [h₂, hg]
    rfl
  let m (p : ℕ) : S₂.cochains F.obj p ⟶ S₁.cochains F.obj p :=
    AddCommGrpCat.ofHom
      { toFun := fun s t => F.obj.map (g p t).op (s (fun _ => 0))
        map_zero' := by funext t; exact (F.obj.map (g p t).op).hom.map_zero
        map_add' := by
          intro a b
          funext t
          exact (F.obj.map (g p t).op).hom.map_add _ _ }
  have hm (p : ℕ) : Function.Bijective (m p) :=
    etale_coproduct_cech_restriction_bijective X I U f V fV c hc hw S₁ S₂ F p
      (g p) (hg p)
  have hm_comm (p : ℕ) : m p ≫ (S₁.complex F.obj).d p (p + 1) =
      (S₂.complex F.obj).d p (p + 1) ≫ m (p + 1) := by
    simp only [SiteCechComplex.complex, CochainComplex.of_d]
    apply AddCommGrpCat.ext
    intro s
    funext t
    change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      F.obj.map (S₁.indexMap t j.succAbove).op
        (F.obj.map (g p (t ∘ j.succAbove)).op (s (fun _ => 0)))) =
      F.obj.map (g (p + 1) t).op (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        F.obj.map (S₂.indexMap (fun _ => 0) j.succAbove).op (s (fun _ => 0)))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul]
    congr 1
    have h := congrArg (fun a => F.obj.map a.op) (hg_face p t j)
    simp only [op_comp, F.obj.map_comp] at h
    exact congrArg (fun a => a (s (fun _ => 0))) h
  let e (p : ℕ) : S₂.cochains F.obj p ≅ S₁.cochains F.obj p :=
    (AddEquiv.ofBijective (m p).hom (hm p)).toAddCommGrpIso
  refine ⟨S₁, S₂, ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩⟩
  intro p q hpq
  obtain rfl : p + 1 = q := hpq
  exact hm_comm p

end AlgebraicGeometry
