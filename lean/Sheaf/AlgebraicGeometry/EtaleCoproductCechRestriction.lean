/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Sheaf.AlgebraicGeometry.EtaleFibreProductCoproduct
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover

/-!
# Bijectivity of restrictions to the summands of a coproduct Čech product

Source: Stacks Project, Étale Cohomology, Tag 03OZ, equation-sheaf-coprod.
(blueprint: lem-sc-etale-coproduct-cech-restriction-bijective)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

-- The site universal property gives a product because the base object is terminal.
private noncomputable def cech_product_iso
    {X : Scheme.{u}} {I : Type*} (U : I → X.Etale)
    (f : ∀ i, U i ⟶ Scheme.Etale.mk (𝟙 X)) (S : SiteCechComplex U f)
    (p : ℕ) (t : Fin (p + 1) → I) :
    (Scheme.Etale.forget X).obj (S.W p t) ≅
      ∏ᶜ fun k ↦ (Scheme.Etale.forget X).obj (U (t k)) := by
  classical
  let c : Fan (fun k ↦ U (t k)) := Fan.mk (S.W p t) (S.pr p t)
  have hu (s : Fan (fun k ↦ U (t k))) :
      ∃! b : s.pt ⟶ S.W p t, ∀ k, b ≫ S.pr p t k = s.proj k := by
    apply S.universal
    intro k
    apply (Scheme.Etale.forget X).map_injective
    apply Over.OverMorphism.ext
    simpa using ((Scheme.Etale.forget X).map (s.proj k ≫ f (t k))).w.trans
      ((Scheme.Etale.forget X).map (s.proj 0 ≫ f (t 0))).w.symm
  let h : IsLimit c := Fan.IsLimit.mk c (fun s ↦ (hu s).choose)
    (fun s k ↦ (hu s).choose_spec.1 k)
    (fun s m hm ↦ (hu s).choose_spec.2 m hm)
  let h' := (Fan.isLimitMapConeEquiv (Scheme.Etale.forget X) _ c)
    (isLimitOfPreserves (Scheme.Etale.forget X) h)
  exact h'.conePointUniqueUpToIso (productIsProduct _)

private theorem cech_product_iso_hom_π
    {X : Scheme.{u}} {I : Type*} (U : I → X.Etale)
    (f : ∀ i, U i ⟶ Scheme.Etale.mk (𝟙 X)) (S : SiteCechComplex U f)
    (p : ℕ) (t : Fin (p + 1) → I) (k : Fin (p + 1)) :
    (cech_product_iso U f S p t).hom ≫
      Pi.π (fun k ↦ (Scheme.Etale.forget X).obj (U (t k))) k =
        (Scheme.Etale.forget X).map (S.pr p t k) := by
  classical
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk k)

private theorem cech_coproduct_isColimit
    (X : Scheme.{u}) (I : Type u) [Finite I]
    (U : I → X.Etale) (f : ∀ i, U i ⟶ Scheme.Etale.mk (𝟙 X))
    (V : X.Etale) (fV : V ⟶ Scheme.Etale.mk (𝟙 X))
    (c : ∀ i, U i ⟶ V)
    (hc : IsColimit (Cofan.mk V.left (fun i ↦ (c i).left)))
    (hw : ∀ i, c i ≫ fV = f i)
    (S₁ : SiteCechComplex U f)
    (S₂ : SiteCechComplex (fun _ : Fin 1 ↦ V) (fun _ ↦ fV)) (p : ℕ)
    (g : ∀ t : Fin (p + 1) → I, S₁.W p t ⟶ S₂.W p (fun _ ↦ 0))
    (hg : ∀ t k, g t ≫ S₂.pr p (fun _ ↦ 0) k = S₁.pr p t k ≫ c (t k)) :
    Nonempty (IsColimit (Cofan.mk (S₂.W p (fun _ ↦ 0)).left
      (fun t ↦ (g t).left))) := by
  classical
  let B : I → Scheme.{u} := fun i ↦ (U i).left
  let A : I → Over X := fun i ↦ Over.mk (U i).hom
  let T : Over X := Over.mk (Sigma.desc (fun i ↦ (U i).hom))
  let P := fun t : Fin (p + 1) → I ↦ ∏ᶜ fun k ↦ A (t k)
  let eV : T ≅ (Scheme.Etale.forget X).obj V :=
    Over.isoMk ((coproductIsCoproduct B).coconePointUniqueUpToIso hc) (by
      apply Sigma.hom_ext
      intro i
      change Sigma.ι B i ≫
        ((coproductIsCoproduct B).coconePointUniqueUpToIso hc).hom ≫ V.hom =
          Sigma.ι B i ≫ Sigma.desc (fun i ↦ (U i).hom)
      have hi : Sigma.ι B i ≫
          ((coproductIsCoproduct B).coconePointUniqueUpToIso hc).hom = (c i).left :=
        IsColimit.comp_coconePointUniqueUpToIso_hom
          (coproductIsCoproduct B) hc (Discrete.mk i)
      rw [← Category.assoc, hi, Sigma.ι_desc]
      have hv : fV.left = V.hom := by
        have h := CategoryTheory.MorphismProperty.Over.w fV
        change fV.left ≫ 𝟙 X = V.hom at h
        exact (Category.comp_id _).symm.trans h
      have hi : (f i).left = (U i).hom := by
        have h := CategoryTheory.MorphismProperty.Over.w (f i)
        change (f i).left ≫ 𝟙 X = (U i).hom at h
        exact (Category.comp_id _).symm.trans h
      rw [← hv, ← hi]
      exact congrArg (fun h ↦ h.left) (hw i))
  have hV (i : I) :
      Over.homMk (Sigma.ι B i) (Sigma.ι_desc (fun i ↦ (U i).hom) i) ≫ eV.hom =
        (Scheme.Etale.forget X).map (c i) := by
    apply Over.OverMorphism.ext
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct B) hc (Discrete.mk i)
  let e₁ (t : Fin (p + 1) → I) :
      (Scheme.Etale.forget X).obj (S₁.W p t) ≅ P t := cech_product_iso U f S₁ p t
  let e₂ := cech_product_iso (fun _ : Fin 1 ↦ V) (fun _ ↦ fV) S₂ p (fun _ ↦ 0)
  obtain ⟨e, he, _⟩ := etale_fibre_product_coproduct X I B (fun i ↦ (U i).hom)
  -- Transport the canonical decomposition along the chosen-product comparisons.
  let E : (∐ fun t : Fin (p + 1) → I ↦
      (Scheme.Etale.forget X).obj (S₁.W p t)) ≅
      (Scheme.Etale.forget X).obj (S₂.W p (fun _ ↦ 0)) :=
    Sigma.mapIso e₁ ≪≫ e p ≪≫ Pi.mapIso (fun _ ↦ eV) ≪≫ e₂.symm
  have hE (t : Fin (p + 1) → I) :
      Sigma.ι _ t ≫ E.hom = (Scheme.Etale.forget X).map (g t) := by
    apply (cancel_mono e₂.hom).mp
    apply Pi.hom_ext
    intro k
    simp only [E, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, Sigma.ι_mapIso_hom_assoc, Pi.mapIso_hom_π]
    rw [reassoc_of% (he p t k)]
    rw [← Category.assoc, hV]
    rw [cech_product_iso_hom_π (fun _ : Fin 1 ↦ V) (fun _ ↦ fV) S₂ p
      (fun _ ↦ 0) k]
    change ((cech_product_iso U f S₁ p t).hom ≫
      Pi.π (fun k ↦ (Scheme.Etale.forget X).obj (U (t k))) k) ≫
        (Scheme.Etale.forget X).map (c (t k)) = _
    rw [cech_product_iso_hom_π U f S₁ p t k]
    simpa only [Functor.map_comp] using ((Scheme.Etale.forget X).congr_map (hg t k)).symm
  let hc' : IsColimit (Cofan.mk _ (fun t ↦ (Scheme.Etale.forget X).map (g t))) :=
    IsColimit.ofIsoColimit (coproductIsCoproduct _) (Cofan.ext E hE)
  exact ⟨(Cofan.isColimitMapCoconeEquiv (Over.forget X) _ _)
    (isColimitOfPreserves (Over.forget X) hc')⟩

private theorem sections_bijective_of_coproduct
    {X : Scheme.{u}} {J : Type u} (W : J → X.Etale) (V : X.Etale)
    (g : ∀ j, W j ⟶ V)
    (hc : IsColimit (Cofan.mk V.left (fun j ↦ (g j).left)))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (fun s : F.obj.obj (op V) ↦
      (fun j ↦ F.obj.map (g j).op s : ∀ j, F.obj.obj (op (W j)))) := by
  let A : J → Scheme.{u} := fun j ↦ (W j).left
  let e : (∐ A) ≅ V.left :=
    (coproductIsCoproduct A).coconePointUniqueUpToIso hc
  have he (j : J) : Sigma.ι A j ≫ e.hom = (g j).left := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct A) hc (Discrete.mk j)
  have hm (j : J) : Mono ((g j).left) := by
    rw [← he j]
    infer_instance
  have (j : J) : Mono (g j) := by
    exact (Scheme.Etale.forget X ⋙ Over.forget X).mono_of_mono_map (hm j)
  -- A scheme coproduct has monic, disjoint coprojections covering its point space.
  have hcov : Sieve.ofArrows W g ∈ X.smallEtaleTopology V := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, rfl⟩ := e.hom.surjective x
    obtain ⟨⟨j, z⟩, rfl⟩ := (sigmaMk A).surjective y
    refine Set.mem_iUnion.mpr ⟨j, z, ?_⟩
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, he]
  have hd (i j : J) (hij : i ≠ j) :
      Disjoint (Set.range (g i).left.base) (Set.range (g j).left.base) := by
    apply Set.disjoint_iff_forall_ne.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    have hxy' : Sigma.ι A i x = Sigma.ι A j y := by
      apply (ConcreteCategory.bijective_of_isIso (Scheme.forgetToTop.map e.hom)).1
      change e.hom (Sigma.ι A i x) = e.hom (Sigma.ι A j y)
      simpa only [← he, Scheme.Hom.comp_apply] using hxy
    exact hij (Sigma.mk.inj_iff.mp ((sigmaι_eq_iff A i j x y).mp hxy')).1
  let := Scheme.Etale.isIso_piLift_of_disjoint F W g hcov hd
  have hb := (Concrete.productEquiv (fun j ↦ F.obj.obj (op (W j)))).bijective.comp
    (ConcreteCategory.bijective_of_isIso (Pi.lift fun j ↦ F.obj.map (g j).op))
  convert hb using 1
  ext s j
  simp only [Function.comp_apply, Concrete.productEquiv_apply_apply,
    ← ConcreteCategory.comp_apply, Pi.lift_π]

/-- Restrictions from an iterated product of a disjoint union to the indexed
iterated products of its summands give a bijection on sheaf sections.
Source: Stacks Project, Étale Cohomology, Tag 03OZ, equation-sheaf-coprod.
(blueprint: lem-sc-etale-coproduct-cech-restriction-bijective)

Proof: the colimit hypothesis identifies V with the scheme coproduct of the U i,
with c i its coprojections. Apply etale_fibre_product_coproduct to their maps to X.
The universal properties of S₁ and S₂ identify its products with the chosen products
in this statement, including degree zero. Under these identifications g t is the
inclusion of the t-indexed summand: its projections are exactly pr followed by c.
The summands are disjoint open subschemes and cover the entire singleton product,
so they form an étale covering. Apply the proved upstream theorem
Scheme.Etale.isIso_piLift_of_disjoint to this monic disjoint covering. Its proof is
the sheaf equalizer argument: Restrictions on
self-intersections impose no condition; intersections of distinct summands are empty.
An abelian sheaf has zero sections on the empty scheme by the empty covering axiom.
Thus every tuple of sections glues uniquely, and the restriction map is bijective.
The sections indexed by maps to Fin 1 are a single section, since those maps are unique.
For empty I the singleton product is empty and both sides have one zero section.
No affineness, joint surjectivity over X, or differential compatibility is used. -/
theorem etale_coproduct_cech_restriction_bijective
    (X : Scheme.{u}) (I : Type u) [Finite I]
    (U : I → X.Etale) (f : ∀ i, U i ⟶ Scheme.Etale.mk (𝟙 X))
    (V : X.Etale) (fV : V ⟶ Scheme.Etale.mk (𝟙 X))
    (c : ∀ i, U i ⟶ V)
    (hc : IsColimit (Cofan.mk V.left (fun i => (c i).left)))
    (hw : ∀ i, c i ≫ fV = f i)
    (S₁ : SiteCechComplex U f)
    (S₂ : SiteCechComplex (fun _ : Fin 1 => V) (fun _ => fV))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    (g : ∀ t : Fin (p + 1) → I, S₁.W p t ⟶ S₂.W p (fun _ => 0))
    (hg : ∀ t k, g t ≫ S₂.pr p (fun _ => 0) k = S₁.pr p t k ≫ c (t k)) :
    Function.Bijective (fun s : S₂.cochains F.obj p =>
      (fun t => F.obj.map (g t).op (s (fun _ => 0)) : S₁.cochains F.obj p)) := by
  classical
  obtain ⟨hcop⟩ := cech_coproduct_isColimit X I U f V fV c hc hw S₁ S₂ p g hg
  have hb := sections_bijective_of_coproduct (S₁.W p) (S₂.W p (fun _ ↦ 0)) g hcop F
  let ev : S₂.cochains F.obj p ≃ F.obj.obj (op (S₂.W p (fun _ ↦ 0))) :=
    Equiv.piUnique (fun t ↦ F.obj.obj (op (S₂.W p t)))
  exact hb.comp ev.bijective

end AlgebraicGeometry
