/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
import WeilConjectures.AlgebraicGeometry.HigherDirectImageLocalClassVanishing
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOverCoherence

/-! # Eventual vanishing of affine higher-image sections

## References

* Stacks Project, Tags 09Z1, 03Q8 and 0738.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- A stage section with zero limit image becomes zero at a later stage
(Stacks, Tags 09Z1 and 0738). -/
theorem exists_higher_image_affine_class_eq_zero
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (V : S.Etale) [IsAffine V.left] (i : I)
    (y : (higherDirectImage Λ ((D.obj i).hom ≫ k) q
      ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj.obj (op V))
    (hy : ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op V)) y = 0) :
    ∃ (j : I) (f : j ⟶ i),
      ((higherDirectImageOverMap Λ k G q (D.map f)).hom.app (op V)) y = 0 := by
  classical
  obtain ⟨R, hR, hlocal⟩ := exists_higher_image_local_class_eq_zero
    Λ k G q D c hc V i y hy
  let A := R.arrows.category
  let U (a : A) : S.Etale := a.obj.left
  let r (a : A) : U a ⟶ V := a.obj.hom
  have hr : Sieve.ofArrows U r ∈ S.smallEtaleTopology V := by
    rw [show Sieve.ofArrows U r = R from Sieve.ofArrows_category R]
    exact hR
  have hcover := (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mp hr
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun a ↦ Set.range (r a).left)
    (fun a ↦ (r a).left.isOpenMap.isOpen_range) (by rw [hcover])
  have htcover : Sieve.ofArrows (fun a : t ↦ U a.val) (fun a : t ↦ r a.val) ∈
      S.smallEtaleTopology V := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hx⟩
  let K (j : I) := higherDirectImage Λ ((D.obj j).hom ≫ k) q
    ((((D.obj j).hom)^*[ModuleCat.{u + 1} Λ]).obj G)
  have hzero : ∀ a : t, ∃ (j : I) (f : j ⟶ i),
      ((higherDirectImageOverMap Λ k G q (D.map f)).hom.app (op (U a.val)))
        ((K i).obj.map (r a.val).op y) = 0 := by
    intro a
    exact hlocal (U a.val) (r a.val) a.val.property
  choose j f hf using hzero
  obtain ⟨l, g, b, hb⟩ := IsCofiltered.wideCospan f
  let T := higherDirectImageOverMap Λ k G q (D.map g)
  have hres : ∀ a : t, (K l).obj.map (r a.val).op (T.hom.app (op V) y) = 0 := by
    intro a
    have hnat := congrArg (fun z ↦ z y) (T.hom.naturality (r a.val).op)
    simp only [ModuleCat.comp_apply] at hnat
    rw [← hnat]
    change ((higherDirectImageOverMap Λ k G q (D.map g)).hom.app (op (U a.val)))
      ((K i).obj.map (r a.val).op y) = 0
    rw [← hb a, D.map_comp,
      (higher_image_over_transition_coherence Λ k G q).2]
    change ((higherDirectImageOverMap Λ k G q (D.map (b a))).hom.app (op (U a.val)))
      (((higherDirectImageOverMap Λ k G q (D.map (f a))).hom.app (op (U a.val)))
        ((K i).obj.map (r a.val).op y)) = 0
    rw [hf a, map_zero]
  refine ⟨l, g, ?_⟩
  let e : ModuleCat.of Λ Λ ⟶ (K l).obj.obj (op V) :=
    ModuleCat.ofHom
      { toFun := fun n ↦ n • (T.hom.app (op V) y)
        map_add' := fun m n ↦ add_smul _ _ _
        map_smul' := fun m n ↦ mul_smul _ _ _ }
  have he : e = 0 := by
    apply (K l).property.hom_ext_ofArrows (fun a : t ↦ r a.val) htcover
    intro a
    rw [Limits.zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro n
    change (K l).obj.map (r a.val).op (n • (T.hom.app (op V) y)) = 0
    rw [map_smul, hres a, smul_zero]
  have h := congrArg (fun z ↦ z (1 : Λ)) he
  change (1 : Λ) • (T.hom.app (op V) y) = 0 at h
  simpa only [one_smul] using h


end AlgebraicGeometry.Etale
