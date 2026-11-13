/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernel
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelFactorization
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.TorsionControlledFormalRestriction
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-! # Factorization through a restricted formal kernel

Source: Stacks Project, Lemma 087X (lemma-inverse-systems-abelian), construction
(a)--(d) and the final sentence of its proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem restrictedKernelImage {X : Scheme.{u}} (U : X.Opens)
    {M N P : X.Modules} (f : M ⟶ N) (g : M ⟶ P) :
    ∃ e : (Scheme.Modules.restrictFunctor U.ι).obj
        (Abelian.image (kernel.ι f ≫ g)) ≅
        Abelian.image (kernel.ι ((Scheme.Modules.restrictFunctor U.ι).map f) ≫
          (Scheme.Modules.restrictFunctor U.ι).map g),
      e.hom ≫ Abelian.image.ι _ =
        (Scheme.Modules.restrictFunctor U.ι).map (Abelian.image.ι (kernel.ι f ≫ g)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let a := PreservesKernel.iso R f
  let v := kernel.ι (R.map f) ≫ R.map g
  have hv : R.map (kernel.ι f ≫ g) = a.hom ≫ v := by
    simp [v, a, ← Category.assoc, PreservesKernel.iso_hom]
  let b : Abelian.image (R.map (kernel.ι f ≫ g)) ≅ Abelian.image v :=
    Abelian.imageIsoImage _ ≪≫ image.eqToIso hv ≪≫
      asIso (image.preComp a.hom v) ≪≫ (Abelian.imageIsoImage v).symm
  have hb : b.hom ≫ Abelian.image.ι v =
      Abelian.image.ι (R.map (kernel.ι f ≫ g)) := by
    dsimp only [b, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    simp only [Category.assoc]
    simp only [Abelian.image.ι]
    rw [← Abelian.imageIsoImage_hom_comp_image_ι v,
      Iso.inv_hom_id_assoc, image.preComp_ι, ← image.eq_fac,
      Abelian.imageIsoImage_hom_comp_image_ι]
  refine ⟨Abelian.PreservesImage.iso R (kernel.ι f ≫ g) ≪≫ b, ?_⟩
  change (Abelian.PreservesImage.iso R (kernel.ι f ≫ g)).hom ≫ b.hom ≫ _ = _
  rw [hb, Abelian.PreservesImage.iso_hom_ι]

set_option backward.isDefEq.respectTransparency false in
/-- A morphism killed by a restricted formal-module morphism factors through
its restricted kernel arrow. This concerns kernels only, with no cokernel or finite
product preservation assertion.

Source: Stacks Project, Lemma 087X (lemma-inverse-systems-abelian), construction
(a)--(d) and the final sentence of its proof; step 2 of
lem-weil-pbc-coherent-formal-modules-restriction-limits. -/
theorem coherentFormalModules_restriction_kernel_factorization {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
    [IsNoetherian U.toScheme] {F G : CoherentFormalModule X I} (α : F ⟶ G)
    (c : KernelFork α) (hc : IsLimit c)
    (T : CoherentFormalModule U.toScheme (I.comap U.ι))
    (γ : T ⟶ (coherentFormalModulesRestriction I U).obj F)
    (hγ : γ ≫ (coherentFormalModulesRestriction I U).map α = 0) :
    ∃ δ : T ⟶ (coherentFormalModulesRestriction I U).obj c.pt,
      δ ≫ (coherentFormalModulesRestriction I U).map c.ι = γ := by
  classical
  let R := Scheme.Modules.restrictFunctor U.ι
  let r := coherentFormalModulesRestriction I U
  obtain ⟨d, _, S, j, hS, K, ι, e, htrans, hcomp, hzero, _⟩ :=
    coherentFormalModule_kernel I F G α
  have hq (m : ℕ) : (S.obj (Opposite.op m)).IsQuasicoherent := by
    have : (F.obj.obj (Opposite.op (m + d))).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
        (F.property.1 (m + d))).1
    have : (G.obj.obj (Opposite.op (m + d))).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
        (G.property.1 (m + d))).1
    have : (F.obj.obj (Opposite.op m)).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
        (F.property.1 m)).1
    have := Scheme.Modules.isQuasicoherent_kernel (α.hom.app (Opposite.op (m + d)))
    let f := kernel.ι (α.hom.app (Opposite.op (m + d))) ≫
      F.obj.map (homOfLE (Nat.le_add_right m d)).op
    have := Scheme.Modules.isQuasicoherent_cokernel f
    have := Scheme.Modules.isQuasicoherent_kernel (cokernel.π f)
    obtain ⟨a, _⟩ := hS m
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso a.symm
      (inferInstanceAs (Abelian.image (kernel.ι (α.hom.app (Opposite.op (m + d))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m d)).op)).IsQuasicoherent)
  let j' := Functor.whiskerRight j R
  have hS' : ∀ m : ℕ, ∃ a : (S ⋙ R).obj (Opposite.op m) ≅
      Abelian.image (kernel.ι ((r.map α).hom.app (Opposite.op (m + d))) ≫
        (r.obj F).obj.map (homOfLE (Nat.le_add_right m d)).op),
      a.hom ≫ Abelian.image.ι _ = j'.app (Opposite.op m) := by
    intro m
    obtain ⟨a, ha⟩ := hS m
    obtain ⟨b, hb⟩ := restrictedKernelImage U (α.hom.app (Opposite.op (m + d)))
      (F.obj.map (homOfLE (Nat.le_add_right m d)).op)
    refine ⟨R.mapIso a ≪≫ b, ?_⟩
    change R.map a.hom ≫ b.hom ≫
      Abelian.image.ι (kernel.ι (R.map (α.hom.app (Opposite.op (m + d)))) ≫
        R.map (F.obj.map (homOfLE (Nat.le_add_right m d)).op)) = R.map (j.app (Opposite.op m))
    rw [hb, ← R.map_comp, ha]
  let e' (n : ℕ) :
      formalModuleQuotient (I.comap U.ι) (n + 1) ((S ⋙ R).obj (Opposite.op (n + d))) ≅
        (r.obj K).obj.obj (Opposite.op n) :=
    let := hq (n + d)
    restrictionQuotientIso I (S.obj (Opposite.op (n + d))) U (n + 1) ≪≫ R.mapIso (e n)
  have he' (n : ℕ) :
      formalModuleQuotientπ (I.comap U.ι) (n + 1) ((S ⋙ R).obj (Opposite.op (n + d))) ≫
          (e' n).hom =
        R.map (formalModuleQuotientπ I (n + 1) (S.obj (Opposite.op (n + d))) ≫ (e n).hom) := by
    have := hq (n + d)
    dsimp only [e', Iso.trans_hom, Functor.mapIso_hom]
    simpa only [R, r, coherentFormalModulesRestriction, Category.assoc,
      Functor.map_comp, Functor.comp_obj] using
      congrArg (· ≫ R.map (e n).hom)
        (restrictionQuotientIso_π I (S.obj (Opposite.op (n + d))) U (n + 1))
  have htrans' (n : ℕ) :
      formalModuleQuotientπ (I.comap U.ι) (n + 2)
          ((S ⋙ R).obj (Opposite.op (n + 1 + d))) ≫
          (e' (n + 1)).hom ≫ (r.obj K).obj.map (homOfLE (Nat.le_succ n)).op =
        (S ⋙ R).map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) d)).op ≫
          formalModuleQuotientπ (I.comap U.ι) (n + 1)
            ((S ⋙ R).obj (Opposite.op (n + d))) ≫ (e' n).hom := by
    rw [← Category.assoc, he', he']
    exact (R.congr_map (htrans n)).trans (by simp only [R.map_comp]; rfl)
  have hcomp' (n : ℕ) :
      formalModuleQuotientπ (I.comap U.ι) (n + 1) ((S ⋙ R).obj (Opposite.op (n + d))) ≫
          (e' n).hom ≫ (r.map ι).hom.app (Opposite.op n) =
        j'.app (Opposite.op (n + d)) ≫ (r.obj F).obj.map (homOfLE (Nat.le_add_right n d)).op := by
    rw [← Category.assoc, he']
    exact (R.congr_map (hcomp n)).trans (by simp only [R.map_comp]; rfl)
  obtain ⟨δ, hδ⟩ := coherentFormalModule_kernel_factorization (I.comap U.ι)
    (r.obj F) (r.obj G) (r.map α) d (S ⋙ R) j' hS' (r.obj K) (r.map ι)
    e' htrans' hcomp' T γ hγ
  obtain ⟨k, hk⟩ := KernelFork.IsLimit.lift' hc ι hzero
  refine ⟨δ ≫ r.map k, ?_⟩
  rw [Category.assoc, ← r.map_comp, hk, hδ]


end AlgebraicGeometry
