/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.CategoryTheory.LocalModuleIso

/-! # Constant sections of local module Hom and Isom presheaves

Source: Stacks Project, Modules on Sites, Tag 093T.
(blueprint: lem-sf-constant-local-module-isom-bijective).
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {D : Type v} [Category.{u} D]
  (F : D ⥤ SheafOfModules.{u} R) (M N P : D)

/-- The canonical constant-presheaf map into local module morphisms. -/
def constantLocalHom : (Functor.const Cᵒᵖ).obj (M ⟶ N) ⟶ localHom (F.obj M) (F.obj N) where
  app U := ↾fun a ↦ (localHomEquiv _ _ U).symm ((overFunctor R U.unop).map (F.map a))
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    ext x
    rfl

lemma constantLocalHom_equiv (U : Cᵒᵖ) (a : M ⟶ N) :
    localHomEquiv _ _ U ((constantLocalHom F M N).app U a) =
      (overFunctor R U.unop).map (F.map a) :=
  (localHomEquiv _ _ U).apply_symm_apply _

lemma constantLocalHom_comp (U : Cᵒᵖ) (a : M ⟶ N) (b : N ⟶ P) :
    (constantLocalHom F M P).app U (a ≫ b) =
      localHomComp _ _ _ ((constantLocalHom F M N).app U a)
        ((constantLocalHom F N P).app U b) := by
  apply (localHomEquiv _ _ U).injective
  simp [constantLocalHom, localHomComp]

lemma constantLocalHom_id (U : Cᵒᵖ) :
    (constantLocalHom F M M).app U (𝟙 M) = localHomId (F.obj M) U := by
  apply (localHomEquiv _ _ U).injective
  simp [constantLocalHom, localHomId]

/-- The canonical constant-presheaf map into local module isomorphisms. -/
def constantLocalIso : (Functor.const Cᵒᵖ).obj (M ≅ N) ⟶ localIso (F.obj M) (F.obj N) where
  app U := ↾fun a ↦ (overFunctor R U.unop).mapIso (F.mapIso a)
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Iso.ext
    ext W x
    rfl

lemma constantLocalIso_hom (U : Cᵒᵖ) (a : M ≅ N) :
    (localHomEquiv _ _ U).symm ((constantLocalIso F M N).app U a).hom =
      (constantLocalHom F M N).app U a.hom := rfl

lemma constantLocalIso_inv (U : Cᵒᵖ) (a : M ≅ N) :
    (localHomEquiv _ _ U).symm ((constantLocalIso F M N).app U a).inv =
      (constantLocalHom F N M).app U a.inv := rfl

/-- The constant Isom map is locally injective if the corresponding Hom map is. -/
theorem constantLocalIso_locallyInjective
    [hMN : Presheaf.IsLocallyInjective J (constantLocalHom F M N)] :
    Presheaf.IsLocallyInjective J (constantLocalIso F M N) where
  equalizerSieve_mem {U} a b hab := by
    have h := congrArg (fun e ↦ (localHomEquiv (F.obj M) (F.obj N) U).symm e.hom) hab
    rw [constantLocalIso_hom, constantLocalIso_hom] at h
    have hh := hMN.equalizerSieve_mem (X := U) a.hom b.hom h
    apply J.superset_covering _ hh
    intro V f hf
    change a = b
    apply Iso.ext
    exact hf

/-- Lift forward and backward maps, then enforce the two inverse identities locally. -/
theorem constantLocalIso_locallySurjective
    [sMN : Presheaf.IsLocallySurjective J (constantLocalHom F M N)]
    [sNM : Presheaf.IsLocallySurjective J (constantLocalHom F N M)]
    [iMM : Presheaf.IsLocallyInjective J (constantLocalHom F M M)]
    [iNN : Presheaf.IsLocallyInjective J (constantLocalHom F N N)] :
    Presheaf.IsLocallySurjective J (constantLocalIso F M N) where
  imageSieve_mem {U} e := by
    let a := (localHomEquiv _ _ (op U)).symm e.hom
    let b := (localHomEquiv _ _ (op U)).symm e.inv
    let S := Presheaf.imageSieve (constantLocalHom F M N) a ⊓
      Presheaf.imageSieve (constantLocalHom F N M) b
    have hS : S ∈ J U := J.intersection_covering
      (sMN.imageSieve_mem a) (sNM.imageSieve_mem b)
    apply J.transitive hS
    intro V f hf
    obtain ⟨g, hg⟩ := hf.1
    obtain ⟨h, hh⟩ := hf.2
    have hgh : (constantLocalHom F M M).app (op V) (g ≫ h) =
        (constantLocalHom F M M).app (op V) (𝟙 M) := by
      rw [constantLocalHom_comp, constantLocalHom_id, hg, hh, ← localHomComp_map]
      have he : localHomComp _ _ _ a b = localHomId (F.obj M) (op U) := by
        apply (localHomEquiv _ _ (op U)).injective
        simp [localHomComp, localHomId, a, b]
      rw [he, localHomId_map]
    have hhg : (constantLocalHom F N N).app (op V) (h ≫ g) =
        (constantLocalHom F N N).app (op V) (𝟙 N) := by
      rw [constantLocalHom_comp, constantLocalHom_id, hg, hh, ← localHomComp_map]
      have he : localHomComp _ _ _ b a = localHomId (F.obj N) (op U) := by
        apply (localHomEquiv _ _ (op U)).injective
        simp [localHomComp, localHomId, a, b]
      rw [he, localHomId_map]
    have heq₁ := iMM.equalizerSieve_mem (X := op V) (g ≫ h) (𝟙 M) hgh
    have heq₂ := iNN.equalizerSieve_mem (X := op V) (h ≫ g) (𝟙 N) hhg
    apply J.superset_covering _ (J.intersection_covering heq₁ heq₂)
    intro W k hk
    let i : M ≅ N := ⟨g, h, hk.1, hk.2⟩
    refine ⟨i, ?_⟩
    apply Iso.ext
    apply (localHomEquiv _ _ (op W)).symm.injective
    change (constantLocalHom F M N).app (op W) g = _
    have hg' := congrArg ((localHom (F.obj M) (F.obj N)).map k.op) hg
    have hn := NatTrans.naturality_apply (constantLocalHom F M N) k.op g
    rw [← hn] at hg'
    have he := NatTrans.naturality_apply (localIsoHom (F.obj M) (F.obj N)) (k ≫ f).op e
    exact hg'.trans (by
      simpa [Functor.map_comp_apply, op_comp, a, localIsoHom] using he.symm)

/-- Local bijectivity of Hom comparisons passes to the comparison on isomorphisms.
Source: Stacks Project, Modules on Sites, Tag 093T, proof of (2).
(blueprint: lem-sf-constant-local-module-isom-bijective). -/
theorem constantLocalIso_locallyBijective
    [Presheaf.IsLocallyInjective J (constantLocalHom F M N)]
    [Presheaf.IsLocallySurjective J (constantLocalHom F M N)]
    [Presheaf.IsLocallySurjective J (constantLocalHom F N M)]
    [Presheaf.IsLocallyInjective J (constantLocalHom F M M)]
    [Presheaf.IsLocallyInjective J (constantLocalHom F N N)] :
    Presheaf.IsLocallyInjective J (constantLocalIso F M N) ∧
      Presheaf.IsLocallySurjective J (constantLocalIso F M N) :=
  ⟨constantLocalIso_locallyInjective F M N, constantLocalIso_locallySurjective F M N⟩

end SheafOfModules
