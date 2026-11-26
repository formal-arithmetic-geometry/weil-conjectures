/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.RingTheory.SmoothAlgebraFilteredColimitDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventual smoothness of pushouts of a finitely presented ring map

We show that if the base change of a finitely presented ring map `A → B` to the colimit of a
filtered diagram of `A`-algebras is smooth, then its base change to some stage of the diagram is
already smooth.

## References

* [Stacks, Tag 0C0B]
* [Stacks, Tag 0CAQ]
* [Stacks, Tag 01ZM]
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry

namespace CommRingCat

set_option backward.defeqAttrib.useBackward true in
/-- Let `A → B` be finitely presented and let `F` be a filtered diagram of `A`-algebras with
colimit `colim F`. If the pushout `B ⊗[A] colim F` is smooth over `colim F`, then already some
pushout stage `B ⊗[A] F j` is smooth over `F j`. -/
theorem exists_smooth_pushout_stage {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : f.hom.FinitePresentation)
    (t : (Functor.const I).obj A ⟶ F) (s : A ⟶ c.pt)
    (hs : ∀ j, t.app j ≫ c.ι.app j = s)
    (C : I → CommRingCat.{u}) (a : ∀ j, B ⟶ C j) (b : ∀ j, F.obj j ⟶ C j)
    (hC : ∀ j, IsPushout f (t.app j) (a j) (b j))
    {L : CommRingCat.{u}} (aL : B ⟶ L) (bL : c.pt ⟶ L)
    (hL : IsPushout f s aL bL) (hsm : bL.hom.Smooth) :
    ∃ j, (b j).hom.Smooth := by
  classical
  have : HasColimit F := ⟨⟨c, hc⟩⟩
  let e : colimit F ≅ c.pt := (colimit.isColimit F).coconePointUniqueUpToIso hc
  let g : colimit F ⟶ L := e.hom ≫ bL
  have hg : g.hom.Smooth := by
    exact (RingHom.Smooth.of_bijective (f := e.hom.hom)
      (ConcreteCategory.bijective_of_isIso e.hom)).comp hsm
  obtain ⟨i, Bi, hBi, fi, hfi, ⟨ε⟩⟩ :=
    Algebra.exists_smooth_algebra_of_filteredColimit F L g hg
  let : Algebra (F.obj i) Bi := fi.hom.toAlgebra
  let : Algebra (F.obj i) (colimit F : CommRingCat.{u}) := (colimit.ι F i).hom.toAlgebra
  let : Algebra (colimit F : CommRingCat.{u}) L := g.hom.toAlgebra
  let ai : CommRingCat.of Bi ⟶ L :=
    CommRingCat.ofHom (ε.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  have hpush : IsPushout fi (c.ι.app i) ai bL := by
    let eL := ε.symm.toRingEquiv.toCommRingCatIso
    refine (isPushout_tensorProduct (F.obj i) (colimit F : CommRingCat.{u}) Bi).flip.of_iso
      (Iso.refl _) (Iso.refl _) e eL ?_ ?_ ?_ ?_
    · rfl
    · change colimit.ι F i ≫ e.hom = c.ι.app i
      simp [e]
    · rfl
    · ext x
      exact ε.symm.commutes x
  have hBig : IsPushout f (t.app i ≫ c.ι.app i) aL bL := by
    simpa only [hs] using hL
  let aiOld : C i ⟶ L := (hC i).desc aL (c.ι.app i ≫ bL)
    (by rw [← Category.assoc, hs, hL.w])
  have hOld : IsPushout (b i) (c.ι.app i) aiOld bL := hBig.of_top' (hC i)
  let D := F.op ⋙ Scheme.Spec
  let d := Scheme.Spec.mapCone c.op
  have hd : IsLimit d :=
    isLimitOfPreserves Scheme.Spec hc.op
  have (j : Iᵒᵖ) : IsAffine (D.obj j) := inferInstanceAs (IsAffine (Spec _))
  have : ∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f) := fun f ↦ inferInstance
  have H₁ : IsPullback (Spec.map ai) (Spec.map bL) (Spec.map fi)
      (d.π.app (.op i)) := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  have H₂ : IsPullback (Spec.map aiOld) (Spec.map bL) (Spec.map (b i))
      (d.π.app (.op i)) := isPullback_SpecMap_of_isPushout _ _ _ _ hOld
  have : Smooth (Spec.map fi) := HasRingHomProperty.Spec_iff.mpr hfi
  have : LocallyOfFinitePresentation (Spec.map f) := HasRingHomProperty.Spec_iff.mpr hf
  have : LocallyOfFinitePresentation (Spec.map (b i)) :=
    MorphismProperty.of_isPullback
      (isPullback_SpecMap_of_isPushout _ _ _ _ (hC i)) inferInstance
  obtain ⟨k, r, htail⟩ := exists_iso_of_isPullback (D := D) (c := d) hd H₁ H₂
  obtain ⟨εk, hεk, -⟩ := htail
    (Y₁' := pullback (Spec.map fi) (D.map r))
    (Y₂' := pullback (Spec.map (b i)) (D.map r))
    (p₁' := pullback.snd (Spec.map fi) (D.map r))
    (p₂' := pullback.snd (Spec.map (b i)) (D.map r))
    (q₁ := pullback.fst (Spec.map fi) (D.map r))
    (q₂ := pullback.fst (Spec.map (b i)) (D.map r))
    (h₁' := isPullbackLift (D := D) (c := d) r H₁)
    (h₂' := isPullbackLift (D := D) (c := d) r H₂)
    (IsPullback.of_hasPullback (Spec.map fi) (D.map r))
    (isPullbackLift_fst (D := D) (c := d) r H₁) (isPullbackLift_snd (D := D) (c := d) r H₁)
    (IsPullback.of_hasPullback (Spec.map (b i)) (D.map r))
    (isPullbackLift_fst (D := D) (c := d) r H₂) (isPullbackLift_snd (D := D) (c := d) r H₂)
  have hnew : Smooth (pullback.snd (Spec.map fi) (D.map r)) := inferInstance
  have hold : Smooth (pullback.snd (Spec.map (b i)) (D.map r)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Smooth εk.hom, hεk]
    exact hnew
  have ht : t.app i ≫ F.map r.unop = t.app k.unop := by
    have h := t.naturality r.unop
    change 𝟙 A ≫ t.app k.unop = t.app i ≫ F.map r.unop at h
    simpa only [Category.id_comp] using h.symm
  have hBigk : IsPushout f (t.app i ≫ F.map r.unop) (a k.unop) (b k.unop) := by
    simpa only [ht] using hC k.unop
  let aik : C i ⟶ C k.unop := (hC i).desc (a k.unop) (F.map r.unop ≫ b k.unop)
    (by rw [← Category.assoc, ht, (hC k.unop).w])
  have hpushk : IsPushout (b i) (F.map r.unop) aik (b k.unop) :=
    hBigk.of_top' (hC i)
  have hsquare : IsPullback (Spec.map aik) (Spec.map (b k.unop))
      (Spec.map (b i)) (D.map r) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ hpushk
  have : Smooth (Spec.map (b k.unop)) := by
    rw [← hsquare.isoPullback_hom_snd]
    infer_instance
  exact ⟨k.unop, HasRingHomProperty.Spec_iff.mp this⟩

end CommRingCat
