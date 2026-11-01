/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import WeilConjectures.CategoryTheory.Exact.ExactFunctorHalfPlane
import all WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-!
# Exact functors transport exact couples

Source: Stacks Project, Homology, Section 12.21, Tags 011Q, 011R, 011S, 0AMJ,
and the transport argument of the blueprint (blueprint: lem-sp-exact-functor-couple).
The index `r` denotes the actual page `r + 2`. Object equalities identify the initial
mapped datum; subsequent identifications of subobjects are commuting isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  {s : ℕ}

private theorem map_exact {U V W : C} (f : U ⟶ V) (g : V ⟶ W)
    (hz : f ≫ g = 0) (he : imageSubobject f = kernelSubobject g) :
    imageSubobject (Φ.map f) = kernelSubobject (Φ.map g) := by
  exact (ShortComplex.exact_iff_image_eq_kernel _).mp
    (((ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk f g hz)).mpr he).map Φ)

private def mapped (X : BigradedExactCouple C s) : BigradedExactCouple B s where
  D p q := Φ.obj (X.D p q)
  E p q := Φ.obj (X.E p q)
  alpha p q := Φ.map (X.alpha p q)
  f p q := Φ.map (X.f p q)
  g p q := Φ.map (X.g p q)
  alpha_f_zero p q := by rw [← Φ.map_comp, X.alpha_f_zero, Φ.map_zero]
  f_g_zero p q := by rw [← Φ.map_comp, X.f_g_zero, Φ.map_zero]
  g_alpha_zero p q := by rw [← Φ.map_comp, X.g_alpha_zero, Φ.map_zero]
  exact_alpha p q := map_exact Φ _ _ (X.alpha_f_zero p q) (X.exact_alpha p q)
  exact_f p q := map_exact Φ _ _ (X.f_g_zero p q) (X.exact_f p q)
  exact_g p q := map_exact Φ _ _ (X.g_alpha_zero p q) (X.exact_g p q)

private noncomputable def imageIso {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) : Φ.obj (image f) ≅ image g :=
  (PreservesImage.iso Φ f).symm ≪≫ (im (C := B)).mapIso
    (Arrow.isoMk (f := Arrow.mk (Φ.map f)) (g := Arrow.mk g) eU eV h.symm)

omit [Φ.Additive] in
private theorem imageIso_ι {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) :
    (imageIso Φ f g eU eV h).hom ≫ image.ι g = Φ.map (image.ι f) ≫ eV.hom := by
  have hm : image.map (Arrow.isoMk (f := Arrow.mk (Φ.map f))
      (g := Arrow.mk g) eU eV h.symm).hom ≫ image.ι g =
      image.ι (Φ.map f) ≫ eV.hom := image.map_ι _
  dsimp only [imageIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, im]
  rw [Category.assoc, hm, ← Category.assoc, PreservesImage.inv_comp_image_ι_map]

private noncomputable def cyclesIso {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) : Φ.obj (kernel f) ≅ kernel g :=
  PreservesKernel.iso Φ f ≪≫ kernel.mapIso (Φ.map f) g eU eV h

private noncomputable def quotientIso {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) : Φ.obj (cokernel f) ≅ cokernel g :=
  PreservesCokernel.iso Φ f ≪≫ cokernel.mapIso (Φ.map f) g eU eV h

private structure Comparison (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) where
  δ : ∀ p q, Φ.obj (X.D p q) ≅ Y.D p q
  φ : ∀ p q, Φ.obj (X.E p q) ≅ Y.E p q
  ha : ∀ p q, Φ.map (X.alpha p q) ≫ (δ (p - 1) (q + 1)).hom =
    (δ p q).hom ≫ Y.alpha p q
  hf : ∀ p q, Φ.map (X.f p q) ≫ (δ (p + 2) (q - 1)).hom =
    (φ p q).hom ≫ Y.f p q
  hg : ∀ p q, Φ.map (X.g p q) ≫ (φ (p + s) (q - s)).hom =
    (δ p q).hom ≫ Y.g p q

variable {Φ}

omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
private theorem Comparison.hd {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.d p q) ≫ (e.φ (p + 2 + s) (q - 1 - s)).hom =
      (e.φ p q).hom ≫ Y.d p q := by
  dsimp only [d]
  rw [Φ.map_comp, Category.assoc, e.hg, ← Category.assoc, e.hf, Category.assoc]

private noncomputable def Comparison.di {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.obj (X.derivedD p q) ≅ Y.derivedD p q :=
  imageIso Φ _ _ (e.δ (p + 1) (q - 1)) (e.δ (p + 1 - 1) (q - 1 + 1))
    (e.ha (p + 1) (q - 1))

private noncomputable def Comparison.ki {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.obj (kernel (X.d p q)) ≅ kernel (Y.d p q) :=
  cyclesIso Φ _ _ (e.φ p q) (e.φ (p + 2 + s) (q - 1 - s)) (e.hd p q)

private noncomputable def Comparison.ei {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.obj (X.derivedE p q) ≅ Y.derivedE p q :=
  quotientIso Φ _ _ (e.φ (p - s - 2) (q + s + 1)) (e.ki p q) (e.lift_comm p q)

private noncomputable def Comparison.next {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) :
    Comparison Φ X.derived Y.derived where
  δ := e.di
  φ := e.ei
  ha := e.derived_ha
  hf := e.derived_hf
  hg := e.derived_hg

private noncomputable def filtrationIso (X : BigradedExactCouple C 0)
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (hA : ∀ n p, Φ.map ((AX n).ι p) ≫ (eA n).hom = (AY n).ι p)
    (n p : ℤ) :
    Φ.obj ((X.imageFiltration n (AX n)).step p : C) ≅
      (((mapped Φ X).imageFiltration n (AY n)).step p : B) :=
  Φ.mapIso (imageSubobjectIso ((AX n).ι p)) ≪≫
    imageIso Φ ((AX n).ι p) ((AY n).ι p) (Iso.refl _) (eA n)
      (by simpa using hA n p) ≪≫ (imageSubobjectIso ((AY n).ι p)).symm

private theorem filtrationIso_arrow (X : BigradedExactCouple C 0)
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (hA : ∀ n p, Φ.map ((AX n).ι p) ≫ (eA n).hom = (AY n).ι p)
    (n p : ℤ) :
    (filtrationIso X AX AY eA hA n p).hom ≫
        (((mapped Φ X).imageFiltration n (AY n)).step p).arrow =
      Φ.map (((X.imageFiltration n (AX n)).step p).arrow) ≫ (eA n).hom := by
  dsimp only [filtrationIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    imageFiltration]
  rw [Category.assoc, Category.assoc, imageSubobject_arrow',
    imageIso_ι, ← Category.assoc, ← Φ.map_comp, imageSubobject_arrow]

private theorem filtrationIso_step (X : BigradedExactCouple C 0)
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (hA : ∀ n p, Φ.map ((AX n).ι p) ≫ (eA n).hom = (AY n).ι p)
    (n p : ℤ) :
    Φ.map (Subobject.ofLE ((X.imageFiltration n (AX n)).step (p + 1))
      ((X.imageFiltration n (AX n)).step p)
      ((X.imageFiltration n (AX n)).antitone_step (by omega))) ≫
        (filtrationIso X AX AY eA hA n p).hom =
      (filtrationIso X AX AY eA hA n (p + 1)).hom ≫
        Subobject.ofLE (((mapped Φ X).imageFiltration n (AY n)).step (p + 1))
          (((mapped Φ X).imageFiltration n (AY n)).step p)
          (((mapped Φ X).imageFiltration n (AY n)).antitone_step (by omega)) := by
  apply (cancel_mono (((mapped Φ X).imageFiltration n (AY n)).step p).arrow).mp
  rw [Category.assoc, filtrationIso_arrow, ← Category.assoc, ← Φ.map_comp,
    Subobject.ofLE_arrow, Category.assoc, Subobject.ofLE_arrow, filtrationIso_arrow]

private noncomputable def gradedIso (X : BigradedExactCouple C 0)
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (hA : ∀ n p, Φ.map ((AX n).ι p) ≫ (eA n).hom = (AY n).ι p)
    (n p : ℤ) :
    Φ.obj ((X.imageFiltration n (AX n)).gradedPiece p) ≅
      ((mapped Φ X).imageFiltration n (AY n)).gradedPiece p :=
  quotientIso Φ _ _ (filtrationIso X AX AY eA hA n (p + 1))
    (filtrationIso X AX AY eA hA n p) (filtrationIso_step X AX AY eA hA n p)

/-! Transport of exact couples along an exact additive functor.
Source: Stacks Project, Homology, Section 12.21; blueprint: lem-sp-exact-functor-couple.
The full transport construction is retained as the next proof obligation. -/
end CategoryTheory.BigradedExactCouple
