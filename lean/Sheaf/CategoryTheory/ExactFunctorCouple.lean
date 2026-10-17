/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.CategoryTheory.HalfPlaneConvergence
import Sheaf.CategoryTheory.ExactFunctorHalfPlane
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

omit [PreservesFiniteColimits Φ] in
private theorem cyclesIso_ι {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) :
    (cyclesIso Φ f g eU eV h).hom ≫ kernel.ι g =
      Φ.map (kernel.ι f) ≫ eU.hom := by
  simp [cyclesIso, Category.assoc]

private noncomputable def quotientIso {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) : Φ.obj (cokernel f) ≅ cokernel g :=
  PreservesCokernel.iso Φ f ≪≫ cokernel.mapIso (Φ.map f) g eU eV h

omit [PreservesFiniteLimits Φ] in
private theorem quotientIso_π {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) :
    Φ.map (cokernel.π f) ≫ (quotientIso Φ f g eU eV h).hom =
      eV.hom ≫ cokernel.π g := by
  simp [quotientIso, ← Category.assoc]

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

private theorem derived_alpha (X : BigradedExactCouple C s) (p q : ℤ) :
    X.derived.alpha p q ≫ X.derivedDInclusion (p - 1) (q + 1) =
      X.derivedDInclusion p q ≫ X.alpha p q :=
  (Classical.choice X.derivedMaps_exists).alpha_comm p q

private theorem derived_f (X : BigradedExactCouple C s) (p q : ℤ) :
    X.derivedEProjection p q ≫ X.derived.f p q ≫
      X.derivedDInclusion (p + 2) (q - 1) = kernel.ι (X.d p q) ≫ X.f p q :=
  (Classical.choice X.derivedMaps_exists).f_comm p q

private theorem derived_g (X : BigradedExactCouple C s) (p q : ℤ) :
    factorThruImage (X.alpha (p + 1) (q - 1)) ≫ X.derived.g p q =
      X.gToCycles (p + 1) (q - 1) ≫
        X.derivedEProjection ((p + 1) + s) ((q - 1) - s) ≫
          eqToHom (by congr 1 <;> omega) :=
  (Classical.choice X.derivedMaps_exists).g_comm p q

private noncomputable def Comparison.di {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.obj (X.derivedD p q) ≅ Y.derivedD p q :=
  imageIso Φ _ _ (e.δ (p + 1) (q - 1)) (e.δ (p + 1 - 1) (q - 1 + 1))
    (e.ha (p + 1) (q - 1))

omit [Φ.Additive] in
private theorem Comparison.di_ι {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    (e.di p q).hom ≫ Y.derivedDInclusion p q =
      Φ.map (X.derivedDInclusion p q) ≫ (e.δ p q).hom := by
  dsimp only [derivedDInclusion]
  rw [← Category.assoc]
  dsimp only [Comparison.di]
  rw [imageIso_ι, Φ.map_comp, Category.assoc, Category.assoc,
    transport_square Φ (fun p q ↦ (e.δ p q).hom) (by omega) (by omega)]

private noncomputable def Comparison.ki {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.obj (kernel (X.d p q)) ≅ kernel (Y.d p q) :=
  cyclesIso Φ _ _ (e.φ p q) (e.φ (p + 2 + s) (q - 1 - s)) (e.hd p q)

omit [PreservesFiniteColimits Φ] in
private theorem Comparison.ki_ι {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    (e.ki p q).hom ≫ kernel.ι (Y.d p q) =
      Φ.map (kernel.ι (X.d p q)) ≫ (e.φ p q).hom :=
  cyclesIso_ι Φ _ _ _ _ _

omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
private theorem Comparison.hInto {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.dInto p q) ≫ (e.φ p q).hom =
      (e.φ (p - s - 2) (q + s + 1)).hom ≫ Y.dInto p q := by
  dsimp only [dInto]
  rw [Φ.map_comp, Category.assoc,
    transport_square Φ (fun p q ↦ (e.φ p q).hom) (by omega) (by omega),
    ← Category.assoc, e.hd, Category.assoc]

omit [PreservesFiniteColimits Φ] in
private theorem Comparison.lift_comm {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (kernel.lift (X.d p q) (X.dInto p q) (X.dInto_comp_d p q)) ≫
      (e.ki p q).hom = (e.φ (p - s - 2) (q + s + 1)).hom ≫
        kernel.lift (Y.d p q) (Y.dInto p q) (Y.dInto_comp_d p q) := by
  apply (cancel_mono (kernel.ι (Y.d p q))).mp
  rw [Category.assoc, e.ki_ι, ← Category.assoc, ← Φ.map_comp, kernel.lift_ι,
    Category.assoc, kernel.lift_ι, e.hInto]

private noncomputable def Comparison.ei {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.obj (X.derivedE p q) ≅ Y.derivedE p q :=
  quotientIso Φ _ _ (e.φ (p - s - 2) (q + s + 1)) (e.ki p q) (e.lift_comm p q)

private theorem Comparison.ei_π {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derivedEProjection p q) ≫ (e.ei p q).hom =
      (e.ki p q).hom ≫ Y.derivedEProjection p q :=
  quotientIso_π Φ _ _ _ _ _

omit [Φ.Additive] in
private theorem Comparison.derived_ha {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derived.alpha p q) ≫ (e.di (p - 1) (q + 1)).hom =
      (e.di p q).hom ≫ Y.derived.alpha p q := by
  apply (cancel_mono (Y.derivedDInclusion (p - 1) (q + 1))).mp
  rw [Category.assoc, e.di_ι, ← Category.assoc, ← Φ.map_comp, derived_alpha,
    Φ.map_comp, Category.assoc, e.ha, ← Category.assoc, ← e.di_ι,
    Category.assoc]
  rw [Category.assoc, derived_alpha]

private theorem Comparison.derived_hf {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derived.f p q) ≫ (e.di (p + 2) (q - 1)).hom =
      (e.ei p q).hom ≫ Y.derived.f p q := by
  apply (cancel_epi (Φ.map (X.derivedEProjection p q))).mp
  apply (cancel_mono (Y.derivedDInclusion (p + 2) (q - 1))).mp
  calc
    (Φ.map (X.derivedEProjection p q) ≫
        (Φ.map (X.derived.f p q) ≫ (e.di (p + 2) (q - 1)).hom)) ≫
        Y.derivedDInclusion (p + 2) (q - 1) =
        Φ.map (kernel.ι (X.d p q)) ≫ (e.φ p q).hom ≫ Y.f p q := by
      rw [Category.assoc, Category.assoc, e.di_ι, ← Φ.map_comp_assoc,
        ← Φ.map_comp_assoc, Category.assoc (X.derivedEProjection p q),
        derived_f, Φ.map_comp, Category.assoc, e.hf]
    _ = (Φ.map (X.derivedEProjection p q) ≫
        ((e.ei p q).hom ≫ Y.derived.f p q)) ≫
          Y.derivedDInclusion (p + 2) (q - 1) := by
      rw [← Category.assoc (Φ.map (kernel.ι (X.d p q))), ← e.ki_ι,
        Category.assoc, ← derived_f, ← Category.assoc, ← e.ei_π]
      simp only [Category.assoc]

omit [Φ.Additive] in
private theorem Comparison.di_factor {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (factorThruImage (X.alpha (p + 1) (q - 1))) ≫ (e.di p q).hom =
      (e.δ (p + 1) (q - 1)).hom ≫ factorThruImage (Y.alpha (p + 1) (q - 1)) := by
  apply (cancel_mono (image.ι (Y.alpha (p + 1) (q - 1)))).mp
  dsimp only [Comparison.di]
  rw [Category.assoc, imageIso_ι, ← Category.assoc, ← Φ.map_comp, image.fac,
    Category.assoc, image.fac, e.ha]

omit [PreservesFiniteColimits Φ] in
private theorem Comparison.gCycles {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.gToCycles p q) ≫ (e.ki (p + s) (q - s)).hom =
      (e.δ p q).hom ≫ Y.gToCycles p q := by
  apply (cancel_mono (kernel.ι (Y.d (p + s) (q - s)))).mp
  rw [Category.assoc, e.ki_ι, ← Category.assoc, ← Φ.map_comp]
  simp only [gToCycles, kernel.lift_ι, Category.assoc]
  exact e.hg p q

private theorem Comparison.derived_hg {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derived.g p q) ≫ (e.ei (p + (s + 1 : ℕ)) (q - (s + 1 : ℕ))).hom =
      (e.di p q).hom ≫ Y.derived.g p q := by
  apply (cancel_epi (Φ.map (factorThruImage (X.alpha (p + 1) (q - 1))))).mp
  rw [← Φ.map_comp_assoc, derived_g, Φ.map_comp, Φ.map_comp]
  rw [Category.assoc, Category.assoc,
    transport_square Φ (fun p q ↦ (e.ei p q).hom) (by omega) (by omega),
    ← Category.assoc (Φ.map (X.derivedEProjection _ _)), e.ei_π,
    Category.assoc]
  rw [← Category.assoc (Φ.map (X.gToCycles (p + 1) (q - 1)))
    (e.ki (p + 1 + s) (q - 1 - s)).hom, e.gCycles]
  rw [← Category.assoc (Φ.map (factorThruImage (X.alpha (p + 1) (q - 1))))
    (e.di p q).hom, e.di_factor]
  simp only [Category.assoc, derived_g]

private noncomputable def Comparison.next {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) :
    Comparison Φ X.derived Y.derived where
  δ := e.di
  φ := e.ei
  ha := e.derived_ha
  hf := e.derived_hf
  hg := e.derived_hg

private noncomputable def comparisonPages (X : BigradedExactCouple C 0) :
    (r : ℕ) → Comparison Φ (X.pageCouple r) ((mapped Φ X).pageCouple r)
  | 0 => { δ := fun _ _ ↦ Iso.refl _
           φ := fun _ _ ↦ Iso.refl _
           ha := by intros; simp [mapped, pageCouple]
           hf := by intros; simp [mapped, pageCouple]
           hg := by intros; simp [mapped, pageCouple] }
  | r + 1 => (comparisonPages X r).next

private noncomputable def pageInclusion {A : Type*} [Category A] [Abelian A]
    (X : BigradedExactCouple A 0) : ∀ r : ℕ, ∀ p q : ℤ,
    (X.pageCouple r).D p q ⟶ X.D p q
  | 0, _, _ => 𝟙 _
  | r + 1, p, q => (X.pageCouple r).derivedDInclusion p q ≫ pageInclusion X r p q

private theorem pageInclusion_mono {A : Type*} [Category A] [Abelian A]
    (X : BigradedExactCouple A 0) (r : ℕ) (p q : ℤ) : Mono (pageInclusion X r p q) := by
  induction r with
  | zero => dsimp only [pageInclusion]; infer_instance
  | succ r ih => dsimp only [pageInclusion]; infer_instance

private theorem comparisonPages_inclusion (X : BigradedExactCouple C 0)
    (r : ℕ) (p q : ℤ) :
    ((comparisonPages X r).δ p q).hom ≫ pageInclusion (mapped Φ X) r p q =
      Φ.map (pageInclusion X r p q) := by
  induction r with
  | zero => simp [comparisonPages, pageInclusion]
  | succ r ih =>
    change ((comparisonPages X r).di p q).hom ≫
      ((mapped Φ X).pageCouple r).derivedDInclusion p q ≫ _ = _
    rw [← Category.assoc, Comparison.di_ι, Category.assoc, ih, ← Φ.map_comp]
    rfl

private theorem mapped_diagonal (X : BigradedExactCouple C 0) (n p : ℤ) :
    Φ.map (X.alphaDiagonal n p) = (mapped Φ X).alphaDiagonal n p := by
  simp only [alphaDiagonal, mapped, Φ.map_comp]
  congr 1
  exact eqToHom_map Φ _

private theorem cocone_natural (X : BigradedExactCouple C 0)
    (hE : ∀ p q : ℤ, p < 0 → IsZero (X.E p q))
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (h0 : ∀ n, Φ.map ((AX n).ι 0) ≫ (eA n).hom = (AY n).ι 0)
    (n p : ℤ) : Φ.map ((AX n).ι p) ≫ (eA n).hom = (AY n).ι p := by
  induction p using Int.inductionOn' with
  | b => exact 0
  | zero => exact h0 n
  | succ p hp ih =>
    rw [← (AX n).comm, Φ.map_comp, Category.assoc, ih,
      mapped_diagonal, (AY n).comm]
  | pred p hp ih =>
    have := alpha_iso_left X hE (p - 1 + 1) (n - (p - 1 + 1)) (by omega)
    have : IsIso (X.alphaDiagonal n (p - 1)) := by
      dsimp only [alphaDiagonal]
      infer_instance
    apply (cancel_epi (Φ.map (X.alphaDiagonal n (p - 1)))).mp
    rw [← Φ.map_comp_assoc, (AX n).comm, mapped_diagonal, (AY n).comm]
    exact Eq.mp (congrArg (fun j : ℤ ↦ Φ.map ((AX n).ι j) ≫ (eA n).hom =
      (AY n).ι j) (show p = p - 1 + 1 by omega)) ih

private noncomputable def normalizedColimitIso (X : BigradedExactCouple C 0)
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (hAX : ∀ n, (AX n).obj = X.D 0 n)
    (hAY : ∀ n, (AY n).obj = (mapped Φ X).D 0 n) (n : ℤ) :
    Φ.obj (AX n).obj ≅ (AY n).obj :=
  Φ.mapIso (eqToIso (hAX n)) ≪≫ (eqToIso (hAY n)).symm

private theorem normalizedColimitIso_zero (X : BigradedExactCouple C 0)
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (hAX : ∀ n, (AX n).obj = X.D 0 n)
    (hAY : ∀ n, (AY n).obj = (mapped Φ X).D 0 n)
    (hAX0 : ∀ n, (AX n).ι 0 ≫ eqToHom (hAX n) = eqToHom (by congr 1; omega))
    (hAY0 : ∀ n, (AY n).ι 0 ≫ eqToHom (hAY n) = eqToHom (by congr 1; omega))
    (n : ℤ) :
    Φ.map ((AX n).ι 0) ≫ (normalizedColimitIso X AX AY hAX hAY n).hom =
      (AY n).ι 0 := by
  apply (cancel_mono (eqToHom (hAY n))).mp
  dsimp only [normalizedColimitIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    eqToIso.hom, eqToIso.inv]
  rw [Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    ← Φ.map_comp, hAX0, hAY0]
  exact eqToHom_map Φ _

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
/-- An exact additive functor transports an exact couple, its derived pages, and its
half-plane abutment filtration.

Proof plan: construct the mapped exact couple using preservation of images, kernels,
and cokernels; compare one derived step by cancellation of the canonical mono and epi;
iterate the comparison over pages and compose the derived-D inclusions; transport the
half-plane convergence and filtration comparisons using exactness and the canonical
finite-page stabilization maps.
Source: Stacks Project, Homology, Section 12.21 (Tags 011Q, 011R, 011S, 0AMJ);
(blueprint: lem-sp-exact-functor-couple)
Proof, step 1: preservation of images, kernels, cokernels, and exactness constructs
the mapped couple.
Proof, step 2: cancellation of image inclusions and quotient projections compares each derived page.
Proof, step 3: induction transports the half-plane convergence and filtration maps. -/
theorem exactFunctor_couple
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (X : BigradedExactCouple C 0) :
    ∃ Y : BigradedExactCouple B 0,
    ∃ hD : ∀ p q : ℤ, Φ.obj (X.D p q) = Y.D p q,
    ∃ hE : ∀ p q : ℤ, Φ.obj (X.E p q) = Y.E p q,
    (∀ p q : ℤ, Φ.map (X.alpha p q) ≫ eqToHom (hD (p - 1) (q + 1)) =
      eqToHom (hD p q) ≫ Y.alpha p q) ∧
    (∀ p q : ℤ, Φ.map (X.f p q) ≫ eqToHom (hD (p + 2) (q - 1)) =
      eqToHom (hE p q) ≫ Y.f p q) ∧
    (∀ p q : ℤ, Φ.map (X.g p q) ≫ eqToHom (hE (p + 0) (q - 0)) =
      eqToHom (hD p q) ≫ Y.g p q) ∧
    ∃ δ : ∀ (r : ℕ) (p q : ℤ),
      Φ.obj ((X.pageCouple r).D p q) ≅ (Y.pageCouple r).D p q,
    ∃ φ : ∀ (r : ℕ) (p q : ℤ),
      Φ.obj ((X.pageCouple r).E p q) ≅ (Y.pageCouple r).E p q,
    ∃ iX : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q,
    ∃ iY : ∀ (r : ℕ) (p q : ℤ), (Y.pageCouple r).D p q ⟶ Y.D p q,
    (∀ p q : ℤ, δ 0 p q = eqToIso (hD p q) ∧ φ 0 p q = eqToIso (hE p q)) ∧
    (∀ p q : ℤ, iX 0 p q = 𝟙 _ ∧ iY 0 p q = 𝟙 _) ∧
    (∀ (r : ℕ) (p q : ℤ),
      iX (r + 1) p q = (X.pageCouple r).derivedDInclusion p q ≫ iX r p q ∧
      iY (r + 1) p q = (Y.pageCouple r).derivedDInclusion p q ≫ iY r p q) ∧
    (∀ (r : ℕ) (p q : ℤ), Mono (iX r p q) ∧ Mono (iY r p q) ∧
      (δ r p q).hom ≫ iY r p q = Φ.map (iX r p q) ≫ eqToHom (hD p q)) ∧
    (∀ (r : ℕ) (p q : ℤ),
      Φ.map ((X.pageCouple r).alpha p q) ≫ (δ r (p - 1) (q + 1)).hom =
        (δ r p q).hom ≫ (Y.pageCouple r).alpha p q) ∧
    (∀ (r : ℕ) (p q : ℤ),
      Φ.map ((X.pageCouple r).f p q) ≫ (δ r (p + 2) (q - 1)).hom =
        (φ r p q).hom ≫ (Y.pageCouple r).f p q) ∧
    (∀ (r : ℕ) (p q : ℤ),
      Φ.map ((X.pageCouple r).g p q) ≫ (φ r (p + r) (q - r)).hom =
        (δ r p q).hom ≫ (Y.pageCouple r).g p q) ∧
    (∀ (r : ℕ) (p q : ℤ),
      Φ.map ((X.pageCouple r).d p q) ≫ (φ r (p + 2 + r) (q - 1 - r)).hom =
        (φ r p q).hom ≫ (Y.pageCouple r).d p q) ∧
    (∀ (r : ℕ) (p q : ℤ),
      ∃ k : Φ.obj (kernel ((X.pageCouple r).d p q)) ⟶
        kernel ((Y.pageCouple r).d p q),
      IsIso k ∧
      k ≫ kernel.ι ((Y.pageCouple r).d p q) =
        Φ.map (kernel.ι ((X.pageCouple r).d p q)) ≫ (φ r p q).hom ∧
      Φ.map ((X.pageCouple r).derivedEProjection p q) ≫ (φ (r + 1) p q).hom =
        k ≫ (Y.pageCouple r).derivedEProjection p q) ∧
    (∀ (a : ℤ)
      (_ : ∀ p q : ℤ, q < a → IsZero (X.D p q))
      (_ : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q)),
      (∀ p q : ℤ, q < a → IsZero (Y.D p q)) ∧
      (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (Y.E p q)) ∧
      ∃ LX : LimitSubobjects X, ∃ LY : LimitSubobjects Y,
      ∃ AX : ∀ n : ℤ, AlphaColimit X n, ∃ AY : ∀ n : ℤ, AlphaColimit Y n,
      ∃ hAX : ∀ n : ℤ, (AX n).obj = X.D 0 n,
      ∃ hAY : ∀ n : ℤ, (AY n).obj = Y.D 0 n,
      ∃ eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj,
      (∀ n : ℤ, (AX n).ι 0 ≫ eqToHom (hAX n) =
        eqToHom (by congr 1; omega)) ∧
      (∀ n : ℤ, (AY n).ι 0 ≫ eqToHom (hAY n) =
        eqToHom (by congr 1; omega)) ∧
      (∀ n p : ℤ, Φ.map ((AX n).ι p) ≫ (eA n).hom =
        eqToHom (hD p (n - p)) ≫ (AY n).ι p) ∧
      (∀ n p : ℤ, p ≤ 0 →
        (X.imageFiltration n (AX n)).step p = ⊤ ∧
        (Y.imageFiltration n (AY n)).step p = ⊤) ∧
      (∀ n : ℤ, (X.imageFiltration n (AX n)).IsFinite ∧
        (Y.imageFiltration n (AY n)).IsFinite) ∧
      X.ConvergesTo LX AX ∧ Y.ConvergesTo LY AY ∧
      ∃ τ : ∀ n p : ℤ,
        Φ.obj ((X.imageFiltration n (AX n)).step p : C) ≅
          ((Y.imageFiltration n (AY n)).step p : B),
      ∃ κ : ∀ n p : ℤ,
        Φ.obj ((X.imageFiltration n (AX n)).gradedPiece p) ≅
          (Y.imageFiltration n (AY n)).gradedPiece p,
      (∀ n p : ℤ,
        (τ n p).hom ≫ ((Y.imageFiltration n (AY n)).step p).arrow =
          Φ.map (((X.imageFiltration n (AX n)).step p).arrow) ≫ (eA n).hom) ∧
      (∀ n p : ℤ,
        Φ.map (cokernel.π (Subobject.ofLE
          ((X.imageFiltration n (AX n)).step (p + 1))
          ((X.imageFiltration n (AX n)).step p)
          ((X.imageFiltration n (AX n)).antitone_step (by omega)))) ≫ (κ n p).hom =
        (τ n p).hom ≫ cokernel.π (Subobject.ofLE
          ((Y.imageFiltration n (AY n)).step (p + 1))
          ((Y.imageFiltration n (AY n)).step p)
          ((Y.imageFiltration n (AY n)).antitone_step (by omega)))) ∧
      (∀ (r : ℕ) (p q : ℤ), (r : ℤ) + 2 > max (q - a + 1) p →
        ∃ sX : (X.pageCouple r).E p q ≅ (X.pageCouple (r + 1)).E p q,
        ∃ sY : (Y.pageCouple r).E p q ≅ (Y.pageCouple (r + 1)).E p q,
        kernel.ι ((X.pageCouple r).d p q) ≫ sX.hom =
          (X.pageCouple r).derivedEProjection p q ∧
        kernel.ι ((Y.pageCouple r).d p q) ≫ sY.hom =
          (Y.pageCouple r).derivedEProjection p q ∧
        Φ.map sX.hom ≫ (φ (r + 1) p q).hom = (φ r p q).hom ≫ sY.hom) ∧
      (∃ φInfinity : ∀ p q : ℤ, Φ.obj (X.pageInfinity LX p q) ≅ Y.pageInfinity LY p q,
        (∀ p q : ℤ, Φ.map (X.toPageInfinity LX p q) ≫ (φInfinity p q).hom =
          eqToHom (hD p q) ≫ Y.toPageInfinity LY p q) ∧
        (∀ (r : ℕ) (p q : ℤ), (r : ℤ) + 2 > max (q - a + 1) p →
          ∃ hZX : X.cycleBoundaryTower.Z r p q = LX.Z p q,
          ∃ hZY : Y.cycleBoundaryTower.Z r p q = LY.Z p q,
          ∃ eX : (X.pageCouple r).E p q ≅ X.pageInfinity LX p q,
          ∃ eY : (Y.pageCouple r).E p q ≅ Y.pageInfinity LY p q,
          X.cycleBoundaryTower.projection r p q ≫ eX.hom =
            eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : C)) hZX) ≫
              cokernel.π (Subobject.ofLE (LX.B p q) (LX.Z p q)
                (limitBoundary_le_cycle X LX p q)) ∧
          Y.cycleBoundaryTower.projection r p q ≫ eY.hom =
            eqToHom (congrArg (fun S : Subobject (Y.E p q) ↦ (S : B)) hZY) ≫
              cokernel.π (Subobject.ofLE (LY.B p q) (LY.Z p q)
                (limitBoundary_le_cycle Y LY p q)) ∧
          Φ.map eX.hom ≫ (φInfinity p q).hom = (φ r p q).hom ≫ eY.hom) ∧
        ∀ p q : ℤ,
          ∃ ξX : X.pageInfinity LX p q ≅
            (X.imageFiltration (p + q) (AX (p + q))).gradedPiece p,
          ∃ ξY : Y.pageInfinity LY p q ≅
            (Y.imageFiltration (p + q) (AY (p + q))).gradedPiece p,
          X.toPageInfinity LX p q ≫ ξX.hom = X.toGradedPiece AX p q ∧
          Y.toPageInfinity LY p q ≫ ξY.hom = Y.toGradedPiece AY p q ∧
          Φ.map ξX.hom ≫ (κ (p + q) p).hom = (φInfinity p q).hom ≫ ξY.hom) ∧
      (∀ (r : ℕ) (p q : ℤ),
        (r : ℤ) + 2 ≥ max (p + 3) (q - a + 2) →
        ∃ lambdaX : (AX (p + q)).obj ≅ X.D (p - r) (q + r),
        ∃ lambdaY : (AY (p + q)).obj ≅ Y.D (p - r) (q + r),
        ∃ tX : ((X.imageFiltration (p + q) (AX (p + q))).step p : C) ≅
          (X.pageCouple r).D (p - r) (q + r),
        ∃ tY : ((Y.imageFiltration (p + q) (AY (p + q))).step p : B) ≅
          (Y.pageCouple r).D (p - r) (q + r),
        ∃ ψX : (X.imageFiltration (p + q) (AX (p + q))).gradedPiece p ≅
          (X.pageCouple r).E p q,
        ∃ ψY : (Y.imageFiltration (p + q) (AY (p + q))).gradedPiece p ≅
          (Y.pageCouple r).E p q,
        lambdaX.inv = eqToHom (by congr 1; omega) ≫ (AX (p + q)).ι (p - r) ∧
        lambdaY.inv = eqToHom (by congr 1; omega) ≫ (AY (p + q)).ι (p - r) ∧
        tX.hom ≫ iX r (p - r) (q + r) =
          ((X.imageFiltration (p + q) (AX (p + q))).step p).arrow ≫ lambdaX.hom ∧
        tY.hom ≫ iY r (p - r) (q + r) =
          ((Y.imageFiltration (p + q) (AY (p + q))).step p).arrow ≫ lambdaY.hom ∧
        cokernel.π (Subobject.ofLE
          ((X.imageFiltration (p + q) (AX (p + q))).step (p + 1))
          ((X.imageFiltration (p + q) (AX (p + q))).step p)
          ((X.imageFiltration (p + q) (AX (p + q))).antitone_step (by omega))) ≫
          ψX.hom = tX.hom ≫ (X.pageCouple r).g (p - r) (q + r) ≫
            eqToHom (by congr 1 <;> omega) ∧
        cokernel.π (Subobject.ofLE
          ((Y.imageFiltration (p + q) (AY (p + q))).step (p + 1))
          ((Y.imageFiltration (p + q) (AY (p + q))).step p)
          ((Y.imageFiltration (p + q) (AY (p + q))).antitone_step (by omega))) ≫
          ψY.hom = tY.hom ≫ (Y.pageCouple r).g (p - r) (q + r) ≫
            eqToHom (by congr 1 <;> omega) ∧
        Φ.map ψX.hom ≫ (φ r p q).hom = (κ (p + q) p).hom ≫ ψY.hom)) := by
  classical
  refine ⟨mapped Φ X, fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_, ?_, ?_, ?_⟩
  · intro p q; simp [mapped]
  · intro p q; simp [mapped]
  · intro p q; simp [mapped]
  let δ := fun r p q ↦ ((comparisonPages (Φ := Φ) X r).δ p q)
  let φ := fun r p q ↦ ((comparisonPages (Φ := Φ) X r).φ p q)
  let iX := pageInclusion X
  let iY := pageInclusion (mapped Φ X)
  have H0 : ∀ p q : ℤ, δ 0 p q = Iso.refl _ ∧ φ 0 p q = Iso.refl _ := by
    intro p q; exact ⟨rfl, rfl⟩
  have H1 : ∀ p q : ℤ, iX 0 p q = 𝟙 _ ∧ iY 0 p q = 𝟙 _ := by
    intro p q; exact ⟨rfl, rfl⟩
  have H2 : ∀ (r : ℕ) (p q : ℤ),
      iX (r + 1) p q = (X.pageCouple r).derivedDInclusion p q ≫ iX r p q ∧
      iY (r + 1) p q = ((mapped Φ X).pageCouple r).derivedDInclusion p q ≫ iY r p q := by
    intro r p q; exact ⟨rfl, rfl⟩
  have H3 : ∀ (r : ℕ) (p q : ℤ), Mono (iX r p q) ∧ Mono (iY r p q) ∧
      (δ r p q).hom ≫ iY r p q = Φ.map (iX r p q) ≫ eqToHom (rfl) := by
    intro r p q
    exact ⟨pageInclusion_mono X r p q, pageInclusion_mono (mapped Φ X) r p q,
      by simpa only [eqToHom_refl, Category.comp_id] using
        comparisonPages_inclusion (Φ := Φ) X r p q⟩
  have H4 := fun r p q ↦ (comparisonPages (Φ := Φ) X r).ha p q
  have H5 := fun r p q ↦ (comparisonPages (Φ := Φ) X r).hf p q
  have H6 := fun r p q ↦ (comparisonPages (Φ := Φ) X r).hg p q
  have H7 := fun r p q ↦ (comparisonPages (Φ := Φ) X r).hd p q
  have H8 : ∀ (r : ℕ) (p q : ℤ),
      ∃ k : Φ.obj (kernel ((X.pageCouple r).d p q)) ⟶
        kernel (((mapped Φ X).pageCouple r).d p q), IsIso k ∧
        k ≫ kernel.ι (((mapped Φ X).pageCouple r).d p q) =
          Φ.map (kernel.ι ((X.pageCouple r).d p q)) ≫ (φ r p q).hom ∧
        Φ.map ((X.pageCouple r).derivedEProjection p q) ≫ (φ (r + 1) p q).hom =
          k ≫ ((mapped Φ X).pageCouple r).derivedEProjection p q := by
    intro r p q
    exact ⟨((comparisonPages (Φ := Φ) X r).ki p q).hom, inferInstance,
      (comparisonPages (Φ := Φ) X r).ki_ι p q,
      (comparisonPages (Φ := Φ) X r).ei_π p q⟩
  refine ⟨δ, φ, iX, iY, H0, H1, H2, H3, H4, H5, H6, H7, H8, ?_⟩
  intro a hDX hEX
  have hDY : ∀ p q : ℤ, q < a → IsZero ((mapped Φ X).D p q) :=
    fun p q h ↦ Φ.map_isZero (hDX p q h)
  have hEY : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero ((mapped Φ X).E p q) :=
    fun p q h ↦ Φ.map_isZero (hEX p q h)
  obtain ⟨LX, AX, hAX, hAX0, _, hstableX, htopX, hfiniteX, _, _, hconvX⟩ :=
    X.halfPlaneConvergence a hDX hEX
  obtain ⟨LY, AY, hAY, hAY0, _, hstableY, htopY, hfiniteY, _, _, hconvY⟩ :=
    (mapped Φ X).halfPlaneConvergence a hDY hEY
  let eA := normalizedColimitIso X AX AY hAX hAY
  have hA : ∀ n p : ℤ, Φ.map ((AX n).ι p) ≫ (eA n).hom = (AY n).ι p :=
    cocone_natural X (fun p q h ↦ hEX p q (Or.inl h)) AX AY eA
      (normalizedColimitIso_zero X AX AY hAX hAY hAX0 hAY0)
  let τ := filtrationIso X AX AY eA hA
  let κ := gradedIso X AX AY eA hA
  have hτ := filtrationIso_arrow X AX AY eA hA
  have hκ : ∀ n p : ℤ,
      Φ.map (cokernel.π (Subobject.ofLE
        ((X.imageFiltration n (AX n)).step (p + 1))
        ((X.imageFiltration n (AX n)).step p)
        ((X.imageFiltration n (AX n)).antitone_step (by omega)))) ≫ (κ n p).hom =
      (τ n p).hom ≫ cokernel.π (Subobject.ofLE
        (((mapped Φ X).imageFiltration n (AY n)).step (p + 1))
        (((mapped Φ X).imageFiltration n (AY n)).step p)
        (((mapped Φ X).imageFiltration n (AY n)).antitone_step (by omega))) :=
    fun n p ↦ quotientIso_π Φ _ _ _ _ _
  refine ⟨hDY, hEY, LX, LY, AX, AY, hAX, hAY, eA, hAX0, hAY0, ?_,
    (fun n p h ↦ ⟨htopX n p h, htopY n p h⟩),
    (fun n ↦ ⟨(hfiniteX n).1, (hfiniteY n).1⟩), hconvX, hconvY, τ, κ,
    hτ, hκ, ?_, ?_⟩
  · intro n p
    simpa only [eqToHom_refl, Category.id_comp] using hA n p
  · intro r p q hr
    obtain ⟨sX, hsX⟩ := hstableX r p q hr
    obtain ⟨sY, hsY⟩ := hstableY r p q hr
    obtain ⟨k, hk, hkι, hkπ⟩ := H8 r p q
    have : Epi (kernel.ι ((X.pageCouple r).d p q)) := by
      have : Epi (kernel.ι ((X.pageCouple r).d p q) ≫ sX.hom) := by
        rw [hsX]; infer_instance
      have h : Epi ((kernel.ι ((X.pageCouple r).d p q) ≫ sX.hom) ≫ sX.inv) :=
        inferInstance
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
    refine ⟨sX, sY, hsX, hsY, ?_⟩
    apply (cancel_epi (Φ.map (kernel.ι ((X.pageCouple r).d p q)))).mp
    rw [← Φ.map_comp_assoc, hsX, hkπ, ← Category.assoc, ← hkι,
      Category.assoc, hsY]
  · exact exactFunctor_halfPlane Φ X (mapped Φ X) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      δ φ iX iY H0 H1 H2 H3 H6 H8 a hDX hEX hDY hEY LX LY AX AY hAX hAY
      hAX0 hAY0 hconvX hconvY eA τ κ
      (by simpa only [eqToHom_refl, Category.id_comp] using hA) hτ hκ

end CategoryTheory.BigradedExactCouple
