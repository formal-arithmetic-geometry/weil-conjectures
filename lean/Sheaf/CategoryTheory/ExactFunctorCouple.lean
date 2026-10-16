/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.CategoryTheory.HalfPlaneConvergence
import Sheaf.CategoryTheory.ExactFunctorHalfPlane
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
private structure FunctorComparison
    (X : BigradedExactCouple C s) (Y : BigradedExactCouple B s) where
  dIso : ∀ p q : ℤ, Φ.obj (X.D p q) ≅ Y.D p q
  eIso : ∀ p q : ℤ, Φ.obj (X.E p q) ≅ Y.E p q
  alpha_comm : ∀ p q : ℤ, Φ.map (X.alpha p q) ≫ (dIso (p - 1) (q + 1)).hom =
    (dIso p q).hom ≫ Y.alpha p q
  f_comm : ∀ p q : ℤ, Φ.map (X.f p q) ≫ (dIso (p + 2) (q - 1)).hom =
    (eIso p q).hom ≫ Y.f p q
  g_comm : ∀ p q : ℤ, Φ.map (X.g p q) ≫ (eIso (p + s) (q - s)).hom =
    (dIso p q).hom ≫ Y.g p q
private noncomputable def mapped (X : BigradedExactCouple C s) : BigradedExactCouple B s :=
  ⟨{ D := fun i ↦ Φ.obj (X.toExactCouple.D i)
     E := fun i ↦ Φ.obj (X.toExactCouple.E i)
     α := fun i j ↦ Φ.map (X.toExactCouple.α i j)
     f := fun i j ↦ Φ.map (X.toExactCouple.f i j)
     g := fun i j ↦ Φ.map (X.toExactCouple.g i j)
     shape_α := fun i j h ↦ by rw [X.toExactCouple.shape_α i j h, Φ.map_zero]
     shape_f := fun i j h ↦ by rw [X.toExactCouple.shape_f i j h, Φ.map_zero]
     shape_g := fun i j h ↦ by rw [X.toExactCouple.shape_g i j h, Φ.map_zero]
     α_g := fun i j k ↦ by rw [← Φ.map_comp, X.toExactCouple.α_g, Φ.map_zero]
     g_f := fun i j k ↦ by rw [← Φ.map_comp, X.toExactCouple.g_f, Φ.map_zero]
     f_α := fun i j k ↦ by rw [← Φ.map_comp, X.toExactCouple.f_α, Φ.map_zero]
     exact_α_g := fun i j k hij hjk ↦ (X.toExactCouple.exact_α_g i j k hij hjk).map Φ
     exact_g_f := fun i j k hij hjk ↦ (X.toExactCouple.exact_g_f i j k hij hjk).map Φ
     exact_f_α := fun i j k hij hjk ↦ (X.toExactCouple.exact_f_α i j k hij hjk).map Φ }⟩

variable {Φ}
omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
private theorem differential_comm (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.map (X.d p q) ≫ (T.eIso (p + 2 + s) (q - 1 - s)).hom =
      (T.eIso p q).hom ≫ Y.d p q := by
  dsimp [d]
  rw [Functor.map_comp, Category.assoc, T.g_comm, ← Category.assoc, T.f_comm,
    Category.assoc]
private noncomputable def imageIso (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.obj (X.derivedD p q) ≅ Y.derivedD p q :=
  (PreservesImage.iso Φ (X.alpha (p + 1) (q - 1))).symm ≪≫
    (im (C := B)).mapIso (Arrow.isoMk' _ _ (T.dIso (p + 1) (q - 1))
      (T.dIso ((p + 1) - 1) ((q - 1) + 1)) (T.alpha_comm (p + 1) (q - 1)).symm)
omit [Φ.Additive] in
private theorem imageIso_inclusion (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    (imageIso X Y T p q).hom ≫ Y.derivedDInclusion p q =
      Φ.map (X.derivedDInclusion p q) ≫ (T.dIso p q).hom := by
  dsimp only [imageIso, Iso.trans_hom, Functor.mapIso_hom, im,
    derivedDInclusion, derivedD, Iso.symm_hom]
  rw [Category.assoc, ← Category.assoc (image.map _)]
  erw [image.map_ι]
  simp only [Arrow.isoMk_hom_right, Arrow.mk_hom, ← Category.assoc]
  erw [PreservesImage.inv_comp_image_ι_map]
  simp only [Functor.map_comp, Category.assoc]
  rw [transport_square Φ (fun p q ↦ (T.dIso p q).hom) (by omega) (by omega)]
private noncomputable def cyclesIso (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.obj (kernel (X.d p q)) ≅ kernel (Y.d p q) :=
  PreservesKernel.iso Φ _ ≪≫ kernel.mapIso _ _ (T.eIso p q)
    (T.eIso (p + 2 + s) (q - 1 - s)) (differential_comm X Y T p q)
omit [PreservesFiniteColimits Φ] in
private theorem cyclesIso_inclusion (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    (cyclesIso X Y T p q).hom ≫ kernel.ι (Y.d p q) =
      Φ.map (kernel.ι (X.d p q)) ≫ (T.eIso p q).hom := by
  simp [cyclesIso]
omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
private theorem boundary_comm (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.map (X.dInto p q) ≫ (T.eIso p q).hom =
      (T.eIso (p - s - 2) (q + s + 1)).hom ≫ Y.dInto p q := by
  dsimp [dInto]
  rw [Functor.map_comp, Category.assoc, transport_square Φ
    (fun p q ↦ (T.eIso p q).hom) (by omega) (by omega),
    ← Category.assoc, differential_comm, Category.assoc]
omit [PreservesFiniteColimits Φ] in
private theorem liftedBoundary_comm (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.map (kernel.lift (X.d p q) (X.dInto p q) (X.dInto_comp_d p q)) ≫
        (cyclesIso X Y T p q).hom =
      (T.eIso (p - s - 2) (q + s + 1)).hom ≫
        kernel.lift (Y.d p q) (Y.dInto p q) (Y.dInto_comp_d p q) := by
  apply (cancel_mono (kernel.ι (Y.d p q))).mp
  rw [Category.assoc, cyclesIso_inclusion, ← Category.assoc,
    ← Functor.map_comp, kernel.lift_ι, Category.assoc, kernel.lift_ι, boundary_comm]
private noncomputable def quotientIso (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.obj (X.derivedE p q) ≅ Y.derivedE p q :=
  PreservesCokernel.iso Φ _ ≪≫ cokernel.mapIso _ _
    (T.eIso (p - s - 2) (q + s + 1)) (cyclesIso X Y T p q)
      (liftedBoundary_comm X Y T p q)
private theorem quotientIso_projection (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derivedEProjection p q) ≫ (quotientIso X Y T p q).hom =
      (cyclesIso X Y T p q).hom ≫ Y.derivedEProjection p q := by
  simp [quotientIso, derivedEProjection]

omit [Φ.Additive] in
private theorem derived_alpha_comm (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derived.alpha p q) ≫ (imageIso X Y T (p - 1) (q + 1)).hom =
      (imageIso X Y T p q).hom ≫ Y.derived.alpha p q := by
  have hx := (Classical.choice X.derivedMaps_exists).alpha_comm p q
  have hy := (Classical.choice Y.derivedMaps_exists).alpha_comm p q
  rw [← derived_alpha] at hx
  rw [← derived_alpha] at hy
  have : Mono (Y.derivedDInclusion (p - 1) (q + 1)) := by
    dsimp [derivedDInclusion]; infer_instance
  apply (cancel_mono (Y.derivedDInclusion (p - 1) (q + 1))).mp
  rw [Category.assoc, imageIso_inclusion, ← Category.assoc, ← Functor.map_comp,
    hx, Functor.map_comp, Category.assoc, T.alpha_comm,
    ← Category.assoc, ← imageIso_inclusion]
  simp only [Category.assoc]
  rw [hy]
private theorem derived_f_comm (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derived.f p q) ≫ (imageIso X Y T (p + 2) (q - 1)).hom =
      (quotientIso X Y T p q).hom ≫ Y.derived.f p q := by
  have hx := (Classical.choice X.derivedMaps_exists).f_comm p q
  have hy := (Classical.choice Y.derivedMaps_exists).f_comm p q
  rw [← derived_f] at hx
  rw [← derived_f] at hy
  have : Mono (Y.derivedDInclusion (p + 2) (q - 1)) := by
    dsimp [derivedDInclusion]; infer_instance
  have : Epi (Φ.map (X.derivedEProjection p q)) := by
    dsimp [derivedEProjection]; infer_instance
  apply (cancel_epi (Φ.map (X.derivedEProjection p q))).mp
  apply (cancel_mono (Y.derivedDInclusion (p + 2) (q - 1))).mp
  simp only [Category.assoc]
  rw [imageIso_inclusion, ← Category.assoc, ← Functor.map_comp,
    ← Category.assoc, ← Functor.map_comp, Category.assoc, hx, Functor.map_comp,
    Category.assoc, T.f_comm]
  rw [← Category.assoc (Φ.map (X.derivedEProjection p q)) (quotientIso X Y T p q).hom,
    quotientIso_projection, Category.assoc, hy,
    ← Category.assoc (cyclesIso X Y T p q).hom, cyclesIso_inclusion]
  simp only [Category.assoc]
omit [Φ.Additive] in
private theorem imageIso_factor (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.map (factorThruImage (X.alpha (p + 1) (q - 1))) ≫ (imageIso X Y T p q).hom =
      (T.dIso (p + 1) (q - 1)).hom ≫ factorThruImage (Y.alpha (p + 1) (q - 1)) := by
  have : Mono (Y.derivedDInclusion p q) := by
    dsimp [derivedDInclusion]; infer_instance
  apply (cancel_mono (Y.derivedDInclusion p q)).mp
  rw [Category.assoc, imageIso_inclusion, ← Category.assoc, ← Functor.map_comp]
  dsimp only [derivedDInclusion]
  simp only [image.fac_assoc, Functor.map_comp, Category.assoc]
  rw [transport_square Φ (fun p q ↦ (T.dIso p q).hom) (by omega) (by omega)]
  rw [← Category.assoc, T.alpha_comm]
  simp only [Category.assoc]
omit [PreservesFiniteColimits Φ] in
private theorem g_cycles_comm (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.map (X.gToCycles p q) ≫ (cyclesIso X Y T (p + s) (q - s)).hom =
      (T.dIso p q).hom ≫ Y.gToCycles p q := by
  apply (cancel_mono (kernel.ι (Y.d (p + s) (q - s)))).mp
  rw [Category.assoc, cyclesIso_inclusion, ← Category.assoc, ← Functor.map_comp]
  dsimp only [gToCycles]
  simp only [kernel.lift_ι, Category.assoc]
  exact T.g_comm p q
private theorem derived_g_comm (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derived.g p q) ≫
        (quotientIso X Y T (p + (s + 1 : ℕ)) (q - (s + 1 : ℕ))).hom =
      (imageIso X Y T p q).hom ≫ Y.derived.g p q := by
  have hx := (Classical.choice X.derivedMaps_exists).g_comm p q
  have hy := (Classical.choice Y.derivedMaps_exists).g_comm p q
  rw [← derived_g] at hx
  rw [← derived_g] at hy
  apply (cancel_epi (Φ.map (factorThruImage (X.alpha (p + 1) (q - 1))))).mp
  rw [← Category.assoc, ← Functor.map_comp, hx]
  rw [← Category.assoc (Φ.map (factorThruImage (X.alpha (p + 1) (q - 1))))
    (imageIso X Y T p q).hom, imageIso_factor, Category.assoc, hy]
  simp only [Functor.map_comp, Category.assoc]
  rw [transport_square Φ (fun p q ↦ (quotientIso X Y T p q).hom)
    (show (p + 1) + (s : ℤ) = p + (s + 1 : ℕ) by omega)
    (show (q - 1) - (s : ℤ) = q - (s + 1 : ℕ) by omega)]
  rw [← Category.assoc (Φ.map (X.derivedEProjection ((p + 1) + s) ((q - 1) - s))),
    quotientIso_projection]
  rw [← Category.assoc (Φ.map (X.gToCycles (p + 1) (q - 1)))]
  rw [← Category.assoc (Φ.map (X.gToCycles (p + 1) (q - 1))), g_cycles_comm]
  simp only [Category.assoc]

private noncomputable def comparisonDerived (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) (T : FunctorComparison Φ X Y) :
    FunctorComparison Φ X.derived Y.derived where
  dIso := imageIso X Y T
  eIso := quotientIso X Y T
  alpha_comm := derived_alpha_comm X Y T
  f_comm := derived_f_comm X Y T
  g_comm := derived_g_comm X Y T
private noncomputable def comparisonPages
    (X : BigradedExactCouple C 0) (Y : BigradedExactCouple B 0)
    (T : FunctorComparison Φ X Y) :
    ∀ r : ℕ, FunctorComparison Φ (X.pageCouple r) (Y.pageCouple r)
  | 0 => T
  | r + 1 => comparisonDerived (X.pageCouple r) (Y.pageCouple r) (comparisonPages X Y T r)

private noncomputable def pageInclusion {A : Type*} [Category A] [Abelian A]
    (X : BigradedExactCouple A 0) :
    ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q
  | 0, p, q => 𝟙 (X.D p q)
  | r + 1, p, q => (X.pageCouple r).derivedDInclusion p q ≫ pageInclusion X r p q

private theorem pageInclusion_mono {A : Type*} [Category A] [Abelian A]
    (X : BigradedExactCouple A 0) (r : ℕ) (p q : ℤ) : Mono (pageInclusion X r p q) := by
  induction r with
  | zero => change Mono (𝟙 (X.D p q)); infer_instance
  | succ r ih =>
    have : Mono ((X.pageCouple r).derivedDInclusion p q) := by
      dsimp [derivedDInclusion]; infer_instance
    dsimp only [pageInclusion]
    infer_instance

private theorem comparisonPages_inclusion
    (X : BigradedExactCouple C 0) (Y : BigradedExactCouple B 0)
    (T : FunctorComparison Φ X Y) (r : ℕ) (p q : ℤ) :
    ((comparisonPages X Y T r).dIso p q).hom ≫ pageInclusion Y r p q =
      Φ.map (pageInclusion X r p q) ≫ (T.dIso p q).hom := by
  induction r with
  | zero =>
    change (T.dIso p q).hom ≫ 𝟙 _ = Φ.map (𝟙 _) ≫ (T.dIso p q).hom
    simp only [Functor.map_id, Category.comp_id, Category.id_comp]
  | succ r ih =>
    change (imageIso (X.pageCouple r) (Y.pageCouple r)
      (comparisonPages X Y T r) p q).hom ≫
        ((Y.pageCouple r).derivedDInclusion p q ≫ pageInclusion Y r p q) = _
    rw [← Category.assoc, imageIso_inclusion, Category.assoc, ih]
    simp only [pageInclusion, Functor.map_comp, Category.assoc]

section FiltrationComparison

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (X : BigradedExactCouple C 0) (Y : BigradedExactCouple B 0)
  (hD : ∀ p q : ℤ, Φ.obj (X.D p q) = Y.D p q)
  (ha : ∀ p q : ℤ, Φ.map (X.alpha p q) ≫ eqToHom (hD (p - 1) (q + 1)) =
    eqToHom (hD p q) ≫ Y.alpha p q)
  (AX : ∀ n : ℤ, AlphaColimit X n) (AY : ∀ n : ℤ, AlphaColimit Y n)
  (hAX : ∀ n : ℤ, (AX n).obj = X.D 0 n)
  (hAY : ∀ n : ℤ, (AY n).obj = Y.D 0 n)
  (hAX0 : ∀ n : ℤ, (AX n).ι 0 ≫ eqToHom (hAX n) =
    eqToHom (by congr 1; omega))
  (hAY0 : ∀ n : ℤ, (AY n).ι 0 ≫ eqToHom (hAY n) =
    eqToHom (by congr 1; omega))
private theorem alpha_left_iso {A : Type*} [Category A] [Abelian A]
    (Z : BigradedExactCouple A 0)
    (hE : ∀ p q : ℤ, p < 0 → IsZero (Z.E p q)) (p q : ℤ) (hp : p ≤ 0) :
    IsIso (Z.alpha p q) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, p = i + 2 := ⟨p - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, q = j - 1 := ⟨q + 1, by omega⟩
  have hker : kernelSubobject (Z.alpha (i + 2) (j - 1)) = ⊥ := by
    have hz : Z.f i j = 0 := (hE i j (by omega)).eq_zero_of_src _
    exact (Z.exact_alpha i j).symm.trans (by rw [hz, imageSubobject_zero])
  have : Mono (Z.alpha (i + 2) (j - 1)) :=
    Abelian.mono_of_kernel_ι_eq_zero _ (Subobject.mk_eq_bot_iff_zero.mp hker)
  have him : imageSubobject (Z.alpha (i + 2) (j - 1)) = ⊤ := by
    have hz : Z.g (i + 2 - 1) (j - 1 + 1) = 0 :=
      (hE _ _ (by omega)).eq_zero_of_tgt _
    simpa only [hz, kernelSubobject_zero] using Z.exact_g (i + 2) (j - 1)
  apply (Subobject.isIso_iff_mk_eq_top _).mpr
  rwa [imageSubobject_mono] at him
include ha hAX hAY hAX0 hAY0 in
private theorem colimit_comparison
    (hEX : ∀ p q : ℤ, p < 0 → IsZero (X.E p q)) :
    ∃ eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj,
    ∀ n p : ℤ, Φ.map ((AX n).ι p) ≫ (eA n).hom =
      eqToHom (hD p (n - p)) ≫ (AY n).ι p := by
  let eA (n : ℤ) := Φ.mapIso (eqToIso (hAX n)) ≪≫ eqToIso (hD 0 n) ≪≫
    (eqToIso (hAY n)).symm
  have hdiag (n p : ℤ) :
      Φ.map (X.alphaDiagonal n p) ≫ eqToHom (hD p (n - p)) =
        eqToHom (hD (p + 1) (n - (p + 1))) ≫ Y.alphaDiagonal n p := by
    dsimp only [alphaDiagonal]
    rw [Functor.map_comp, Category.assoc]
    have ht : Φ.map (eqToHom (show X.D (p + 1 - 1) (n - (p + 1) + 1) =
        X.D p (n - p) by congr 1 <;> omega)) ≫ eqToHom (hD p (n - p)) =
        eqToHom (hD (p + 1 - 1) (n - (p + 1) + 1)) ≫ eqToHom (by congr 1 <;> omega) := by
      simp only [eqToHom_map, eqToHom_trans]
    rw [ht, ← Category.assoc, ha, Category.assoc]
  refine ⟨eA, ?_⟩
  intro n p
  induction p using Int.inductionOn' with
  | b => exact 0
  | zero =>
    dsimp only [eA, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Iso.symm_hom,
      eqToIso.inv]
    rw [← Category.assoc, ← Functor.map_comp, hAX0]
    have hAYι : (AY n).ι 0 = eqToHom (by rw [hAY n]; congr 1; omega) := by
      apply (cancel_mono (eqToHom (hAY n))).mp
      simpa only [eqToHom_trans] using hAY0 n
    rw [hAYι]
    simp only [eqToHom_map, eqToHom_trans]
  | succ p hp ih =>
    rw [← (AX n).comm p, Functor.map_comp, Category.assoc, ih,
      ← Category.assoc, hdiag, Category.assoc, (AY n).comm]
  | pred p hp ih =>
    have : IsIso (X.alphaDiagonal n (p - 1)) := by
      have := alpha_left_iso X hEX (p - 1 + 1) (n - (p - 1 + 1)) (by omega)
      dsimp only [alphaDiagonal]; infer_instance
    apply (cancel_epi (Φ.map (X.alphaDiagonal n (p - 1)))).mp
    rw [← Category.assoc, ← Functor.map_comp, (AX n).comm,
      ← Category.assoc (Φ.map (X.alphaDiagonal n (p - 1))), hdiag,
      Category.assoc, (AY n).comm]
    convert ih using 1 <;> congr 6 <;> omega
private theorem filtration_comparison
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (hA : ∀ n p : ℤ, Φ.map ((AX n).ι p) ≫ (eA n).hom =
      eqToHom (hD p (n - p)) ≫ (AY n).ι p) :
    ∃ τ : ∀ n p : ℤ, Φ.obj ((X.imageFiltration n (AX n)).step p : C) ≅
      ((Y.imageFiltration n (AY n)).step p : B),
    ∃ κ : ∀ n p : ℤ, Φ.obj ((X.imageFiltration n (AX n)).gradedPiece p) ≅
      (Y.imageFiltration n (AY n)).gradedPiece p,
    (∀ n p : ℤ, (τ n p).hom ≫ ((Y.imageFiltration n (AY n)).step p).arrow =
      Φ.map (((X.imageFiltration n (AX n)).step p).arrow) ≫ (eA n).hom) ∧
    (∀ n p : ℤ,
      Φ.map (cokernel.π (Subobject.ofLE
        ((X.imageFiltration n (AX n)).step (p + 1))
        ((X.imageFiltration n (AX n)).step p)
        ((X.imageFiltration n (AX n)).antitone_step (by omega)))) ≫ (κ n p).hom =
      (τ n p).hom ≫ cokernel.π (Subobject.ofLE
        ((Y.imageFiltration n (AY n)).step (p + 1))
        ((Y.imageFiltration n (AY n)).step p)
        ((Y.imageFiltration n (AY n)).antitone_step (by omega)))) := by
  let τ (n p : ℤ) := Φ.mapIso (imageSubobjectIso ((AX n).ι p)) ≪≫
    (PreservesImage.iso Φ ((AX n).ι p)).symm ≪≫
    (im (C := B)).mapIso (Arrow.isoMk' _ _ (eqToIso (hD p (n - p))) (eA n)
      (hA n p).symm) ≪≫ (imageSubobjectIso ((AY n).ι p)).symm
  have hτ (n p : ℤ) :
      (τ n p).hom ≫ ((Y.imageFiltration n (AY n)).step p).arrow =
        Φ.map (((X.imageFiltration n (AX n)).step p).arrow) ≫ (eA n).hom := by
    dsimp only [τ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, im,
      imageFiltration, DecreasingFiltration.step]
    simp only [Category.assoc, imageSubobject_arrow']
    erw [image.map_ι]
    simp only [Arrow.isoMk_hom_right, Arrow.mk_hom, ← Category.assoc]
    simp only [Category.assoc]
    erw [PreservesImage.inv_comp_image_ι_map_assoc]
    rw [← Category.assoc, ← Functor.map_comp, imageSubobject_arrow]
  let kX (n p : ℤ) := Subobject.ofLE
    ((X.imageFiltration n (AX n)).step (p + 1))
    ((X.imageFiltration n (AX n)).step p)
    ((X.imageFiltration n (AX n)).antitone_step (by omega))
  let kY (n p : ℤ) := Subobject.ofLE
    ((Y.imageFiltration n (AY n)).step (p + 1))
    ((Y.imageFiltration n (AY n)).step p)
    ((Y.imageFiltration n (AY n)).antitone_step (by omega))
  have hstep (n p : ℤ) : Φ.map (kX n p) ≫ (τ n p).hom =
      (τ n (p + 1)).hom ≫ kY n p := by
    apply (cancel_mono ((Y.imageFiltration n (AY n)).step p).arrow).mp
    rw [Category.assoc, hτ, ← Category.assoc, ← Functor.map_comp]
    dsimp only [kX, kY]
    rw [Subobject.ofLE_arrow, Category.assoc, Subobject.ofLE_arrow, hτ]
  let κ (n p : ℤ) := PreservesCokernel.iso Φ (kX n p) ≪≫
    cokernel.mapIso _ _ (τ n (p + 1)) (τ n p) (hstep n p)
  refine ⟨τ, κ, hτ, ?_⟩
  intro n p
  simp [κ, kX, kY]

end FiltrationComparison

/-- An exact additive functor transports an exact couple, all its derived pages, and
its half-plane abutment filtration, with the canonical cohomology comparisons.
Source: Stacks Project, Tags 011Q, 011R, 011S, 0AMJ, and the blueprint transport argument
(blueprint: lem-sp-exact-functor-couple).

Proof, step 1: exactness preserves the three image/kernel equalities and additivity
preserves the zero composites (def-sp-exact-couple, lem-sp-exact-functor-preserves-homology).
Step 2: one derived step commutes with the functor. The D term is an image and the E
term is cycles modulo boundaries. Preservation of images, kernels and cokernels gives
the comparisons. The defining restriction equations characterize alpha, f and g by
cancelling mono inclusions and epi projections (lem-sp-derived-couple-exact).
Step 3: recursively iterate the explicitly constructed derived comparison. The kernel
and cokernel maps give the next E comparison; the image inclusions give the D
comparison. Cancel image inclusions and quotient projections to prove all three
structure-map squares directly, hence the differential square.
Step 4: preservation of zero objects carries the half-plane vanishing conditions to
the image couple. The stabilization bound is unchanged; quotient comparisons commute
with the stabilization maps, giving the infinite-page comparison (thm-sp-half-plane-convergence).
Step 5: the abutment is D at (0,n). Exactness carries the images of all alpha powers
to their images, so each filtration step and its successive quotient are preserved
(def-sp-filtration, lem-sp-exact-functor-preserves-homology).
Step 6: at a sufficiently large page, transport the filtration along the inverse alpha
isomorphism to its D term. The induced g map identifies its quotient with E. Applying
the functor to this quotient equation and cancelling the epimorphic quotient map proves
the final graded-piece square (thm-sp-half-plane-convergence, def-sp-convergence). -/
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
  let Y := mapped Φ X
  let hD : ∀ p q : ℤ, Φ.obj (X.D p q) = Y.D p q := fun _ _ ↦ rfl
  let hE : ∀ p q : ℤ, Φ.obj (X.E p q) = Y.E p q := fun _ _ ↦ rfl
  let T : FunctorComparison Φ X Y :=
    { dIso := fun p q ↦ eqToIso (hD p q)
      eIso := fun p q ↦ eqToIso (hE p q)
      alpha_comm := fun p q ↦ by
        simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]
        rfl
      f_comm := fun p q ↦ by
        simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]
        rfl
      g_comm := fun p q ↦ by
        simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]
        rfl }
  let δ := fun r ↦ (comparisonPages X Y T r).dIso
  let φ := fun r ↦ (comparisonPages X Y T r).eIso
  have H0 : ∀ p q : ℤ, δ 0 p q = eqToIso (hD p q) ∧
      φ 0 p q = eqToIso (hE p q) := fun _ _ ↦ ⟨rfl, rfl⟩
  have H1 : ∀ p q : ℤ, pageInclusion X 0 p q = 𝟙 _ ∧
      pageInclusion Y 0 p q = 𝟙 _ := fun _ _ ↦ ⟨rfl, rfl⟩
  have H2 : ∀ (r : ℕ) (p q : ℤ),
      pageInclusion X (r + 1) p q =
        (X.pageCouple r).derivedDInclusion p q ≫ pageInclusion X r p q ∧
      pageInclusion Y (r + 1) p q =
        (Y.pageCouple r).derivedDInclusion p q ≫ pageInclusion Y r p q :=
    fun _ _ _ ↦ ⟨rfl, rfl⟩
  have H3 : ∀ (r : ℕ) (p q : ℤ),
      Mono (pageInclusion X r p q) ∧ Mono (pageInclusion Y r p q) ∧
      (δ r p q).hom ≫ pageInclusion Y r p q =
        Φ.map (pageInclusion X r p q) ≫ eqToHom (hD p q) :=
    fun r p q ↦ ⟨pageInclusion_mono X r p q, pageInclusion_mono Y r p q,
      comparisonPages_inclusion X Y T r p q⟩
  have H4 := fun r ↦ (comparisonPages X Y T r).alpha_comm
  have H5 := fun r ↦ (comparisonPages X Y T r).f_comm
  have H6 := fun r ↦ (comparisonPages X Y T r).g_comm
  have H7 := fun r ↦ differential_comm (X.pageCouple r) (Y.pageCouple r)
    (comparisonPages X Y T r)
  have H8 : ∀ (r : ℕ) (p q : ℤ),
      ∃ k : Φ.obj (kernel ((X.pageCouple r).d p q)) ⟶
        kernel ((Y.pageCouple r).d p q), IsIso k ∧
      k ≫ kernel.ι ((Y.pageCouple r).d p q) =
        Φ.map (kernel.ι ((X.pageCouple r).d p q)) ≫ (φ r p q).hom ∧
      Φ.map ((X.pageCouple r).derivedEProjection p q) ≫ (φ (r + 1) p q).hom =
        k ≫ (Y.pageCouple r).derivedEProjection p q := by
    intro r p q
    refine ⟨(cyclesIso (X.pageCouple r) (Y.pageCouple r)
      (comparisonPages X Y T r) p q).hom, inferInstance, ?_, ?_⟩
    · exact cyclesIso_inclusion _ _ _ _ _
    · exact quotientIso_projection _ _ _ _ _
  refine ⟨Y, hD, hE, T.alpha_comm, T.f_comm, T.g_comm, δ, φ,
    pageInclusion X, pageInclusion Y, H0, H1, H2, H3, H4, H5, H6, H7, H8, ?_⟩
  intro a hDX hEX
  have hDY : ∀ p q : ℤ, q < a → IsZero (Y.D p q) := by
    intro p q hq
    exact (Functor.map_isZero Φ (hDX p q hq)).of_iso (eqToIso (hD p q))
  have hEY : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (Y.E p q) := by
    intro p q hpq
    exact (Functor.map_isZero Φ (hEX p q hpq)).of_iso (eqToIso (hE p q))
  obtain ⟨LX, AX, hAX, hAX0, _, hXstable, hXtop, hXfinite, _, _, hXconv⟩ :=
    halfPlaneConvergence X a hDX hEX
  obtain ⟨LY, AY, hAY, hAY0, _, hYstable, hYtop, hYfinite, _, _, hYconv⟩ :=
    halfPlaneConvergence Y a hDY hEY
  obtain ⟨eA, hA⟩ := colimit_comparison Φ X Y hD T.alpha_comm AX AY
    hAX hAY hAX0 hAY0 (fun p q hp ↦ hEX p q (Or.inl hp))
  obtain ⟨τ, κ, hτ, hκ⟩ := filtration_comparison Φ X Y hD AX AY eA hA
  obtain ⟨hInfinity, hLarge⟩ :=
    exactFunctor_halfPlane Φ X Y hD hE δ φ (pageInclusion X) (pageInclusion Y)
      H0 H1 H2 H3 H6 H8 a hDX hEX hDY hEY LX LY AX AY hAX hAY
      hAX0 hAY0 hXconv hYconv eA τ κ hA hτ hκ
  refine ⟨hDY, hEY, LX, LY, AX, AY, hAX, hAY, eA, hAX0, hAY0, hA,
    fun n p hp ↦ ⟨hXtop n p hp, hYtop n p hp⟩,
    fun n ↦ ⟨(hXfinite n).1, (hYfinite n).1⟩, hXconv, hYconv, τ, κ,
    hτ, hκ, ?_, hInfinity, hLarge⟩
  intro r p q hr
  obtain ⟨sX, hsX⟩ := hXstable r p q hr
  obtain ⟨sY, hsY⟩ := hYstable r p q hr
  obtain ⟨k, hkiso, hk, hπ⟩ := H8 r p q
  have : Epi ((X.pageCouple r).derivedEProjection p q) := by
    dsimp [derivedEProjection]; infer_instance
  have : Epi (kernel.ι ((X.pageCouple r).d p q)) := by
    have : Epi (kernel.ι ((X.pageCouple r).d p q) ≫ sX.hom) := by
      rw [hsX]; infer_instance
    have : Epi ((kernel.ι ((X.pageCouple r).d p q) ≫ sX.hom) ≫ sX.inv) :=
      inferInstance
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this
  refine ⟨sX, sY, hsX, hsY, ?_⟩
  apply (cancel_epi (Φ.map (kernel.ι ((X.pageCouple r).d p q)))).mp
  rw [← Category.assoc, ← Functor.map_comp, hsX, hπ]
  rw [← Category.assoc (Φ.map (kernel.ι ((X.pageCouple r).d p q)))
    (φ r p q).hom, ← hk, Category.assoc, hsY]

end CategoryTheory.BigradedExactCouple
