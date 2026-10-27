/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Algebra.Hom

/-! # Localization of a presented algebra colimit

Source: Stacks 00CO and 04AX, the two universal properties.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
namespace Algebra.LocalizationColimit
variable {R : Type u} [CommRing R]
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

abbrev Away (A : Type u) [CommRing A] [Algebra R A] (s : R) :=
  Localization.Away (algebraMap R A s)

/-- Localize an algebra map at a common coefficient. -/
def map (s : R) (f : A →ₐ[R] B) : Away A s →+* Away B s :=
  IsLocalization.Away.lift (g := (algebraMap B _).comp f.toRingHom) (algebraMap R A s)
    (by
      change IsUnit (algebraMap B _ (f (algebraMap R A s)))
      rw [f.commutes]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp] theorem map_apply (s : R) (f : A →ₐ[R] B) (a : A) :
    map s f (algebraMap A _ a) = algebraMap B _ (f a) :=
  IsLocalization.Away.lift_eq _ _ a

theorem map_comp (s : R) (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (map s g).comp (map s f) = map s (g.comp f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A s))
  ext a
  change map s g (map s f (algebraMap A _ a)) = map s (g.comp f) (algebraMap A _ a)
  simp only [map_apply, AlgHom.comp_apply]

@[simp] theorem map_id (s : R) : map s (AlgHom.id R A) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A s))
  ext a
  exact map_apply s (AlgHom.id R A) a

/-- Localize the coefficient map. -/
def base (s : R) : Localization.Away s →+* Away A s :=
  IsLocalization.Away.map _ _ (algebraMap R A) s

@[simp] theorem base_apply (s : R) (a : R) :
    base (A := A) s (algebraMap R _ a) = algebraMap A _ (algebraMap R A a) :=
  IsLocalization.map_eq (S := Localization.Away s)
    (Q := Away A s) (Submonoid.le_comap_map _) a

theorem map_base (s : R) (f : A →ₐ[R] B) :
    (map s f).comp (base (A := A) s) = base (A := B) s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  ext a
  change map s f (base s (algebraMap R _ a)) = base s (algebraMap R _ a)
  rw [base_apply, map_apply, f.commutes, base_apply]

/-- A colimit universal property is preserved by inverting a coefficient. -/
theorem existsUnique_lift {I : Type} (i₀ : I)
    (D : I → Type u) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)]
    (F : Type u) [CommRing F] [Algebra R F]
    (rel : I → I → Prop)
    (tr : ∀ i j, rel i j → D i →ₐ[R] D j)
    (inc : ∀ i, D i →ₐ[R] F)
    (hcol : ∀ (Q : Type u) [CommRing Q] (a : ∀ i, D i →+* Q),
      (∀ i j (h : rel i j), (a j).comp (tr i j h).toRingHom = a i) →
      ∃! g : F →+* Q, ∀ i, g.comp (inc i).toRingHom = a i)
    (s : R) (Q : Type u) [CommRing Q]
    (a : ∀ i, Away (D i) s →+* Q)
    (ha : ∀ i j (h : rel i j), (a j).comp (map s (tr i j h)) = a i) :
    ∃! g : Away F s →+* Q, ∀ i, g.comp (map s (inc i)) = a i := by
  let b : ∀ i, D i →+* Q := fun i ↦ (a i).comp (algebraMap (D i) _)
  have hb : ∀ i j (h : rel i j), (b j).comp (tr i j h).toRingHom = b i := by
    intro i j h
    ext x
    have he := RingHom.congr_fun (ha i j h) (algebraMap (D i) _ x)
    change a j (map s (tr i j h) (algebraMap (D i) _ x)) = _ at he
    rw [map_apply] at he
    exact he
  obtain ⟨g, hg, hgu⟩ := hcol Q b hb
  have hunit : IsUnit (g (algebraMap R F s)) := by
    have he := RingHom.congr_fun (hg i₀) (algebraMap R (D i₀) s)
    change g (inc i₀ (algebraMap R (D i₀) s)) = a i₀ (algebraMap (D i₀) _ _) at he
    rw [(inc i₀).commutes] at he
    rw [he]
    exact (IsLocalization.Away.algebraMap_isUnit _).map (a i₀)
  let g' : Away F s →+* Q := IsLocalization.Away.lift (algebraMap R F s) hunit
  have hg' (i : I) : g'.comp (map s (inc i)) = a i := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R (D i) s))
    ext x
    change g' (map s (inc i) (algebraMap (D i) _ x)) = a i (algebraMap (D i) _ x)
    rw [map_apply]
    change IsLocalization.Away.lift _ _ (algebraMap F _ (inc i x)) = _
    rw [IsLocalization.Away.lift_eq]
    exact RingHom.congr_fun (hg i) x
  refine ⟨g', hg', fun k hk ↦ ?_⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R F s))
  have he : k.comp (algebraMap F _) = g := hgu _ (by
    intro i
    ext x
    have he := RingHom.congr_fun (hk i) (algebraMap (D i) _ x)
    change k (map s (inc i) (algebraMap (D i) _ x)) = _ at he
    rw [map_apply] at he
    exact he)
  ext x
  change k (algebraMap F _ x) = g' (algebraMap F _ x)
  rw [show g' (algebraMap F _ x) = g x from IsLocalization.Away.lift_eq _ _ x]
  exact RingHom.congr_fun he x

end Algebra.LocalizationColimit
