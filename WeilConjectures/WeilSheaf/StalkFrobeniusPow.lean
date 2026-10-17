/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkFrobenius

/-!
# Restriction of global sections to a stalk and iterates of the Frobenius

Let `F` be a Weil sheaf on a `k₀`-scheme `X` and `s` a geometric point of `X̄` with
`s ≫ Frᵐ = σᵐ ≫ s`, for instance the geometric point over a closed point of degree `m`. The
restriction `Γ(X̄, F) ⟶ F_s` intertwines the `m`-th power of the Frobenius of the global sections
with the Frobenius of `F_s` relative to `𝔽_{qᵐ}`
(`AlgebraicGeometry.WeilSheaf.globalSectionsToStalkObj_frobenius_pow`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The global sections of `(eᵐ⁺¹)⁻¹_* N` and of `(e⁻¹)_* (eᵐ)⁻¹_* N` are identified compatibly
with the identification `(eᵐ⁺¹)⁻¹_* N ≅ (e⁻¹)_* (eᵐ)⁻¹_* N` defining the iterates of a Weil
structure. -/
@[reassoc]
lemma globalSectionsLowerStarIso_inv_comp_pow_succ {Y : Scheme.{u}} (e : Aut Y)
    (N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) (m : ℕ)
    (h : (e ^ (m + 1)).inv = (e ^ m).inv ≫ e.inv) :
    (ProEtale.globalSectionsLowerStarIso _ (e ^ (m + 1)).inv).inv.app N ≫
      (Sheaf.Γ _ _).map ((ProEtale.lowerStarCongr _ h).hom.app N) ≫
        (Sheaf.Γ _ _).map ((ProEtale.lowerStarComp _ (e ^ m).inv e.inv).inv.app N) =
    (ProEtale.globalSectionsLowerStarIso _ (e ^ m).inv).inv.app N ≫
      (ProEtale.globalSectionsLowerStarIso _ e.inv).inv.app (((e ^ m).inv)_*[_].obj N) := by
  have e₁ := ProEtale.globalSectionsLowerStarIso_congr (WeilCoefficients.{u} l) h N
  have e₂ := ProEtale.globalSectionsLowerStarIso_comp (WeilCoefficients.{u} l) (e ^ m).inv
    e.inv N
  rw [← cancel_mono ((ProEtale.globalSectionsLowerStarIso _ e.inv).hom.app _),
    ← cancel_mono ((ProEtale.globalSectionsLowerStarIso _ (e ^ m).inv).hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← e₂, ← Functor.map_comp_assoc _ ((ProEtale.lowerStarComp _ (e ^ m).inv e.inv).inv.app N),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, e₁, Iso.inv_hom_id_app]
  simp

variable (F : WeilSheaf k₀ l X)

/-- The `m`-th iterate of the Frobenius of the global sections of a Weil sheaf, through the
iterated Weil structure `φ_m : (Frᵐ)^* F ≅ F`:
`Γ(X̄, F) ≅ Γ(X̄, (Fr⁻ᵐ)_* F) --Γ(φ_m)--> Γ(X̄, F)`. -/
noncomputable def globalSectionsFrobeniusPow (m : ℕ) :
    (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj F.obj.carrier.X ⟶
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj F.obj.carrier.X :=
  (ProEtale.globalSectionsLowerStarIso _
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv).inv.app
        F.obj.carrier.X ≫
    (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom)

/-- The `(m + 1)`-st iterate of the Frobenius of the global sections is the `m`-th iterate
followed by the Frobenius. -/
lemma globalSectionsFrobeniusPow_succ (m : ℕ) :
    F.globalSectionsFrobeniusPow (m + 1) =
      F.globalSectionsFrobeniusPow m ≫
        (ProEtale.globalSectionsLowerStarIso _
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app F.obj.carrier.X ≫
        (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map F.obj.str.hom) := by
  have h : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).inv =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv := by
    rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]
  have n := (ProEtale.globalSectionsLowerStarIso (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.naturality
      ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom)
  rw [Functor.comp_map] at n
  rw [globalSectionsFrobeniusPow, globalSectionsFrobeniusPow,
    forget_map_frobeniusPowIso_succ_hom F m h]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% globalSectionsLowerStarIso_inv_comp_pow_succ]
  erw [← reassoc_of% n]
  rfl

end AlgebraicGeometry.WeilSheaf
