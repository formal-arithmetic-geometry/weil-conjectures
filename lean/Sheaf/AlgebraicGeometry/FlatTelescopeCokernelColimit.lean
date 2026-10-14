/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # The canonical sequential colimit as a telescope cokernel

Source: the union-cokernel paragraph of `lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-flat-telescope-cokernel-colimit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable {Y : Scheme.{u}}
  (F : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
  (s : ∀ n : ℕ, F n ⟶ F (n + 1))

/-- Compatible maps out of a sequence kill its identity-minus-shift morphism. -/
lemma flatTelescopeDifferential_desc_zero
    {T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (q : ∀ n : ℕ, F n ⟶ T) (hq : ∀ n : ℕ, s n ≫ q (n + 1) = q n) :
    flatTelescopeDifferential F s ≫ Sigma.desc q = 0 := by
  apply Sigma.hom_ext
  intro n
  simp [flatTelescopeDifferential, Preadditive.comp_sub, Preadditive.sub_comp, hq]

noncomputable def flatTelescopeCokernelCocone : Cocone (Functor.ofSequence s) where
  pt := cokernel (flatTelescopeDifferential F s)
  ι := NatTrans.ofSequence
    (fun n ↦ Sigma.ι F n ≫ cokernel.π (flatTelescopeDifferential F s)) (fun n ↦ by
      simp only [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      change s n ≫ Sigma.ι F (n + 1) ≫ cokernel.π (flatTelescopeDifferential F s) =
        Sigma.ι F n ≫ cokernel.π (flatTelescopeDifferential F s)
      have h := congrArg (fun k ↦ Sigma.ι F n ≫ k)
        (cokernel.condition (flatTelescopeDifferential F s))
      simp only [flatTelescopeDifferential, Preadditive.comp_sub,
        Preadditive.sub_comp, Category.id_comp, Sigma.ι_desc_assoc, comp_zero] at h
      exact (sub_eq_zero.mp h).symm)


/-- This cocone is the sequential colimit, by the coproduct and cokernel properties.

Source: the union-cokernel paragraph of `lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-flat-telescope-cokernel-colimit).

Proof: A compatible family of maps from F(n) extends uniquely to the coproduct.
Compatibility says exactly that it annihilates identity minus shift, so it descends
uniquely through the cokernel. Its composites with the displayed cocone injections
are the original maps, by the two universal properties. -/
noncomputable def flatTelescopeCokernelIsColimit :
    IsColimit (flatTelescopeCokernelCocone F s) where
  desc c := cokernel.desc (flatTelescopeDifferential F s) (Sigma.desc (fun n ↦ c.ι.app n))
    (flatTelescopeDifferential_desc_zero F s _ (fun n ↦ by
      simpa only [Functor.ofSequence_map_homOfLE_succ] using c.w (homOfLE (Nat.le_succ n))))
  fac c n := by
    change (Sigma.ι F n ≫ cokernel.π (flatTelescopeDifferential F s)) ≫
      cokernel.desc (flatTelescopeDifferential F s) (Sigma.desc (fun n ↦ c.ι.app n)) _ = _
    simp only [Category.assoc, cokernel.π_desc, Sigma.ι_desc]
  uniq c m hm := by
    apply (cancel_epi (cokernel.π (flatTelescopeDifferential F s))).1
    apply Sigma.hom_ext
    intro n
    simp only [cokernel.π_desc, Sigma.ι_desc]
    have h := hm n
    change (Sigma.ι F n ≫ cokernel.π (flatTelescopeDifferential F s)) ≫ m = _ at h
    simpa only [Category.assoc] using h

end AlgebraicGeometry
