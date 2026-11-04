/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Flatness on a site is invariant under isomorphism

Source: Stacks Project, Tag 03ER (auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {R : Sheaf J CommRingCat.{w}}

/-- Flatness on a site is exactness of the monoidal right tensor functor.
Source: Stacks 03ER (auxiliary; not a blueprint node). -/
theorem isFlatOnSite_iff_exactFunctor_tensorRight
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    IsFlatOnSite M ↔
      letI := isMonoidal_W_independentCoefficients R
      letI := monoidalCategory R
      exactFunctor _ _ (tensorRight M) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  exact ⟨fun h ↦ (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M) h,
    fun h ↦ (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M).symm h⟩

/-- Flatness on a site is invariant under isomorphism of module sheaves.
Source: Stacks 03ER (auxiliary; not a blueprint node). -/
theorem IsFlatOnSite.of_iso
    {M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (e : M ≅ N) (hM : IsFlatOnSite M) : IsFlatOnSite N := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  rw [isFlatOnSite_iff_exactFunctor_tensorRight] at hM ⊢
  exact (exactFunctor _ _).prop_of_iso
    (NatIso.ofComponents (fun Z ↦ whiskerLeftIso Z e)
      (fun f ↦ (whisker_exchange f e.hom).symm)) hM

end SheafOfModules
