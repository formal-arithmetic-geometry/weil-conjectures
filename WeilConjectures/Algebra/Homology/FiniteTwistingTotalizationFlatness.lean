/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationData
import WeilConjectures.Algebra.Homology.KFlatTelescopeClosure
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSiteBiproduct
import Mathlib.Data.Fintype.Order

/-! # K-flatness of finite twisting totalizations

This helper isolates the bounded-above flatness argument once a realization record
has been supplied.
-/

/- The flatness criterion is an existing dependency of the finite totalization construction. -/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
variable {R} {a b : ℤ}

/-- If the terms of every graded complex are flat, the finite direct-sum totalization
and all of its tail complexes are K-flat. Choose a common upper bound for the
bounded graded complexes, use finite biproduct flatness for every totalization term
and tail term, and apply the bounded-above-flat K-flat criterion (Stacks, Tag 06YQ).
The assumed K-flatness of the graded complexes is retained in the interface but is
not needed by this bounded-above argument.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (step 3 of lem-trf-filtered-mapping-cylinder-step).
(blueprint: lem-trf-finite-filtered-totalization-flatness) -/
theorem finiteTwistingTotalization_kflat_of_flat
    (a b : ℤ) (_hab : a ≤ b) (D : FiniteTwistingFamily R a b)
    (M : FiniteTwistingTotalization D)
    (hflat : (∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
      SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D.G p).X n)) ∧
      (∀ p : ↥(Finset.Icc a b), (D.G p).IsKFlatIndependentCoefficients)) :
    M.P.IsKFlatIndependentCoefficients ∧
      ∀ r : ℤ, IsKFlatIndependentCoefficients (J := J) (R := R)
        (M.F.step r : CochainComplex (ringedSiteModules.{w}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) := by
  have hbiproduct {I : Type} [Finite I] (g : I → ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (hg : ∀ i, IsZero (g i)) :
      IsZero (⨁ g) :=
    (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun i ↦ (hg i).eq_of_tgt _ _)
  choose N hN using D.bounded
  obtain ⟨n, hn⟩ := Finite.exists_le N
  have hzero (p : ↥(Finset.Icc a b)) (i : ℤ) (hi : n < i) : IsZero ((D.G p).X i) :=
    hN p i ((hn p).trans_lt hi)
  refine ⟨?_, fun r ↦ ?_⟩
  · have : M.P.IsStrictlyLE n := (isStrictlyLE_iff _ n).2 fun i hi ↦
      (hbiproduct _ fun p ↦ hzero p i hi).of_iso (M.coordinates i)
    exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R M.P n
      fun i ↦ (SheafOfModules.isFlatOnSite_biproduct _ fun p ↦ hflat.1 p i).of_iso
        (M.coordinates i).symm
  · have : (M.F.step r : CochainComplex (ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ).IsStrictlyLE n :=
      (isStrictlyLE_iff _ n).2 fun i hi ↦
        (hbiproduct _ fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ hzero p.val i hi).of_iso
          (M.tailCoordinates r i)
    exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ n
      fun i ↦ (SheafOfModules.isFlatOnSite_biproduct _
        fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ hflat.1 p.val i).of_iso
        (M.tailCoordinates r i).symm

end CochainComplex
