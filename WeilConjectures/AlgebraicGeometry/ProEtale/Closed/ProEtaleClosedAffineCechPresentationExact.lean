/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.ProEtaleClosedCechPresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedAffineCechClosedExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedAffineCechOpenExact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-! # Exactness of the ambient affine closed Čech presentation

Source: the matching-relations argument of
`lem-sp-proetale-closed-injective-affine-cech`, Step 3.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The ambient free-module presentation of three adjacent affine closed Čech
degrees is exact before applying Hom into any injective.

Source: Step 3 of `lem-sp-proetale-closed-injective-affine-cech`.
(blueprint: lem-sp-proetale-closed-affine-cech-presentation-exact).

Proof: the closed restriction i^*T and the open restriction b^*T are exact
(`closedAffineCech_closed_restriction_exact`,
`closedAffineCech_open_restriction_exact`). The inverse images are exact, so
they commute with short-complex homology (`ShortComplex.mapHomologyIso`); hence
both restrictions of the homology of T are zero. The ranges of i and b are
complementary, so the restrictions jointly detect zero
(`ProEtale.isZero_of_isZero_upperStar_of_isCompl`), and T has zero homology,
that is, T is exact. Empty covers, empty schemes and the zero coefficient ring
need no separate argument. -/
theorem closedAffineCech_corepresentingShortComplex_exact
    (A : Type u) [CommRing A] [Finite A] {B O : Scheme.{u}}
    (b : O ⟶ B) [IsOpenImmersion b] [QuasiCompact b]
    (P : B.ProEt) (V : P.left.ProEt) (hV : IsAffine V.left)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      IsAffine (Presheaf.cechNerveObj U y).left.left)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      ProEt.topology P.left V)
    (q : ℕ) (T : CochainCorepresentingShortComplex
      (closedCechCoefficientFunctor A b P V U) q) :
    T.complex.Exact := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let i := b.closedComplement
  have hi := closedAffineCech_closed_restriction_exact A b P V hV U hU hcover q T
  have ho := closedAffineCech_open_restriction_exact A b P V hV U hU hcover q T
  have hpair : IsCompl (Set.range i.base) (Set.range b.base) := by
    change IsCompl (Set.range b.closedComplement) (Set.range b)
    rw [b.range_closedComplement]
    exact isCompl_compl.symm
  apply T.complex.exact_iff_isZero_homology.mpr
  apply ProEtale.isZero_of_isZero_upperStar_of_isCompl i b hpair
  · exact ((T.complex.map (ProEtale.upperStar C i)).exact_iff_isZero_homology.mp hi).of_iso
      (T.complex.mapHomologyIso (ProEtale.upperStar C i)).symm
  · exact ((T.complex.map (ProEtale.upperStar C b)).exact_iff_isZero_homology.mp ho).of_iso
      (T.complex.mapHomologyIso (ProEtale.upperStar C b)).symm

end AlgebraicGeometry.Scheme
