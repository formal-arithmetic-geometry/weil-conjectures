/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.SmoothDivisorLowSupportStandardPair
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local

/-!
# Étale chart transport for smooth-divisor support vanishing

This module isolates Step 4 of `lem-pur-smooth-divisor-low-support` from the standard-pair
calculation.  Its input is the already established standard-pair assertion, universally in
finite coefficients and in the relative affine-line base.  The conclusion is the support
vanishing for a smooth codimension-one pair.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Transport the standard-pair calculation across smooth codimension-one étale charts.

The proof uses the smooth-pair coordinate theorem and the stalk dimension equation to obtain
an étale jointly-surjective family of charts carrying the divisor to a zero section.  Exact
inverse image commutes with homology of the right-derived support functor, and the finite Tate
pullback comparison identifies the coefficients on each chart.  The standard-pair hypothesis
therefore gives zero homology on every chart; geometric stalk conservativity descends it to the
original sheaf.  The empty-divisor case is the zero support functor.  This is a transport step,
not another formulation of the standard-pair calculation.
(source: clause (b), local-comparison paragraph beginning
"Both classes are global classes supported on D";
blueprint: lem-pur-smooth-divisor-low-support)
-/
theorem isZero_homology_rightDerivedSectionsWithSupport_of_smooth_divisor_of_standard_pair
    {k : Type u} [Field k] (ell N : ℕ) (hell : Nat.Prime ell)
    (hell_unit : IsUnit (ell : k)) (hN : 1 ≤ N)
    {B T D : Scheme.{u}}
    (b : B ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
    [QuasiCompact b]
    (v : T ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n v]
    [IsSeparated (v ≫ b)] [LocallyOfFiniteType (v ≫ b)] [QuasiCompact (v ≫ b)]
    (i : D ⟶ T) [IsClosedImmersion i] [Smooth (i ≫ v)]
    [IsSeparated (i ≫ v ≫ b)] [LocallyOfFiniteType (i ≫ v ≫ b)]
    [QuasiCompact (i ≫ v ≫ b)]
    (hcodim : ∀ d : D, ringKrullDim (T.presheaf.stalk (i d)) =
      ringKrullDim (D.presheaf.stalk d) + (1 : WithBot ℕ∞))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ((ell ^ N : ℕ) : Λ) = 0)
    (hstandard : ∀ {Y G : Scheme.{u}}
      (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
      [QuasiCompact aY]
      (j : G ⟶ AffineSpace (ULift.{u} (Fin 1)) Y) [IsOpenImmersion j]
      (hj : Set.range j.base =
        (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ),
      ∀ q : ℤ, q < 2 →
        IsZero (((DerivedCategory.homologyFunctor _ q).obj
          ((sectionsWithSupport (ModuleCat.{u + 1} Λ) j).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (AlgebraicGeometry.Scheme.finiteEtaleTateSheaf Λ (ell ^ N)
                (AffineSpace (ULift.{u} (Fin 1)) Y) (by simpa using hΛ) 1))))) ) :
    ∀ q : ℤ, q < 2 →
      IsZero (((DerivedCategory.homologyFunctor _ q).obj
        ((sectionsWithSupport (ModuleCat.{u + 1} Λ) i.openComplement.ι).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (AlgebraicGeometry.Scheme.finiteEtaleTateSheaf Λ (ell ^ N) T hΛ 1))))) := by
  sorry

end AlgebraicGeometry.Etale
