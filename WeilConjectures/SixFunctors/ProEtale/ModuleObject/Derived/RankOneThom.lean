/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneDivisorClassIntegral
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted

/-! # Rank-one Thom isomorphism

Source: latest blueprint, `thm-pur-rank-one-thom`, statement and proof Steps 1--3
(blueprint: thm-pur-rank-one-thom).

The positive divisor class and its proper-section and compact-support comparisons
are the recorded canonical constructions of `RankOneDivisorClassIntegral`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Admissible

/-- The rank-one Thom isomorphism, its base-change compatibility, its inverse trace,
and the untwisted compact-support formula.

Source: latest blueprint, `thm-pur-rank-one-thom`, statement and Steps 1--3
(blueprint: thm-pur-rank-one-thom).
The morphism is the positive frame-independent divisor class pushed through the
canonical proper-section identification.  Base change is the canonical exchange
square of `RankOneBaseChangeLaw`; the trace is the two-sided inverse.  The final
isomorphism is the negative Tate line, shifted by `-2`, obtained by untwisting the
positive Tate line in the Thom target.

Proof:
1. The zero section is a smooth Cartier divisor over the base. Apply the global
   frame-independent divisor-class construction; the local class is the positive
   Kummer boundary. The recorded proper-section comparison defines exactly tau.
2. Pull back to each geometric point and trivialize the fibre line. The full derived
   arrow is the supported-origin arrow followed by the specified forget-support map.
   The supported-origin normalization and support-to-compact comparison make both
   arrows invertible for each admissible coefficient. The Tate line is locally free
   of rank one, and compact support preserves bounded constructible finite-Tor objects.
   Thus the cone is bounded constructible. Geometric-point detection makes it zero,
   so tau is invertible.
3. Pullback preserves the zero-divisor pair and its positive Kummer class. Naturality
   of proper-section composition and compact exchange gives the displayed base-change
   law for the actual arrows, including identity maps. Define the trace as the inverse;
   cancellation gives its compatibility and both inverse identities.
4. Compactify the line bundle by its projective completion. Tensor the inverse of tau
   by the invertible negative Tate line shifted by -2. The open and proper perfect
   projection formulas and the positive/negative Tate evaluation identify its source
   with the untwisted compact-support image and its target with Lambda_B(-1)[-2].
-/
theorem rank_one_thom
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (c : Compactification V.p) :
    let τ := canonicalTau P b V Λ hΛ c
    V.zeroSection.ker.IsInvertible ∧
      IsIso τ ∧
      (∀ {B' : Scheme.{u}} (b' : B' ⟶ Spec (CommRingCat.of P.field.k))
        [IsSeparated b'] [LocallyOfFiniteType b'] [QuasiCompact b']
        (V' : PurityVectorBundle P B' b' 1) (g : B' ⟶ B) (gV : V'.E ⟶ V.E)
        (sq : IsPullback gV V'.p V.p g)
        (hz : V'.zeroSection ≫ gV = g ≫ V.zeroSection),
        g ≫ b = b' →
        RankOneBaseChangeLaw P b V Λ hΛ c b' V' g gV sq hz) ∧
      (∃ tr :
          (rightDerivedLowerShriekOfCompactification Λ.X c).obj
            (((DerivedCategory.singleFunctor (Modules Λ V.E) 0).obj
              (line P Λ hΛ V.E)) ⟦(2 : ℤ)⟧) ⟶
            (DerivedCategory.singleFunctor (Modules Λ B) 0).obj (unit Λ B),
        τ ≫ tr = 𝟙 _ ∧ tr ≫ τ = 𝟙 _) ∧
      (let Rπ := (rightDerivedLowerShriekOfCompactification Λ.X c).obj
          ((DerivedCategory.singleFunctor (Modules Λ V.E) 0).obj (unit Λ V.E))
       let negativeLine := (DerivedCategory.singleFunctor (Modules Λ B) 0).obj
          (coefficientSignedTwist B (condensedRingObj Λ.X B) (line P Λ hΛ B) (-1))
       Nonempty (Rπ ≅ negativeLine ⟦(-2 : ℤ)⟧)) := by
  sorry

/-- The rank-one vector-bundle trace is the inverse of the specified positive Thom map.
Source: latest blueprint, `thm-pur-rank-one-thom`, inverse-trace sentence
(blueprint: thm-pur-rank-one-thom). -/
def rankOneTrace
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (c : Compactification V.p) :=
  letI := (rank_one_thom P b V Λ hΛ c).2.1
  inv (canonicalTau P b V Λ hΛ c)

end AlgebraicGeometry.ProEtale.CondensedRing
