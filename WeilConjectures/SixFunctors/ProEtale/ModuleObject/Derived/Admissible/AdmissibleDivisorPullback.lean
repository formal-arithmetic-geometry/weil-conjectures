/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleDivisorClass

/-! # Pullback of the global admissible divisor class

Source: thm-pur-rank-one-thom, Step 3, pullback of the frame class
(blueprint: lem-pur-admissible-divisor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.CondensedRing.Admissible

/-- The global singleton-frame divisor arrow commutes with arbitrary pullback of smooth
Cartier pairs. Source: thm-pur-rank-one-thom, Step 3, and lem-pur-divisor-class, frame
construction (blueprint: lem-pur-admissible-divisor-pullback).
Proof: pull the full Kummer sequence and its root-coordinate inclusion back along g.
The units-sheaf map is natural and need not be invertible; its coordinate maps
induce the map to the primed middle inverse limit. The root-generator and inverse-limit
projection equations identify the pulled Tate line
with linePull. The coefficient insertion commutes with this comparison on its integral
generators, hence on the scalar extension. Naturality of the extension class and of the
coefficient localization sequence gives pullback of +boundary(kappa(f)) on every
principal chart. Pulling an equation chart back gives its pulled equation, with the
closed source comparison defined by closedSourcePull. Smooth-pair low-support vanishing
and bottom-degree separation identify the global pulled class with the unique glued
primed class. Under the evaluation-normalized supported-Hom comparison, exact inverse
image sends evaluation on one to evaluation on the restricted supported one. The derived
representable transport theorem therefore carries the class equality to this equality
of actual arrows, with the displayed closed-source and shifted Tate comparisons.
No flatness of g, finite-coefficient reduction, or invertibility of a Thom arrow is used. -/
theorem divisorArrow_pullback (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X D' X' : Scheme.{u}}
    (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (a' : X' ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) (i' : D' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i']
    (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
    (hpair : SmoothDivisorPair P a i) (hpair' : SmoothDivisorPair P a' i')
    (d : D' ⟶ D) (g : X' ⟶ X) (hbase : g ≫ a = a')
    (sq : IsPullback d i' i g) :
    closedSourcePull Λ sq.toCommSq ≫ divisorArrow P Λ hΛ a' i' hI' hpair' =
      (moduleObjectDerivedPullback Λ.X g).map (divisorArrow P Λ hΛ a i hI hpair) ≫
        (twistPull P Λ hΛ a' a g).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.Admissible
