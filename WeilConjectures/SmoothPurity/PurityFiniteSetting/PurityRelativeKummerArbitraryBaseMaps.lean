/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-! # Relative Kummer maps over an arbitrary base

Source: blueprint latest, relative Kummer proof, Steps 1 and 2 and the comparison
paragraph (blueprint: lem-pur-relative-kummer-arbitrary-base-maps).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The five specified relative maps over an arbitrary k-scheme. No finiteness,
separatedness or geometric-point assumption is made on B. Affine higher vanishing is
omitted here: it follows formally from the affine unit isomorphism.
Source: blueprint latest, sk-lem-sp-reduction/prop-pur-gm-relative-kummer.proof.md,
Steps 1 and 2 and the comparison paragraph
(blueprint: lem-pur-relative-kummer-arbitrary-base-maps).

Proof: write r=ell^N, choose a primitive r-th root in k, and normalize the finite
coefficient and root-line maps. The absolute Kummer computation gives the normalized
constant isomorphisms in degree zero, the coordinate generator in degree one, and
vanishing in the other positive degrees on the two absolute curves. Identify the
actual affine line with the polynomial model and its basic open with the Laurent
model, preserving projections and the coordinate unit. For every geometric point of
B let S be its strict localization. Apply strict-local derived invariance to the
smooth curve C over k and the affine morphism S to Spec k. The normalized-stalk
comparison carries the relative unit to the absolute constant map and the relative
edge of the coordinate boundary to the absolute Kummer generator. Conservative
etale stalks detect the two affine unit isomorphisms, the punctured degree-zero unit,
the punctured degree-one generator and all the stated higher vanishings. Both actual
projections are affine and hence qcqs over arbitrary B. Apply the exact etale-to-
pro-etale comparison, normalized on the actual units and scalar Kummer class; its
unit and edge identities identify the transported maps with precisely the displayed
maps. Thus the five conclusions hold without imposing finite type on B. -/
theorem relative_kummer_arbitrary_base_maps (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (B : Scheme.{u})
    (a : B ⟶ Spec (CommRingCat.of P.field.k)) :
    IsIso (P.relativeUnit h (lineProjection B) false) ∧
    IsIso (P.relativeUnit h (lineProjection B) true) ∧
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (P.relativeUnit h (puncturedProjection B) true)) ∧
    IsIso (P.kummerGenerator h B a) ∧
    (∀ (q : ℕ), 2 ≤ q → IsZero
      ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection B)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured B) true)))) := by sorry

end WeilConjectures.PurityFiniteSetting
