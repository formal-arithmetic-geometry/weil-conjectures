/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero

import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.SixFunctors.OpenTensorNormalization


/-!
# Compactification projection and arbitrary base-change exchange

Q155 stage-2 validation delivery of the published declaration.

Source: main-20261015 Weil blueprint, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-composition.proof.md, final base-change sentence; Stacks Project,
Tags 0E48 and 0GL1 (blueprint: lem-pur-co-smooth-pf-exchange-coherence).

The finite maps are precisely the components of `finiteExchangeProjection`. The ordinary
unbounded constant-coefficient module derived categories are written in the fixed-scalar
sheaf presentation already used by that definition. No etale-origin or Tor bound is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The chosen-compactification projection transformation commutes with arbitrary base-change
exchange. The left side first pulls back projection, then exchanges, then inserts the tensor
and composition comparisons. The right side inserts the source tensor comparison, tensors
exchange with the identity, and applies projection for the base-changed compactification.
The equality is natural in both unbounded inputs: every arrow is a component of the published
natural transformations or canonical comparison isomorphisms. Neither exchange nor projection
is assumed invertible. No separatedness of the horizontal morphism or of the schemes over a
field is required.
Source: main-20261015 blueprint, lem-pur-co-smooth-composition.proof.md, final sentence;
Stacks Project, Tags 0E48, 0GL1 and 0B56
(blueprint: lem-pur-co-smooth-pf-exchange-coherence).

Proof:
1. Write G = v*, H = bar(w)*, V = w*, R = Rp*, R' = Rp'*. The operations are the
   ordinary unbounded derived operations. The exchange e : GR -> R'H is the mate of the
   canonical pullback square. The open base-change map b : Hj! -> j'!V and open tensor
   map gamma are the normalized maps of lem-sf-open-tensor-normalization. Their restrictions
   under the open units are identities, and j'! is fully faithful.
2. Apply lem-weil-pbc-ringed-exchange-tensor-coherence to the proper-factor square at
   A = j!N and P. Its exchange and projection are these same counit-defined maps. Thus
   exchanging after proper projection equals projecting after exchange, with the canonical
   pullback/tensor comparisons. This uses neither proper-base-change invertibility nor
   boundedness or finite Tor amplitude.
3. For Q on the compactifying scheme, the open identity is
   b_(N tensor j*Q) H(gamma_(N,Q)) = gamma_(VN,HQ) (b_N tensor 1).
   Both endpoints are in the essential image of j'!. By full faithfulness it suffices to
   restrict with j'*. The normalized open maps restrict to identities. The remaining tensor
   and composition comparisons agree termwise on K-flat representatives: both send the
   inverse image of x tensor y to the tensor of the inverse images in each bidegree.
   They preserve the total differential, hence give equal derived maps. Use
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
   lem-weil-pbc-proetale-derived-pullback-composition for these representative comparisons.
4. Put C = j!N tensor p*P and W = N tensor u*P. Expand exchange and projection into their
   proper and open factors. Naturality of e at gamma : C -> j!W moves H(gamma) across e.
   Substitute the open identity from step 3 and the proper identity from step 2.
5. Naturality of the counit-defined proper projection in its first input, supplied by
   lem-weil-pbc-ringed-projection-mate-exact, moves R'(b_N tensor 1) across projection.
   The result is exactly the right side below. All factors are natural in N,P, so the
   equality is natural in both. No inverse of exchange or projection occurs. -/
theorem compactification_projection_exchange_coherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T' T U' U : Scheme.{u}} {w : T' ⟶ T} {u' : T' ⟶ U'}
    {u : T ⟶ U} {v : U' ⟶ U}
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (sq : IsPullback w u' u v) (c : Compactification u) [QuasiCompact c.i]
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (P : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))) :
    L((v)^*[ModuleCat.{u + 1} Λ]).map
        (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app N).app P) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c).app
        (((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).obj N).obj
          (L((u)^*[ModuleCat.{u + 1} Λ]).obj P)) ≫
      (Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} Λ]).map
        (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) w).app N).app
          (L((u)^*[ModuleCat.{u + 1} Λ]).obj P)) ≫
      (Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(T')[ModuleCat.{u + 1} Λ]).obj
          (L((w)^*[ModuleCat.{u + 1} Λ]).obj N)).map
            ((leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).inv.app P)) =
    ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) v).app
        ((Rf_!(c)[ModuleCat.{u + 1} Λ]).obj N)).app P ≫
      ((-⊗ᴸ-(U')[ModuleCat.{u + 1} Λ]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c).app N)).app
          (L((v)^*[ModuleCat.{u + 1} Λ]).obj P) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} Λ)
        (c.ofIsPullback sq)).app (L((w)^*[ModuleCat.{u + 1} Λ]).obj N)).app
          (L((v)^*[ModuleCat.{u + 1} Λ]).obj P) := by
  sorry

end AlgebraicGeometry.ProEtale
