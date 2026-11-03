/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneDivisorClassMaps

/-! # Pullback of the canonical proper-section normalization

Source: thm-pur-rank-one-thom, Step 3, the source identification of compact exchange
(blueprint: lem-pur-rank-one-proper-section-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Admissible

/-- Compact-support exchange carries the canonical proper-section identification to the
primed proper-section identification. This concerns only the supported coefficient source;
no divisor or Thom class occurs. Source: thm-pur-rank-one-thom, Step 3, proper coincidence
and composition (blueprint: lem-pur-rank-one-proper-section-pullback).
Proof: the section square is Cartesian, by pasting with the projection square and the
section identities. In the compactification the section has closed support. Expand
supportToOrdinary as the open-adjunction mate. The open exchange mate commutes with this
map by the two adjunction triangle identities and naturality of pullback composition.
Closed pushforward is exact on the Noetherian schemes, so the single-to-derived comparison
closedSingleMap commutes with closed exchange and coefficient-unit pullback. Mate-pasting
for the section and projection squares then identifies their composite with exchange for
the identity square. Under the direct-image compositors and rId this exchange is unitPull.
Thus the surviving factors are exactly the two displayed properSectionMap maps and the
closedSourcePull map. Invertibility of these proper-section maps is already proved in
properSectionMap_isIso; no isomorphy of a divisor class is involved. -/
theorem rankOne_properSection_pullback (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (c : Compactification V.p)
    {B' : Scheme.{u}} (b' : B' ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b'] [LocallyOfFiniteType b'] [QuasiCompact b']
    (V' : PurityVectorBundle P B' b' 1) (g : B' ⟶ B) (gV : V'.E ⟶ V.E)
    (sq : IsPullback gV V'.p V.p g)
    (hz : V'.zeroSection ≫ gV = g ≫ V.zeroSection) :
    (moduleObjectDerivedPullback Λ.X g).map (canonicalSigma P b V Λ c).hom ≫
        (unitPull Λ g).hom =
      compactExchange Λ sq c
          ((DerivedCategory.singleFunctor _ 0).obj (source Λ V.zeroSection)) ≫
        (rightDerivedLowerShriekOfCompactification Λ.X (c.ofIsPullback sq)).map
          (closedSourcePull Λ (CommSq.mk hz.symm)) ≫
        (canonicalSigma P b' V' Λ (c.ofIsPullback sq)).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
