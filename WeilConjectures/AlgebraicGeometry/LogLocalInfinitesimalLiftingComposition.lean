/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LogMorphismOperations
public import WeilConjectures.AlgebraicGeometry.LogInfinitesimalLifting
import WeilConjectures.AlgebraicGeometry.FirstOrderThickeningBaseChange
/-!
# Composition of etale-local logarithmic infinitesimal lifts
Source: Kato 3.2--3.3; ILO X 1.2
(blueprint: lem-sfb-log-local-lifting-composition).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Etale-local infinitesimal lifting for fine log tests is closed under composition.
Source: Kato 3.2--3.3; ILO X 1.2
(blueprint: lem-sfb-log-local-lifting-composition).

Proof: given a strict square-zero test for the composite, first apply the lifting
property of g to the composite of the top map with f. At a chosen point obtain an
etale neighbourhood V with a lift to the middle log scheme. Pull back the test to V.
Strict etale restriction preserves fine log structures, and the pulled-back
immersion is strict and square-zero. Apply the lifting property of f to this test
at a point over the original point. Compose the two etale neighbourhood maps.
The composite still contains the original point in its image. Associate the two
iterated scheme pullbacks to identify their test immersions; the associated log
structures agree because both are the strict pullback of the original log structure.
Compose the strict etale maps on test objects and use associativity of log-map
composition to verify the two required commuting squares. These are precisely the
witnesses in HasEtaleLocalInfinitesimalLifts for the composite. The construction is
pointwise and applies to empty tests without requiring a nonempty covering. -/
theorem EtaleLogMap.localLifts_comp {X Y Z : Scheme.{u}}
    {L : EtaleLogStructure X} {M : EtaleLogStructure Y} {N : EtaleLogStructure Z}
    (f : EtaleLogMap L M) (g : EtaleLogMap M N)
    (hf : f.HasEtaleLocalInfinitesimalLifts) (hg : g.HasEtaleLocalInfinitesimalLifts) :
    (f.comp g).HasEtaleLocalInfinitesimalLifts := by
  sorry
end AlgebraicGeometry
