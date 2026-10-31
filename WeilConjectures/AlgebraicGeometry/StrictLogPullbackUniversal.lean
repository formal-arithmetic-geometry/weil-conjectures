/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LogMorphismOperations
public import WeilConjectures.AlgebraicGeometry.LogInfinitesimalLifting
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.AssociatedLogUniversalStalks
/-!
# Strict log fibre products and their universal property
Source: ILO VI 1.1, VIII 3.3.5--3.3.6
(blueprint: lem-sfb-strict-log-pullback-universal).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- The log product property tests maps from arbitrary log schemes, including the
non-Noetherian fine test schemes used by infinitesimal lifting.
Source: ILO VI 1.1 (blueprint: lem-sfb-strict-log-pullback-universal). -/
def EtaleLogMap.IsLogPullback {X X' Y Y' : Scheme.{u}}
    {M : EtaleLogStructure X} {M' : EtaleLogStructure X'}
    {N : EtaleLogStructure Y} {N' : EtaleLogStructure Y'}
    (p : EtaleLogMap M' M) (q : EtaleLogMap M' N')
    (f : EtaleLogMap M N) (h : EtaleLogMap N' N) : Prop :=
  ∀ (T : Scheme.{u}) (L : EtaleLogStructure T)
    (a : EtaleLogMap L M) (b : EtaleLogMap L N'),
    a.comp f = b.comp h →
      ∃! c : EtaleLogMap L M', c.comp p = a ∧ c.comp q = b

/-- A strict scheme pullback has the log product property, and it exists within fs
locally Noetherian log schemes when the first map is locally of finite presentation.
Source: ILO VI 1.1, VIII 3.3.5--3.3.6
(blueprint: lem-sfb-strict-log-pullback-universal).

Proof: give X times_Y Y' the log structure associated to the inverse image of M_X.
On a chart Q on X this is the associated log structure of the pulled-back chart.
A section [z,u] is sent to the image of z times u by any proposed lift. The
unit-pushout relations hold because log maps preserve structural units; charts
and units generate the log structure, so this lift is unique. These formulas agree
on overlaps and glue. Strictness of h supplies the log map to Y', and the same
formula proves the universal property for every test log structure. The charts Q
remain fs after pullback. The underlying second projection is locally of finite
presentation by scheme base change and therefore has locally Noetherian source.
For any other square with strict first projection and a scheme pullback, its
strictness identifies its log structure with this very inverse-image structure;
the same chart formula, normalized on all pointed relative sections, proves its
universal property. No arbitrary choice of stalk isomorphism is used. -/
theorem strictLogPullback_universal {X Y Y' : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) (h : EtaleLogHom Y' Y) (hh : h.IsStrict) :
    (LocallyOfFinitePresentation f.base →
      ∃ (X' : FineSaturatedLogScheme.{u}) (p : EtaleLogHom X' X)
        (q : EtaleLogHom X' Y') (c : EtaleLogHom X' Y),
        p.IsStrict ∧ IsPullback p.base q.base f.base h.base ∧
          p.CompEq f c ∧ q.CompEq h c) ∧
    (∀ (X' : FineSaturatedLogScheme.{u}) (p : EtaleLogHom X' X)
      (q : EtaleLogHom X' Y') (c : EtaleLogHom X' Y),
      p.IsStrict → IsPullback p.base q.base f.base h.base →
        p.CompEq f c → q.CompEq h c →
          p.toLogMap.IsLogPullback q.toLogMap f.toLogMap h.toLogMap) := by
  sorry
end AlgebraicGeometry
