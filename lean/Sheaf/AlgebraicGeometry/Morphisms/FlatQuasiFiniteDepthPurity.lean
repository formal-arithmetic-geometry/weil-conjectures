/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.RingTheory.Depth

/-!
# Flat quasi-finite purity across a depth-two source boundary

Source: Stacks Project, Tag 0BJH, as used in Tag 0EY6(3).
(blueprint: lem-sbc-flat-quasi-finite-depth-purity)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A flat, locally quasi-finite morphism is etale if it is etale on a source open
whose complement has stalk depth at least two.

Source: Stacks Project, Lemma 58.21.2 (Tag 0BJH), and the proof of Tag 0EY6(3).
(blueprint: lem-sbc-flat-quasi-finite-depth-purity)

Proof: Fix x outside W. The bound on depth implies that its local dimension is
at least two, so x is not a generic point of a component. If x' specializes to x
and has local dimension one, depth is at most dimension; thus x' cannot be outside
W. The restriction hypothesis says that f is etale, hence unramified, at x'.
The four hypotheses of 0BJH now hold: flatness, quasi-finiteness at x, x not generic,
and unramifiedness at every dimension-one generalization. That lemma gives etaleness
at x. At points of W the conclusion is already assumed. Etaleness is local on the
source, so these neighbourhoods prove that f is etale.

For completeness, the purity argument in 0BJH is the following. Etale localization
makes f finite locally free with x the sole point above f(x). Its discriminant cuts
out a locally principal ramification locus in the target. If f(x) lay in this locus,
a dimension-one generalization in the locus would exist because x is not generic.
A ramified point above it specializes to x (finiteness makes f closed); finite flat
local maps preserve dimension, so this point has local dimension one, contradicting
unramifiedness there. Thus the discriminant is a unit at f(x). The empty source and
W equal to the whole source are included; no dominance or normality is assumed. -/
theorem etale_of_flat_quasiFinite_depth_two_boundary
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Flat f]
    (W : X.Opens) (het : Etale (W.ι ≫ f))
    (hboundary : ∀ x : X, x ∉ W →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := X.presheaf.stalk x) (X.presheaf.stalk x)) :
    Etale f := by sorry

end AlgebraicGeometry.Scheme
