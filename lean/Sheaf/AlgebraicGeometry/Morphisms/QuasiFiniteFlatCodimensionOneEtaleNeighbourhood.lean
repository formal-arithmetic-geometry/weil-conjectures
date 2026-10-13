/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# The pointwise ramification criterion for a flat quasi-finite morphism

Source: Stacks Project, Lemma 58.21.2 (Tag 0BJH).
(blueprint: lem-sbc-quasi-finite-flat-codimension-one-etale-neighbourhood)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A flat morphism that is quasi-finite at a positive-dimensional source point
is etale near that point if it is unramified at its dimension-one generalizations.

Source: Stacks Project, Lemma 58.21.2 (Tag 0BJH).
(blueprint: lem-sbc-quasi-finite-flat-codimension-one-etale-neighbourhood)

Proof: Positive stalk dimension says that x is not the generic point of an
irreducible component. The supplied neighbourhoods, together with local finite
type, express unramifiedness at each dimension-one generalization of x.
Work etale locally on source and target (Stacks 02LK) to make f finite and x the
unique point above y = f(x). These localizations preserve stalk dimensions,
flatness and unramifiedness; etaleness descends through them. The resulting finite
flat map over a locally Noetherian target is finite locally free. Its discriminant
cuts out a locally principal closed branch locus D in the target (Stacks 0BJF).
Suppose y belongs to D. Source and target stalk dimensions agree for a finite
flat map (Stacks 00ON), so the target stalk at y has positive dimension. Stacks
0BJG supplies a dimension-one generalization y' of y in D, even if the
discriminant vanishes identically. There is a ramified point x' above y'. Since
the finite map is closed and its fibre at y contains only x, x' specializes to x.
Dimension equality again gives dimension one at x', contradicting the supplied
unramified neighbourhood. Thus y is outside D, and f is etale at x. The etale
locus is open, giving the asserted neighbourhood in the original source.
A zero-dimensional point is excluded by hpos; an empty source has no point x.
No normality, dominance or separateness hypothesis is required. -/
theorem exists_etale_neighbourhood_of_flat_of_quasiFiniteAt_of_codimension_one
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (x : X)
    (hq : f.QuasiFiniteAt x)
    (hpos : (0 : WithBot ℕ∞) < ringKrullDim (X.presheaf.stalk x))
    (hunram : ∀ x' : X, Specializes x' x →
      ringKrullDim (X.presheaf.stalk x') = 1 →
      ∃ V : X.Opens, x' ∈ V ∧ FormallyUnramified (V.ι ≫ f)) :
    ∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f) := by sorry

end AlgebraicGeometry.Scheme
