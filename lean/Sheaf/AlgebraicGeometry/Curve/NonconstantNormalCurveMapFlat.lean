/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Sheaf.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.KrullDimension

/-!
# Flatness of a nonconstant morphism to a normal curve

Source: Stacks Project, `literature/stacks-project/curves.tex`, Tag 0CCK, lemma-flat
(blueprint: lem-a1-nonconstant-normal-curve-map-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism of integral curves over a field with at least two points in its image is flat
when its target is normal.

Source: Stacks Project, `curves.tex`, Tag 0CCK, lemma-flat
(blueprint: lem-a1-nonconstant-normal-curve-map-flat).

Proof:
1. Both curves are integral, hence have unique generic points by `lem-sc-scheme-sober`.
   `lem-pc-scheme-dimension-local-rings` identifies the dimension convention of
   `def-pc-curve` and `def-pc-dimension` with topological Krull dimension. Thus every
   target local ring has dimension at most one.
2. The generic point of the source maps to the generic point of the target. Otherwise its
   image has singleton closure: a proper irreducible closed subset of a dimension-one
   integral scheme cannot contain a strict specialization. Continuity would force the
   whole image into this singleton, contradicting the two-point image hypothesis.
   Thus the morphism is dominant (`def-kun-topological-krull-dimension`,
   `def-weil-locally-ringed-space-morphism`).
3. The field is Noetherian, and its spectrum is Noetherian. Finite type over this base makes
   the target locally Noetherian (`lem-weil-pbc-finite-type-over-noetherian`). Its stalks
   are localizations of Noetherian affine coordinate rings, hence Noetherian by
   `lem-weil-pbc-affine-open-stalk-localization` and `lem-weil-pbc-localization-noetherian`.
4. Each target stalk is a normal local domain of dimension at most one. In dimension one
   it is a DVR (`lem-sc-normal-dim1-dvr`, `def-sc-discrete-valuation-ring`). In dimension
   zero its maximal ideal is zero, so every nonzero element is a unit
   (`def-weil-pbc-krull-dimension-ring`, `lem-weil-pbc-local-ring-unit-criterion`). It is
   then a field. In either case it is a principal ideal domain.
5. The local rings embed into their function fields
   (`lem-sc-integral-scheme-stalks-in-function-field`). Dominance gives an injective map
   of generic-point fields. The stalk map commutes with the two embeddings, as checked
   on germs (`def-weil-locally-ringed-space-morphism`, `def-weil-pbc-module-stalk`), so
   it is injective.
6. An injective map of domains makes the source stalk torsion free over the target stalk.
   Since the latter is a PID, `lem-weil-pbc-pid-torsion-free-module-flat` makes the former
   a flat module. Finite generation as a module is unnecessary.
7. This holds at every source point; stalkwise flatness is flatness of the morphism
   (`def-weil-flat-morphism`).
-/
theorem flat_of_nonconstant_of_isNormalCurve {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsIntegralCurve (X ↘ Spec (.of k))] [IsIntegralCurve (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (h_nonconstant : ∃ x₁ x₂ : X, f x₁ ≠ f x₂) (h_normal : IsNormalScheme Y) :
    Flat f := by
  sorry

end AlgebraicGeometry
