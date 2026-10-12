/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Surjective part of the local proper-flat structure-sheaf criterion.
Source: Stacks Project, Tag 0E62, proof of `perfect-lemma-proper-flat-h0`, localized
at the fixed point; the rank-minimal finite free model is Tag 0BCD.
(blueprint: lem-sc-proper-flat-structure-sheaf-stalk-surjective).

Proof: Properness makes the locally finitely presented morphism quasi-compact and
quasi-separated, hence finitely presented. The structure sheaf is finitely presented
and relatively flat. Perfect direct image and base change therefore give a perfect
complex E = Rf_* O_X whose derived fibre is RΓ(X_s, O). Its negative cohomology vanishes,
and its degree-zero cohomology is κ(s) via the canonical map in the hypothesis.
Take the affine bounded finite free model of Tag 0BCD, with term ranks equal to the
fibre cohomology dimensions. It has no negative terms, and its degree-zero term is
free of rank one. The differentials after passage to κ(s) are zero: in each degree,
the cohomology dimension equals the term dimension, so both adjacent differential
ranks are zero. Thus its degree-zero term identifies with degree-zero fibre cohomology.

On this affine, projectivity of O in degree zero lets us represent the derived unit
O[0] → E by a chain map into the bounded projective model. Localize at s. Its degree-zero
component is a map between rank-one free modules whose residue is the assumed canonical
isomorphism. It is multiplication by an element outside the maximal ideal, hence a unit.
The chain-map equation d^0 u^0 = 0 forces d^0 = 0 in the local ring. There are no negative
terms, so degree-zero cohomology of the model is its degree-zero term at s.

Left exactness of direct image identifies H^0(E) with f_* O_X and the degree-zero unit
with the ordinary structure map. Under the canonical tensor identification f^* O_S ≅ O_X,
the section formula in `exists_tensorPullbackAdjunction` identifies the chosen unit,
followed by pushforward of that identification, with the ordinary structure map.
Pushforward and passage to stalks preserve this isomorphism.
For any output germ, transport it to the degree-zero free module, multiply by
the inverse unit, and transport back to obtain a preimage under the stated stalk map.
-/
theorem surjective_structureSheafMap_stalk_of_proper_flat_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (s : S)
    (hs : IsIso (f.fiberToSpecResidueField s).appTop) :
    Function.Surjective
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf)).stalkLinearMap s) := by sorry

end AlgebraicGeometry
