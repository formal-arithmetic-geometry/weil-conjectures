/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
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

/-!
# A single-fibre criterion for the structure-sheaf unit on a stalk

Source: Stacks Project, Tag 0E62, proof of `perfect-lemma-proper-flat-h0`, localized at
one point (blueprint: lem-sc-proper-flat-structure-sheaf-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If the canonical functions map on one fibre is an isomorphism, the ordinary module
adjunction unit is bijective at that point of the base. No hypothesis on the functions
of the other fibres, and no assertion about arbitrary base change, is made here.
Source: Stacks Project, Tag 0E62, proof of `perfect-lemma-proper-flat-h0`; the local
finite free model used in that proof is Tag 0BCD, `lift-perfect-from-residue-field`.
(blueprint: lem-sc-proper-flat-structure-sheaf-stalk).

Proof: By `lem-pc-rf-perfect-base-change`, applied to the relatively flat, finitely
presented structure sheaf, E = Rf_* O_X is perfect and its derived fibre at s is
RΓ(X_s, O). The negative fibre cohomology is zero, independently of the hypothesis on
H^0. On an affine neighbourhood of s take the bounded finite free residue model of
`lem-sc-perfect-finite-free-residue-model`. Its negative terms vanish and its term in
degree zero has rank one, because H^0 of the fibre is κ(s). The derived unit O[0] → E
is represented in this model by a chain map: on the affine, O is projective and the
bounded complex of projectives computes derived Hom. The degree-zero component of
this chain map reduces to the assumed canonical isomorphism over κ(s). In the local
ring at s this component is therefore a unit between free modules of rank one.
The chain-map identity d^0 u^0 = 0 now gives d^0 = 0 at s. With no negative terms,
H^0(E)_s equals the degree-zero free module, and H^0(u)_s is bijective. Finally
H^0(Rf_* O_X) is f_* O_X, with the canonical map induced by the derived unit; identify
f^* O_S with O_X. The tensor-formula adjunction's sectionwise unit formula identifies
its chosen unit with this canonical map followed by the pushforward of that
identification. The identification is an isomorphism, so bijectivity is unchanged.
This proves the claim for the actual chosen adjunction, not for an arbitrary map.
-/
theorem bijective_structureSheafMap_stalk_of_proper_flat_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (s : S)
    (hs : IsIso (f.fiberToSpecResidueField s).appTop) :
    Function.Bijective
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf)).stalkLinearMap s) := by sorry

end AlgebraicGeometry
