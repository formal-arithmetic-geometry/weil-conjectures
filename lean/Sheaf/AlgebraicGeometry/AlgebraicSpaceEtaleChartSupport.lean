/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Support on an étale scheme chart of an algebraic space

Source: Stacks Project, Morphisms of Spaces, Tag 07TY, lemma-support-covering;
Properties of Spaces, Tag 04KA, definition-support
(blueprint: lem-sfb-space-etale-chart-support).

The space support is the existing nonzero-geometric-germ locus `moduleSupport`.
The chart module is the existing restriction to Zariski opens `schemeRestriction`,
the inverse direction of the Zariski/étale quasi-coherent equivalence. Its ordinary
stalks are Mathlib's module stalks. The chart need not cover the space.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Support on any étale scheme chart is the inverse image of geometric-stalk support.
The chart `T` includes its scheme over `S`, its map to `X`, and representable étaleness.
There is no finite type, Noetherian, or surjectivity assumption.
Source: Stacks Project, Morphisms of Spaces, Tag 07TY, lemma-support-covering
(blueprint: lem-sfb-space-etale-chart-support).

Proof:
1. Fix an ordinary point u of T and a geometric lift, with image xbar in X. Put
   A = O_{T,u}, B = O_{X,xbar}, and N = (M_T)_u. The comparison
   lem-sfb-space-quasicoherent-geometric-stalk-tensor (05VP) identifies
   N tensor_A B with M_xbar. By lem-sfb-space-strict-local-flatness (04KF),
   A to B is the strict-henselization map for this lift. Apply
   lem-sc-strict-henselization-faithfully-flat (07QM) to obtain faithful flatness.
2. The exactness criterion in def-weil-pbc-faithfully-flat-ring-map applied to
   0 to N to 0 gives N = 0 iff B tensor_A N = 0. The tensor swap from
   def-weil-pbc-module-tensor-product identifies this with N tensor_A B = 0,
   hence with M_xbar = 0. No finite-generation or Nakayama argument is used.
3. The vanishing condition is independent of the geometric representative:
   choose an étale surjective atlas V to X and a fixed v over any x. For every
   geometric representative over x, lem-sfb-etale-geometric-point-specified-lift
   (05VN) supplies a lift centered at v. Steps 1 and 2 identify its vanishing
   with the vanishing of the fixed ordinary stalk (M_V)_v. This also covers
   points outside the image of T. The existing moduleSupport definition expresses
   this representative-independent nonzero-germ locus without choosing a lift.
4. The class of the composite geometric point over u is schemePointMap T.obj.hom u
   (def-a1-space-point-topology). Thus the two support membership conditions agree
   at every u, which proves the set equality. -/
theorem etale_chart_moduleSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (M : X.QCoh) (T : X.EtaleSite) :
    {x : X.etaleForget.obj T |
      ¬ Subsingleton (((X.schemeRestriction T).obj M.obj).presheaf.stalk x)} =
      schemePointMap T.obj.hom ⁻¹' moduleSupport M.obj := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
