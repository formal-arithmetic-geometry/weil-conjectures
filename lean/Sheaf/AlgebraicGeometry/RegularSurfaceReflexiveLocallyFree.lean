/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentSheafHom
import WeilConjectures.AlgebraicGeometry.FinitePresentationSourceStalk
import WeilConjectures.AlgebraicGeometry.StalkInternalHomFinitePresentation
import WeilConjectures.AlgebraicGeometry.StalkInternalHomEvaluation
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocallyFreeEvaluationBiduality
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.DualDepthTwo
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.RingTheory.RegularLocalMaximalCohenMacaulayFree
import Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfCoherentFreeStalks

/-!
# Reflexive coherent modules on regular schemes of dimension at most two

Source: Stacks Project, Divisors, Tag 0B3N, Lemma
`divisors-lemma-reflexive-over-regular-dim-2`
(blueprint: lem-sfb-regular-surface-reflexive-locally-free).

Reflexivity means invertibility of the existing canonical evaluation morphism
`SheafOfModules.bidual`, whose target is the twice-iterated internal sheaf Hom into
`SheafOfModules.unit`. Finite local freeness allows different ranks on different opens.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on a regular scheme of topological Krull dimension at most two
is reflexive if and only if it is finite locally free. Reflexivity uses the canonical
map sending a section `s` to the functional `λ ↦ λ(s)`, not just an abstract
isomorphism with the double dual.

Source: Stacks Project, Divisors, Tag 0B3N
(blueprint: lem-sfb-regular-surface-reflexive-locally-free).

Proof:
1. By def-weil-regular-scheme, X is locally Noetherian and every stalk R is a
   Noetherian regular local ring. By lem-sc-scheme-stalk-dimension-generalization-chains,
   its dimension is the supremum of generalization-chain lengths at the point.
   Closures give irreducible closed chains in X, so def-kun-topological-krull-dimension
   bounds this dimension by two. Thus it is zero, one or two; no integrality is assumed.
2. The structure module is quasi-coherent of finite type, hence coherent by
   pqf-lem-coherent-ft-locnoeth. By lem-weil-pbc-coherent-sheaf-hom-coherent the dual
   of F is coherent. By pqf-def-coherent, both F and its dual admit local finite
   presentations: choose finite generators and then finite generators of the kernel.
   By lem-weil-pbc-finite-presentation-source-stalk their stalks M and N are finite
   presented R-modules, hence finite R-modules.
3. Applying lem-weil-pbc-stalk-internal-hom-finite-presentation twice identifies N
   with Hom_R(M,R) and the double-dual stalk with Hom_R(N,R). By
   lem-weil-pbc-stalk-internal-hom-evaluation, the stalk evaluation is exactly
   m ↦ (λ ↦ λ(m)). Reflexivity therefore makes M algebraically reflexive.
4. If F is finite locally free, apply lem-sf-locally-free-sheaf-evaluation-biduality
   on the Zariski site to its finite-free trivializing cover. Its canonical evaluation
   is the same map, hence invertible. This includes rank zero and varying ranks.
5. Conversely assume reflexivity. At a point with dim R = 0, regularity makes the
   maximal ideal zero, so R is a field. By lem-weil-pbc-vector-space-free, M is free.
   Finiteness from step 2 makes its basis finite: finite generators involve finitely
   many basis vectors and span M, so every basis vector belongs to that finite set.
6. If dim R = 1, lem-sc-regular-dim1-dvr makes R a DVR. M is torsion free: if a ≠ 0
   and am = 0, then aλ(m) = λ(am) = 0 for every dual functional λ. Since R is a
   domain, every λ(m) is zero, and injective evaluation gives m = 0. Now
   lem-sc-dvr-fg-torsionfree-free makes the finite module M finite free.
7. If dim R = 2, choose two generators of the maximal ideal. By
   lem-weil-pbc-regular-local-generators-regular-sequence they form a regular sequence,
   so def-weil-pbc-depth gives depth R ≥ 2. Apply new-local-dual-depth-two to N from
   step 2. Its dual, identified with M by step 3, has depth at least two; linear
   isomorphisms preserve the regular sequences defining depth. If M is zero it is
   free of rank zero. Otherwise lem-weil-pbc-depth-le-support-dimension bounds its
   depth by dim Supp M ≤ dim R = 2. Thus its depth is two, and
   lem-weil-pbc-regular-local-mcm-free makes it finite free.
8. All stalks are finite free, so lem-sc-coherent-free-stalks-locally-free applies
   to coherent F on locally Noetherian X. Together with step 4 this gives the
   equivalence. For empty X the stalk condition is vacuous and the empty cover works.
-/
theorem isIso_bidual_iff_isFiniteLocallyFree_of_isRegularScheme
    (X : Scheme.{u}) (hX : IsRegularScheme X)
    (hdim : topologicalKrullDim X ≤ 2) (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    IsIso (SheafOfModules.bidual (R := X.sheaf) F) ↔
      SheafOfModules.IsFiniteLocallyFree F := by
  sorry

end AlgebraicGeometry.Scheme.Modules
