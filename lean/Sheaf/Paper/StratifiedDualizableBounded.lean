/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Constructible
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality
import Sheaf.AlgebraicGeometry.ProEtale.SingleWContractibleCover
import Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits

/-! # Boundedness from stratified dualizability

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Definition 3.3,
Lemma 4.10 and Corollary 4.11 (blueprint: lem-pod-stratified-dualizable-bounded).

The category is the ordinary unbounded derived category of module objects over the
pulled-back condensed ring, with its ordinary relative derived tensor. The explicit
exact pairings specify the two duality contractions on each stratum. No Noetherian,
finite-dimensional or regularity assumption is made.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A complex dualizable on finitely many constructible locally closed strata of a qcqs
scheme has bounded cohomology, and admits a representative vanishing below the same bound.
Source: Hemo--Richarz--Scholbach, Definition 3.3, Lemma 4.10 and Corollary 4.11
(blueprint: lem-pod-stratified-dualizable-bounded).

Proof:
1. Apply lem-fix-constructible-open-closed-refinement to refine the partition to a finite
open/closed tree with qcqs vertices and actual maps from its nonempty leaves to strata.
Pull back each dual pair along these maps using lem-zl-condensed-lisse-proetale-locality.
Empty leaves have the zero module category.
2. For each nonempty leaf T, det-pe-hypercover-single-cover supplies a single w-contractible
cover W = Spec D. Pullback preserves its dual pair. By
lem-zl-condensed-wcontractible-lisse-evaluation the restriction to W is the scalar realization
of a bounded finite-projective complex P over A = Γ(W, B). Choose its term bounds [a_T,b_T],
using [0,0] for a zero complex.
3. Each finite projective term is a retract of a finite free A-module: finite generation
gives a finite free surjection, and projectivity splits it. Scalar realization is exact,
additive and monoidal, so its image is a retract of a finite sum of B[0]. Its cohomology
outside degree zero is therefore a retract of zero and vanishes.
4. The brutal tails of P have degreewise split short exact sequences with quotients
P^r[0][-r]. Apply lem-weil-pbc-complex-ses-triangle and exact scalar realization, then use
lem-sf-derived-homology-long-exact. Descending induction from the zero tail above b_T
bounds the realized tail starting in degree r by [r,b_T], hence bounds K_W by [a_T,b_T].
This does not require scalar realization to be t-exact on arbitrary complexes.
5. The coefficient isomorphism of sk-def-sfb-coefficient-morphisms identifies restriction
with exact geometric module inverse image (lem-trf-geometric-inverse-image-exact).
By lem-weil-pbc-exact-functor-complex-cohomology it commutes with cohomology. Apply
lem-zl-condensed-cover-restriction-conservative to each cohomology sheaf placed in degree
zero to descend the bounds from W to T.
6. Take the minimum of the finitely many a_T and maximum of the b_T; if no leaf is nonempty,
use a = b = 0. For a degree outside these bounds, cohomology vanishes on all leaves.
Induct up the tree using lem-exc-open-closed-detection and exactness of restriction to
show it vanishes at the root. This includes the empty scheme.
7. Choose any cochain representative E of K and take its good lower truncation at a
(def-kun-truncations): zero below a, coker(d^(a-1)) in degree a, and E above a. The quotient
E → C is a quasi-isomorphism since H^j(E) vanishes below a; in degree a and above its
cohomology is unchanged. Thus Q(C) is isomorphic to K and C vanishes below a. -/
theorem stratified_dualizable_bounded
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)))
    (S : Scheme.FiniteLocallyClosedStratification Y)
    (hconstructible : ∀ i : Fin S.n, Topology.IsConstructible (S.stratum i))
    (hdual : ∀ i : Fin S.n, ∃ D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (S.domain i)) Ab.{u + 1})
        (condensedRingObj Λ.X (S.domain i))),
      Nonempty (ExactPairing
        ((CondensedRing.upperStar Λ.X (S.immersion i)).mapDerivedCategory.obj K) D)) :
    ∃ a b : ℤ, a ≤ b ∧
      (∀ j : ℤ, j < a ∨ b < j →
        IsZero ((DerivedCategory.homologyFunctor _ j).obj K)) ∧
      ∃ C : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)) ℤ,
        Nonempty (DerivedCategory.Q.obj C ≅ K) ∧
          ∀ j : ℤ, j < a → IsZero (C.X j) := by
  sorry

end AlgebraicGeometry.ProEtale
