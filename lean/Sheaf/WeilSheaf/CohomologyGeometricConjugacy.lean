/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.WeilSheaf.CohomologyGeometricEquivalence
import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.Paper.ConstantWeilStructure
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.SixFunctors.FrobeniusCohomologyTransport
import Sheaf.Paper.GlobalGeometricFrobenius

/-!
# Cohomology and conjugate geometric Frobenius automorphisms

Source: the transport-of-structure part of the base-change clause of
`sec-poincare-duality/sk-thm-poincare-duality/thm-weil-poincare-duality.md`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

/-- An isomorphism of geometric fibers conjugating one geometric Frobenius to a power
of the other makes the explicit cohomology equivalence intertwine those operators.

Source: literature/blueprint/master/blueprint/sec-poincare-duality/
sk-thm-poincare-duality/thm-weil-poincare-duality.md, base-change clause,
with the transport convention of `def-weil-global-geometric-frobenius`.
(blueprint: lem-pod-cohomology-geometric-conjugacy)

Proof: Pushforward along e is an exact equivalence of the categories of modules over the
continuous coefficient sheaves. Its canonical isomorphism on constant sheaves identifies
the constant object on Ybar with that on Xbar. The canonical isomorphism on global sections
identifies their derived global-section complexes, since an exact equivalence preserves
injective resolutions. The equation he identifies the natural transport by the Frobenius
of Ybar with transport by the r-th power on Xbar: apply composition of pushforwards to
he, and use the composition law for the constant-sheaf and global-section isomorphisms.
The former is `adicConstantSheafToLowerStar_comp`, after forgetting module linearity;
the latter is `globalSectionsLowerStarIso_comp`, together with naturality.
The definition of Weil cohomology as global sections of the homology sheaf of the derived
pushforward to the geometric point agrees with homology of derived global sections:
global sections at an algebraically closed point are exact.
The linear equivalence is the construction
`cohomologyLinearEquivOfGeometricFiberIso`. Naturality of homology carries the transport
identity through its composition isomorphisms to the asserted identity. More explicitly,
the comparison maps are characterized by their equations with the units of right derived
functors. To prove their compatibility, apply `Functor.rightDerived_ext` and these unit
equations, reducing to the preceding identity of maps on complexes. The
r-fold composite of the cohomological Frobenius is its r-th power as a linear endomorphism.
No choice of an embedding between the two base fields is needed for this transport step. -/
theorem cohomologyLinearEquivOfGeometricFiberIso_map_frobenius
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (r : ℕ) (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber)
    (he : (Y ↘ Spec (.of k')).geometricGaloisFrobenius.hom ≫ e.hom =
      e.hom ≫ ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ r).hom) (i : ℤ)
    (x : ((adicConstant k' l Y).cohomology i).carrier) :
    cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i
        (((adicConstant k' l Y).cohomology i).frobenius x) =
      (((adicConstant k l X).cohomology i).frobeniusEnd ^ r)
        (cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i x) := by
  sorry

end AlgebraicGeometry.WeilSheaf
