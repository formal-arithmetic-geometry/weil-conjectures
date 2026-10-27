/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.AlgebraicGeometry.PerfectGeneratorExists
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.AlgebraicGeometry.KoszulRestrictionZero
import WeilConjectures.AlgebraicGeometry.KoszulOpenOrthogonality

/-! # A single perfect weak generator for an algebraic space

Source: Stacks Project, Derived Categories of Spaces, Tag 09IY,
`theorem-bondal-van-den-Bergh` (blueprint: lem-sfb-space-perfect-weak-generator).

The derived module category is formed on the recorded small affine etale model,
which is equivalent to the original small etale ringed topos. Quasi-coherent
cohomology is tested after transport back along its module equivalence. Perfectness
uses the recorded local bounded finite-free-retract representatives. Absolute
quasi-separatedness is expressed by the existing affine-test criterion of Tag 0AHR.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A qcqs algebraic space admits a perfect object detecting zero by shifted Hom groups.
Source: Stacks Project, Derived Categories of Spaces, Tag 09IY,
`theorem-bondal-van-den-Bergh` (blueprint: lem-sfb-space-perfect-weak-generator).

Proof:
1. Use lem-sfb-space-qcqs-distinguished-square-induction for the isomorphism-invariant
   existence of a perfect weak generator. All vertices of its elementary squares are
   qcqs; in particular their overlaps are quasi-compact.
2. In the affine case use lem-pc-perfect-generator-exists. The shifted-target convention
   of def-pc-generators agrees with the displayed shifted-source criterion by replacing
   n with -n. Transfer along lem-sfb-derived-etale-zariski-equivalence; shifted Hom groups
   and zero objects are preserved, and lem-sfb-etale-detects-perfect preserves perfection.
   This includes the empty affine scheme.
3. For an elementary square U -> Y <- V with V = Spec A, choose the generator P on U.
   By lem-sfb-space-perfect-open-retract it is a retract of Q restricted to U for a
   perfect Q on Y. Choose a finite principal-open cover of W = U times_Y V. The finite
   Koszul complex K for its defining elements is perfect and vanishes on W, by
   lem-pc-koszul-restriction-zero and the derived etale/Zariski comparison.
4. By lem-sfb-space-supported-etale-excision, K' = Rf_* K agrees with f_! K and restricts
   to K on V and to zero on U. It is perfect by the local definition on the cover U,V.
   Then G = Q direct-sum K' is perfect, by taking finite sums of its local bounded
   finite-projective representatives. By lem-sfb-space-perfect-objects-compact it has
   quasi-coherent cohomology. Orthogonality to all shifts of G implies orthogonality
   to Q and K'. Excision identifies the latter with orthogonality to K on V.
5. By lem-sfb-space-derived-etale-chart-calculus, E restricted to V has quasi-coherent
   cohomology. Transfer lem-pc-perfect-generation-koszul-orthogonal across
   lem-sfb-derived-etale-zariski-equivalence. It identifies the canonical unit on V
   with an isomorphism E|_V -> Rh_*(E|_W), where h : W -> V is the open immersion.
6. For j : U -> Y, consider the canonical unit E -> Rj_*j^*E. On U it is the identity;
   on V etale base change in lem-sfb-space-derived-etale-chart-calculus identifies it
   with the unit of step 5, including its normalization. Its cone has zero cohomology
   on the cover U,V, hence globally by the sheaf axiom. Thus E is isomorphic to
   Rj_*(E|_U), supplying the detail omitted by Tag 09IY.
7. Open adjunction identifies Hom(Q[n], E) with Hom(Q|_U[n], E|_U). The retract maps
   i : P -> Q|_U and r : Q|_U -> P with i followed by r equal to the identity show
   every map P[n] -> E|_U is zero. The generator on U gives E|_U = 0, hence E = 0.
   Conversely, every map to a zero object is zero. This completes the induction.

Restriction to the small affine ringed model preserves cohomology, shifts, zero
objects, and the local bounded finite-free-retract condition, so the statement is
about the same objects as on the original small etale site. -/
theorem exists_perfect_weak_generator
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X) :
    ∃ P : X.DerivedQCoh,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        X.smallStructureSheaf P.obj ∧
      ∀ E : X.DerivedQCoh, IsZero E.obj ↔
        ∀ n : ℤ, Subsingleton (P.obj⟦n⟧ ⟶ E.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
