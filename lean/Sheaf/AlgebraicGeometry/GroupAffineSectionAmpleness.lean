/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.NormalGroupSquarePower
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Ampleness from one affine section locus on a smooth group

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Proposition 5.9,
final assertion, and Corollaries 6.5 and 6.6(ii), printed pp.13--16;
Raynaud, Faisceaux amples sur les schemas en groupes, VI, Theorem 2.1.
(blueprint: lem-sfb-group-affine-section-ampleness).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A line on a smooth separated finitely presented group with connected fibres over
an affine locally Noetherian normal base is absolutely ample if a supplied section of a
positive tensor power has affine nonvanishing locus meeting every fibre. `U` is precisely
that locus, as specified by `hU`. The group need not be commutative or proper, and the line
has no symmetry or rigidification hypothesis. Finite presentation is written as local
finite presentation and quasi-compactness; separatedness implies quasi-separatedness.

Source: Guo, Proposition 5.9 and Corollaries 6.5 and 6.6(ii), printed pp.13--16;
Raynaud, VI, Theorem 2.1 (blueprint: lem-sfb-group-affine-section-ampleness).

Proof:
1. Finite presentation gives quasi-compactness and quasi-separatedness. Apply
   lem-sfb-normal-group-square-power to obtain r >= 1 such that A = L.tensorPow r
   satisfies the square condition for left multiplication.
2. Tensor sigma with itself r times and reassociate to a section v of A.tensorPow n.
   In a local frame its coefficient is f^r when sigma has coefficient f. A residue-field
   value f^r is nonzero exactly when f is nonzero. Thus its nonvanishing locus is U,
   which is affine and surjective over T by hmeets.
3. By lem-weil-pbc-surjective-base-change, the projection G times_T U to G is surjective.
   The automorphism (g,u) -> (gu,u), with inverse (x,u) -> (xu^{-1},u), identifies the
   multiplication map with the automorphism followed by the projection. Hence the
   multiplication image is all of G. The union of affine positive-power section loci
   of A contains U, so its multiplication image is likewise all of G.
4. Apply lem-sfb-square-action-affine-orbit-criterion to the left action of G on itself.
   It proves A ample. Each affine section locus witnessing ampleness of A comes from
   a positive power of L, by reassociation of tensor factors, with the same residue
   values. Quasi-compactness and these loci give IsAmple G.left L by
   def-weil-pbc-ample-invertible-module. -/
theorem isAmple_of_group_affine_section
    (T : Scheme.{u}) [IsAffine T] [IsLocallyNoetherian T]
    (hT : ∀ t : T, IsDomain (T.presheaf.stalk t) ∧
      IsIntegrallyClosed (T.presheaf.stalk t))
    (G : Over T) [GrpObj G] [Smooth G.hom] [IsSeparated G.hom]
    [LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom]
    (hconnected : ∀ t : T, ConnectedSpace (G.hom.fiber t))
    (L : G.left.Modules) [L.IsInvertible] (n : ℕ) (hn : 1 ≤ n)
    (sigma : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤))
    (U : G.left.Opens) (hU : (U : Set G.left) = nonvanishingLocus (L.tensorPow n) sigma)
    (haffine : IsAffineOpen U)
    (hmeets : ∀ t : T, ∃ x : G.left, x ∈ U ∧ G.hom x = t) :
    IsAmple G.left L := by
  sorry

end AlgebraicGeometry.Scheme.Modules
