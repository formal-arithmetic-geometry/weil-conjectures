/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Topology.Connected.Basic

import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Sheaf.AlgebraicGeometry.RationalMapExtensionValuationPoint
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Rational fixed points for split solvable groups

Source: Milne, Algebraic Groups (2017), Theorem 16.51, printed p.343.
(blueprint: lem-sfb-split-solvable-rational-fixed-point)

The internal module object is a scheme action with its unit and associativity morphism
identities. Fixedness is tested on all commutative k-algebras, including nonreduced ones.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- A split solvable group acting on a proper finite-type scheme with a rational point
has a rational point fixed scheme-theoretically. The scalar extension of `x` to `A` is
`toUnit ((algSpec (.of k)).obj (.op (CommAlgCat.of k A))) ≫ x`, where
`(algSpec (.of k)).obj (.op (CommAlgCat.of k A))` is Spec A with its k-structure.
The action on points is induced by the scheme morphism `ModObj.smul`; its laws are
the morphism identities in `ModObj`.

Source: Milne, Algebraic Groups (2017), Theorem 16.51, printed p.343; fixed subschemes
in Theorem 7.1, printed pp.138--139.
(blueprint: lem-sfb-split-solvable-rational-fixed-point)

Proof, following the eight steps of the node:
1. For G_a acting on a proper Z with y in Z(k), set L = Spec k[s] and U = D(s).
   The polynomial-domain and spectrum-stalk lemmas make L integral, with dense U and
   complement the rational point o = (s). Finite type over a field makes L Noetherian
   by lem-weil-pbc-finite-type-over-noetherian. Its stalk at o is k[s]_(s), a valuation
   ring: write a nonzero rational function as s^n p/q with p(0)q(0) nonzero. The
   function lies in the stalk for n nonnegative, and its inverse does otherwise.
   On U use the additive orbit map f(s) = a(s^(-1),y), in the coordinates of def-sc-gm-ga.
2. By lem-sfb-rational-map-extension-valuation-point, f extends over a neighbourhood
   of o. Together with U this is all of L. Set z = F(o), a rational point of Z.
3. On V = Spec k[u,s,(1+us)^(-1)], compare a(u,F(s)) with F(s/(1+us)). They agree
   on D(s) by the additive action identity, since (s/(1+us))^(-1) = u+s^(-1).
   The affine-spectrum and principal-open localization descriptions give these
   morphisms. The polynomial-domain and spectrum-stalk lemmas make V reduced and
   D(s) dense. Z is separated by properness, so
   lem-sfb-relative-separated-dominant-ext makes them equal on V. Restrict along
   s = 0 to obtain a(u,z) = z as morphisms, hence after every algebra extension.
4. For G_m apply lem-sfb-split-torus-rational-fixed-point in rank one. This and
   steps 1--3 cover both possible quotient factors; transport along their given
   group-scheme isomorphisms.
5. Induct on the length of the series in def-sfb-split-solvable-right-torsors.
   At length zero the group is trivial and every rational point is fixed. Otherwise
   N = H_1 has the shorter split series. It is smooth and connected by that series,
   and affine of finite type as a closed subgroup of H: its coordinate algebra is
   a quotient of the finitely generated coordinate algebra of H, by the closed
   immersion and finite-type definitions. Induction gives an N-fixed rational y.
6. Apply lem-sfb-universal-fixed-subscheme to the N-action to obtain the closed
   subscheme j : Y = X^N → X. N is separated since it is affine: its diagonal comes
   from the surjection k[N] tensor k[N] → k[N]. X is separated by properness.
   Representability puts y in Y(k). By lem-weil-pbc-closed-immersion-proper, Y is
   proper, hence finite type and separated. No reduction of X or Y is taken.
7. The represented fppf quotient q : H → Q has kernel N and Q is G_a or G_m.
   By lem-sfb-normal-fixed-subscheme-quotient-action, Q acts on Y compatibly with
   q and j. Steps 1--4 give a Q-fixed rational point z of the proper Y.
8. Set x = j(z). For every k-algebra A and h in H(A), compatibility gives
   a_A(h,x_A) = j_A(b_A(q_A(h),z_A)) = j_A(z_A) = x_A. This finishes induction.
   Only normality in each predecessor is used; finite or imperfect fields and
   nonreduced or disconnected targets are all included.
-/
theorem exists_rational_fixed_point_of_isSplitSolvable
    {k : Type u} [Field k] (H : Grp (Over (Spec (.of k))))
    [Smooth H.X.hom] [ConnectedSpace H.X.left] [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (hsplit : IsSplitSolvable H)
    (X : Over (Spec (.of k))) [IsProper X.hom] [ModObj H.X X]
    (hX : Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ X)) :
    ∃ x : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (h : (algSpec (.of k)).obj (.op (CommAlgCat.of k A)) ⟶ H.X),
        h • (toUnit ((algSpec (.of k)).obj (.op (CommAlgCat.of k A))) ≫ x) =
          toUnit ((algSpec (.of k)).obj (.op (CommAlgCat.of k A))) ≫ x := by
  sorry

end AlgebraicGeometry
