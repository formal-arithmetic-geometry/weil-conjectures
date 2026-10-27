/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleFpDirectedApproximation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Finite algebra approximation with surjective transitions

Source: Stacks Project, Limits of Spaces, Tag 086Z,
lemma-finite-algebra-directed-colimit-finite-finitely-presented
(blueprint: lem-sfb-space-finite-algebra-surjective-fp-colimit).

The colimit is in the existing full category of quasi-coherent commutative algebra sheaves.
Finiteness and algebra finite presentation are tested on affine etale chart sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite quasi-coherent algebra on a qcqs algebraic space is a directed colimit of
finite, finitely presented algebras with surjective maps on affine etale chart sections.
Source: Stacks Project, Limits of Spaces, Tag 086Z,
lemma-finite-algebra-directed-colimit-finite-finitely-presented
(blueprint: lem-sfb-space-finite-algebra-surjective-fp-colimit).

Proof:
1. Choose a finite affine etale covering using lem-a1-space-affine-etale-cover and
   lem-a1-space-finite-affine-subatlas. Apply
   lem-sfb-space-module-fp-directed-approximation to the underlying module of A.
   By lem-sfb-space-qcoh-affine-chart-calculus, affine sections compute this colimit.
   Lift finite generating lists on the finitely many covering charts to one common
   stage F. Its map to A is surjective on those charts, hence as a sheaf map; its
   quasi-coherent cokernel vanishes, giving surjectivity on every affine chart.
2. Form D = Sym(F). The map F to A extends to a surjective algebra map D to A.
   Affine-chart calculus identifies its quasi-coherent kernel ideal J and D/J with A,
   including the quotient universal property.
3. Let K be the directed poset of finite-type quasi-coherent submodules E of J.
   It contains zero and has upper bounds given by sums. It is small within the chosen
   size bound: submodules are families of subsets of section sets on the fixed site.
   Module approximation of J and affine-chart calculus show that images of its finite
   presentation stages belong to K and exhaust J on every affine chart.
4. Put Q_i = D/(E_i), where (E_i) is the generated ideal. Affine-chart calculus makes
   these quasi-coherent. By lem-weil-pbc-symmetric-algebra-finite-presentation, they
   are finitely presented as algebras: F is finitely presented and E_i has finite
   module generators. Inclusion of ideals gives surjective transitions with the
   identity, composition and compatibility laws of quotient maps.
5. On every affine chart, the ideals (E_i) have union J. A compatible family of maps
   from D/(E_i) gives one map from D killing J, hence factors uniquely through A.
   Affine-chart calculus promotes this to the algebra-sheaf colimit universal property,
   and thus to its full subcategory of quasi-coherent algebras.
6. Choose finite generators of F on the finite covering charts. By
   lem-weil-pbc-finite-algebra-is-integral, their images in A satisfy monic polynomials.
   Their finitely many polynomial relations lie in E_i for one common index i_0.
   All Q_i with i at least i_0 satisfy these same monic relations.
7. Bounded monomials in the generators span those Q_i on each covering chart, so
   they are finite modules there. A degree-zero monic relation gives the zero algebra;
   with no generators the unit alone spans. Affine-chart calculus gives finiteness
   on every affine chart. For the empty space, all chart section modules are zero.
8. Restrict K to its nonempty directed tail above i_0. Every stage is now finite and
   finitely presented. The tail still has colimit A: extend a compatible tail family
   to k in K by choosing an upper bound of k and i_0 and composing to that stage.
   Common upper bounds give independence and compatibility, so step 5 applies. -/
theorem exists_finite_finitePresentation_surjective_colimit
    {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [CompactSpace (Point Y.obj.obj)] (hqs : IsAbsolutelyQuasiSeparated Y)
    (A : Y.QCAlg) (hA : A.obj.IsFinite) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ Y.QCAlg),
      (∀ i : I, (D.obj i).obj.IsFinite ∧ (D.obj i).obj.IsFinitePresentation) ∧
      (∀ (i j : I) (h : i ≤ j) (U : Y.EtaleSite),
        IsAffine (Y.etaleForget.obj U) →
          Function.Surjective ((D.map (homOfLE h)).hom.right.hom.app (op U))) ∧
      ∃ ι : D ⟶ (Functor.const I).obj A,
        Nonempty (IsColimit (Cocone.mk A ι)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
