/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Reduced
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier

import Sheaf.AlgebraicGeometry.AbelianVariety.ClosedSubgroupReducedComponent
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.ProductIrreducibleComponentsBijection
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible

/-! # Closed translation stabilizers and effective divisors

Source: Milne, Algebraic Groups (2017), Proposition 1.79 and Corollaries 1.80-1.81,
printed pp. 30-31. The Cartier-divisor consequence is the agent-supplied supporting
argument for the converse of Milne, Abelian Varieties, I Proposition 8.1.
(blueprint: lem-sfb-closed-translation-stabilizer)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A closed subscheme of an abelian variety has a closed translation stabilizer,
with its universal property after every base change. The reduced identity component
of the stabilizer of an effective divisor's reduced support preserves the divisor.

Source: Milne, Algebraic Groups (2017), Proposition 1.79 and Corollaries 1.80-1.81,
printed pp. 30-31; agent-supplied Cartier-divisor argument supporting Milne AV I 8.1.
(blueprint: lem-sfb-closed-translation-stabilizer)

The product in `Over (Spec k)` is the scheme fibre product. The morphism
`fst A T * (snd A T ≫ a)` sends `(x,t)` to `x + a(t)`. Thus equality of its
pullback ideal with the projection pullback is exactly scheme-theoretic translation
invariance, including on nonreduced test schemes. The second conjunct is the same
universal property for `H × S → A × S`: a point over S is a pair `(a,s)`.
The open U of H_red is specified by the inverse image of the identity component
of H; reduction is a homeomorphism, so U has exactly the structure of `(H_red)^0`.

Proof:
1. Apply lem-sfb-constant-source-closed-factorization-locus to `(z,a) ↦ z+a` on
   Z times A. Z is separated finite type, being closed in the proper variety A.
   This constructs the closed locus P of translations taking Z into Z, without
   assuming that Z is reduced.
2. Intersect P with its inverse image under inversion. Both containments give
   equality of closed subschemes. The translation identities make this a subgroup
   on every test scheme, giving def-sc-group-scheme-subgroup. The same functor on
   S-schemes is represented by H times S, with unique lifts over the chosen S-point.
3. For Z the reduced support of F, use
   lem-sfb-abelian-closed-subgroup-reduced-component to obtain C = (H_red)^0.
   By lem-sc-abelian-variety-characterization A and C are geometrically integral;
   lem-trf-smooth-geometrically-normal makes A normal in every characteristic.
4. For each irreducible support component D, the product C times D is irreducible
   by lem-sc-product-irreducible-components-bijection. Its action image lies in Z
   and its closure contains D via the identity slice. Maximality of D makes this
   closure D. Using also inverse translations, every c in C(k) fixes D.
5. At each codimension-one support point translation induces an isomorphism of DVRs,
   preserving the order of a local equation of F. At other height-one points both
   equations are units. On a normal integral affine neighbourhood, apply
   lem-trf-normal-domain-principal-divisor-kernel: the quotient of the two equations
   has zero divisor, hence is a unit. Therefore t_c^*F = F as closed subschemes.
6. Repeat steps 1-2 for F itself, obtaining its closed scheme stabilizer K.
   The closed subscheme K times_A C of C contains every k-rational point of C.
7. By lem-pc-rational-points-dense those points are dense. The defining ideal of
   K times_A C on each reduced affine open of C lies in every prime, hence is zero.
   Thus C factors through K as schemes, not merely on rational points.
8. Evaluate this factorization at the universal C-point. The shear
   (x,c) ↦ (x+c,c) preserves F times C, so the action and projection pullbacks
   have identical ideal sheaves. The projection is flat and the shear is an
   isomorphism; lem-pc-flat-pullback-effective-cartier-ideal makes these pullbacks
   effective Cartier divisors. This identity persists on nonreduced test schemes.
-/
theorem exists_closed_translation_stabilizer
    (k : Type u) [Field k] [IsAlgClosed k]
    (A Z : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (z : Z ⟶ A) [IsClosedImmersion z.left] :
    ∃ (H : Over (Spec (.of k))) (_ : GrpObj H) (i : H ⟶ A),
      IsClosedSubgroupScheme i ∧
      (∀ (T : Over (Spec (.of k))) (a : T ⟶ A),
        (∃! b : T ⟶ H, b ≫ i = a) ↔
          z.left.ker.comap ((fst A T * (snd A T ≫ a)).left) =
            z.left.ker.comap (fst A T).left) ∧
      (∀ (S T : Over (Spec (.of k))) (s : T ⟶ S) (a : T ⟶ A),
        (∃! b : T ⟶ H ⊗ S, b ≫ fst H S ≫ i = a ∧ b ≫ snd H S = s) ↔
          z.left.ker.comap ((fst A T * (snd A T ≫ a)).left) =
            z.left.ker.comap (fst A T).left) ∧
      (∀ (F : A.left.IdealSheafData), F.IsInvertible → z.left.ker = F.radical →
        ∃ U : (GrpObj.reduced H).left.Opens,
          (U : Set (GrpObj.reduced H).left) =
            (GrpObj.reducedι H).left ⁻¹' connectedComponent (GrpObj.onePoint H) ∧
          F.comap
              ((fst A (Over.mk (U.ι ≫ (GrpObj.reduced H).hom)) *
                (snd A (Over.mk (U.ι ≫ (GrpObj.reduced H).hom)) ≫
                  Over.homMk U.ι ≫ GrpObj.reducedι H ≫ i)).left) =
            F.comap (fst A (Over.mk (U.ι ≫ (GrpObj.reduced H).hom))).left) := by
  sorry

end AlgebraicGeometry
