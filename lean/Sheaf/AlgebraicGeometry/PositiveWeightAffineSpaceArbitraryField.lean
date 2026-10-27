/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import Mathlib.RingTheory.Filtration

/-! # Affine space from strictly positive tangent weights over an arbitrary field

Source: Milne, Algebraic Groups (2017), Definition 13.40 and Theorem 13.41,
printed pp.269--270 (blueprint: lem-sfb-positive-weight-affine-space-arbitrary-field).

The weight equation is tested over the universal Laurent algebra of the residue field.
It concerns algebraic characters, including characters divisible by the characteristic.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- The universal Laurent parameter, viewed as a unit in the dual-number algebra.
Source: Milne, Definition 13.40, p.269
(blueprint: lem-sfb-positive-weight-affine-space-arbitrary-field). -/
def tangentLaurentUnit (K : Type u) [Field K] : (DualNumber (LaurentPolynomial K))ˣ :=
  Units.map (TrivSqZeroExt.inlHom (LaurentPolynomial K) (LaurentPolynomial K)).toMonoidHom
    (unitOfInvertible (LaurentPolynomial.T 1))

/-- The positive character equation on a tangent vector, evaluated at the universal unit.
The two projections uniquely specify the map to G_m times X: the first is the universal
parameter and the second is the scalar extension of the given dual-number tangent vector.
The output is that same vector with epsilon multiplied by z^n. This is differentiation
in the X direction only; the character z^n is never differentiated.
Source: Milne, Definition 13.40 and Theorem 13.41, pp.269--270
(blueprint: lem-sfb-positive-weight-affine-space-arbitrary-field). -/
def IsPositiveTangentCharacter
    (k : Type u) [Field k] (X : Over (Spec (.of k)))
    (a : ModObj (StandardGroupSchemes.multiplicative k) X) (x : X.left)
    (v : schemeTangentSpace k X.left X.hom x) (n : ℤ) : Prop :=
  0 < n ∧
    ∃ q : Spec (.of (DualNumber (LaurentPolynomial (X.left.residueField x)))) ⟶
        ((StandardGroupSchemes.multiplicative k) ⊗ X).left,
      q ≫ (fst (StandardGroupSchemes.multiplicative k) X).left =
        Spec.map (CommRingCat.ofHom
          (LaurentPolynomial.eval₂
            ((TrivSqZeroExt.inlHom _ _).comp
              (LaurentPolynomial.C.comp
                (StructureSheaf.toStalk k (X.hom x) ≫ X.hom.stalkMap x ≫
                  X.left.residue x).hom))
            (tangentLaurentUnit (X.left.residueField x)))) ∧
      q ≫ (snd (StandardGroupSchemes.multiplicative k) X).left =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
          (LaurentPolynomial.C : X.left.residueField x →+*
            LaurentPolynomial (X.left.residueField x)))) ≫ v.val ∧
      q ≫ a.smul.left =
        Spec.map (CommRingCat.ofHom
          ((TrivSqZeroExt.map
            ((LaurentPolynomial.T n : LaurentPolynomial (X.left.residueField x)) •
              (LinearMap.id : LaurentPolynomial (X.left.residueField x) →ₗ[
                LaurentPolynomial (X.left.residueField x)]
                LaurentPolynomial (X.left.residueField x)))).toRingHom.comp
            (DualNumber.mapRingHom
              (LaurentPolynomial.C : X.left.residueField x →+*
                LaurentPolynomial (X.left.residueField x))))) ≫ v.val

/-- A smooth geometrically connected affine finite-type scheme with a rational fixed point
and strictly positive tangent characters is affine space over its original field, with that
point as origin. The finite tangent basis may be empty. The residue field at a rational
point is canonically the base field, so the basis size d is dim_k T_x X.
Source: Milne, Definition 13.40 and Theorem 13.41, printed pp.269--270
(blueprint: lem-sfb-positive-weight-affine-space-arbitrary-field).

Proof plan:
1. By lem-pc-affine-finite-type-algebra and
   lem-weil-pbc-smooth-scheme-over-field-regular the coordinate algebra A is finite type
   and X is regular. Geometric connectedness and the point give connected nonemptiness;
   lem-sc-regular-connected-integral makes A a domain. The stalk is A_m by
   lem-weil-pbc-spec-map-stalk-localization, and is regular local with residue field k.
2. Apply lem-sfb-gm-affine-action-grading. Universal fixedness and uniqueness of Laurent
   coefficients make m homogeneous and put every nonzero weight into m, over finite k too.
3. Localization gives m/m^2 = mA_m/(mA_m)^2: for s outside m, replace 1/s modulo m by
   1/epsilon(s). This proves surjectivity, and clearing denominators proves injectivity.
   Finite algebra generators, after subtracting their values at x, span m/m^2.
4. By lem-sc-rational-tangent-cotangent-duality the tangent operator is the transpose
   of function pullback, without an inverse. The universal Laurent equation gives the
   same positive weights on m/m^2. Take homogeneous lifts of its eigenbasis.
5. Apply lem-weil-pbc-krull-intersection-jacobson in A_m. Since A is a domain, A embeds
   in A_m, hence the intersection of the powers of m in A is zero.
6. Products of j cotangent basis elements span m^j/m^(j+1). Their weights are positive.
   A homogeneous element of m of nonpositive weight therefore lies in every m^j and
   vanishes by step 5. Thus A_0 = k and all negative graded pieces vanish. This also
   works with the empty basis.
7. Apply lem-sfb-positive-graded-regular-polynomial to conclude k[T_1,...,T_d] = A.
   Taking spectra gives the asserted k-isomorphism, and the lifts lie in m, so x maps
   to the origin. For d = 0 this is Spec k. All constructions were over k. -/
theorem positive_weight_affine_space_arbitrary_field
    (k : Type u) [Field k] (X : Over (Spec (.of k))) [IsAffine X.left]
    [Smooth X.hom] [GeometricallyConnected X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (a : ModObj (StandardGroupSchemes.multiplicative k) X)
    (s : Over.mk (𝟙 (Spec (.of k))) ⟶ X)
    (hs : ∀ (W : Over (Spec (.of k)))
      (t : W ⟶ StandardGroupSchemes.multiplicative k),
      lift t (Over.homMk W.hom ≫ s) ≫ a.smul = Over.homMk W.hom ≫ s)
    (d : ℕ)
    (b : Module.Basis (Fin d) (X.left.residueField (s.left (IsLocalRing.closedPoint k)))
      (schemeTangentSpace k X.left X.hom (s.left (IsLocalRing.closedPoint k))))
    (n : Fin d → ℤ)
    (hn : ∀ i : Fin d,
      IsPositiveTangentCharacter k X a (s.left (IsLocalRing.closedPoint k)) (b i) (n i)) :
    ∃ e : X.left ≅ AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)),
      e.hom ≫ (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)) ↘ Spec (.of k)) = X.hom ∧
      s.left ≫ e.hom = AffineSpace.homOfVector (𝟙 (Spec (.of k))) (fun _ ↦ 0) := by
  sorry

end AlgebraicGeometry
