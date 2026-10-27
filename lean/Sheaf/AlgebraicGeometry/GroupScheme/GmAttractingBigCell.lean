/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
public import Mathlib.Algebra.DualNumber
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
import Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.Properties

/-! # Attracting subgroups and the zero-fixed-tangent big cell

Source: Milne, Algebraic Groups (2017), Definitions 13.29--13.30 and
Theorem 13.33(a)--(e), pp.264--266, applied to H semidirect G_m
(blueprint: lem-sfb-gm-action-attracting-subgroup-big-cell).

All algebra-valued points, orbit extensions, and character tests retain nonreduced
algebras. The Lie module is the existing identity tangent module `GrpObj.Lie`.
The suprema below are the subspaces underlying the indicated sums of character spaces.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.GmAttractingBigCell

variable {k : Type u} [Field k]

/-- The G_m point associated to a unit, by the Laurent algebra universal property.
Source: Milne, Definition 13.29, p.264
(blueprint: lem-sfb-gm-action-attracting-subgroup-big-cell). -/
def gmPoint (R : Type u) [CommRing R] [Algebra k R] (z : Rˣ) :
    points (StandardGroupSchemes.multiplicative k) R :=
  StandardGroupSchemes.map k
    (AddMonoidAlgebra.lift k R ℤ ((Units.coeHom R).comp (zpowersHom Rˣ z)))

/-- The orbit extends over Spec R[t] and takes zero to the identity.
The sign is 1 for U_+ and -1 for U_-. Equality over the Laurent algebra is
restriction to the actual punctured affine line, at its universal unit.
Source: Milne, Definition 13.29, p.264
(blueprint: lem-sfb-gm-action-attracting-subgroup-big-cell). -/
def IsAttracting (H : Grp (Over (Spec (.of k))))
    [ModObj (StandardGroupSchemes.multiplicative k) H.X]
    (sign : ℤ) (R : Type u) [CommRing R] [Algebra k R] (h : points H.X R) : Prop :=
  ∃ f : points H.X (Polynomial R),
    points.map H.X
        ((Polynomial.toLaurentAlg : Polynomial R →ₐ[R] LaurentPolynomial R).restrictScalars k) f =
      gmPoint (k := k) (LaurentPolynomial R)
          ((unitOfInvertible (LaurentPolynomial.T 1)) ^ sign) •
        points.map H.X (IsScalarTower.toAlgHom k R (LaurentPolynomial R)) h ∧
    points.map H.X ((Polynomial.aeval (0 : R)).restrictScalars k) f = 1

/-- The algebraic weight-j space, testing the action on each scalar-extended tangent
point against the dual-number substitution epsilon to z^j epsilon. Taking the span
bundles the linear eigenspace; the tested set is already closed under linear operations.
Source: Milne, Theorem 13.33(c), pp.265--266
(blueprint: lem-sfb-gm-action-attracting-subgroup-big-cell). -/
def weightSpace (H : Grp (Over (Spec (.of k))))
    [ModObj (StandardGroupSchemes.multiplicative k) H.X] (j : ℤ) :
    Submodule k (GrpObj.Lie H.X) :=
  Submodule.span k {v | ∀ (R : Type u) [CommRing R] [Algebra k R] (z : Rˣ),
    points.map (StandardGroupSchemes.multiplicative k)
        (TrivSqZeroExt.inlAlgHom k R R) (gmPoint R z) •
        points.map H.X (DualNumber.lift
          ⟨(Algebra.ofId k (DualNumber R), DualNumber.eps),
            DualNumber.eps_mul_eps, fun c ↦
              DualNumber.commute_eps_left (algebraMap k (DualNumber R) c)⟩)
          (GrpObj.tangentPoint v) =
      points.map H.X ((DualNumber.scale ((z ^ j : Rˣ) : R)).restrictScalars k)
        (points.map H.X (DualNumber.lift
          ⟨(Algebra.ofId k (DualNumber R), DualNumber.eps),
            DualNumber.eps_mul_eps, fun c ↦
              DualNumber.commute_eps_left (algebraMap k (DualNumber R) c)⟩)
          (GrpObj.tangentPoint v))}

/-- The actual multiplication map from a pair of subgroups into the ambient scheme.
Source: Milne, Theorem 13.33(d), pp.265--266
(blueprint: lem-sfb-gm-action-attracting-subgroup-big-cell). -/
def multiplication {H U V : Grp (Over (Spec (.of k)))}
    (i : U ⟶ H) (j : V ⟶ H) : U.X ⊗ V.X ⟶ H.X :=
  (fst U.X V.X ≫ i.hom.hom) * (snd U.X V.X ≫ j.hom.hom)

/-- Smooth geometrically connected attracting subgroups, their equivariant tangent
identifications, and the dense open multiplication cell when the weight-zero space vanishes.
Source: Milne, Definitions 13.29--13.30 and Theorem 13.33(a)--(e), pp.264--266
(blueprint: lem-sfb-gm-action-attracting-subgroup-big-cell).

Proof plan, following the five steps of the node:
1. Over a field finite type implies finite presentation
   (lem-weil-pbc-finite-type-noetherian-finite-presentation). Apply
   lem-sfb-relative-dynamic-subgroups to a and its reciprocal action. This gives
   the closed smooth connected subgroups, their all-algebra orbit formulas, and
   positive and negative tangent images. Retain the fixed subgroup Z and limit subgroup P,
   with Lie Z the weight-zero space and multiplication Z times U_+ isomorphic to P.
2. Uniqueness of an orbit extension follows from injectivity of R[t] into R[t,t^-1].
   Commuting the two action parameters shows that applying a(t,-) preserves each
   extension and its identity value at zero. Yoneda gives the restricted actions;
   their inclusions commute with the ambient action. Differentiating those actual
   diagrams proves equivariance, using lem-sfb-affine-group-dual-number-calculus.
3. If the zero weight vanishes, Z is smooth geometrically connected with zero tangent.
   Apply the empty-weight case of lem-sfb-positive-weight-affine-space-arbitrary-field
   to its trivial action: Z is Spec k as a group scheme, including on nonreduced algebras.
4. Thus P equals U_+ under its inclusion. Substitute in the open immersion
   U_- times P to H from lem-sfb-relative-dynamic-subgroups. Its map is multiplication
   and its image contains the identity.
5. Smoothness implies regularity (lem-weil-pbc-smooth-scheme-over-field-regular).
   Geometric connectedness and the identity imply connectedness and nonemptiness;
   lem-sc-regular-connected-integral gives integrality, hence irreducibility
   (def-pc-integral-scheme). The nonempty open image is therefore dense.
No perfectness or characteristic assumption is used. The empty tangent module,
trivial group, and zero test algebra are included. -/
theorem exists_attracting_subgroups_bigCell
    (H : Grp (Over (Spec (.of k)))) [IsAffine H.X.left]
    [Smooth H.X.hom] [GeometricallyConnected H.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [a : ModObj (StandardGroupSchemes.multiplicative k) H.X]
    (hAut : TorusCharacterTangent.ActsByGroupAutomorphisms
      (Grp.mk (StandardGroupSchemes.multiplicative k)) H) :
    ∃ (Uminus Uplus : Grp (Over (Spec (.of k))))
      (iminus : Uminus ⟶ H) (iplus : Uplus ⟶ H)
      (aminus : ModObj (StandardGroupSchemes.multiplicative k) Uminus.X)
      (aplus : ModObj (StandardGroupSchemes.multiplicative k) Uplus.X),
      IsClosedSubgroupScheme iminus.hom.hom ∧ IsClosedSubgroupScheme iplus.hom.hom ∧
      Smooth Uminus.X.hom ∧ Smooth Uplus.X.hom ∧
      GeometricallyConnected Uminus.X.hom ∧ GeometricallyConnected Uplus.X.hom ∧
      (∀ (R : Type u) [CommRing R] [Algebra k R] (h : points H.X R),
        (h ∈ Set.range (fun x : points Uminus.X R ↦ x ≫ iminus.hom.hom) ↔
          IsAttracting H (-1) R h) ∧
        (h ∈ Set.range (fun x : points Uplus.X R ↦ x ≫ iplus.hom.hom) ↔
          IsAttracting H 1 R h)) ∧
      (∀ (W : Over (Spec (.of k)))
        (s : W ⟶ StandardGroupSchemes.multiplicative k) (x : W ⟶ Uminus.X),
        lift s x ≫ aminus.smul ≫ iminus.hom.hom = s • (x ≫ iminus.hom.hom)) ∧
      (∀ (W : Over (Spec (.of k)))
        (s : W ⟶ StandardGroupSchemes.multiplicative k) (x : W ⟶ Uplus.X),
        lift s x ≫ aplus.smul ≫ iplus.hom.hom = s • (x ≫ iplus.hom.hom)) ∧
      (GrpObj.differential iminus.hom.hom).toLinearMap.range =
        ⨆ (j : ℤ) (_ : j < 0), weightSpace H j ∧
      (GrpObj.differential iplus.hom.hom).toLinearMap.range =
        ⨆ (j : ℤ) (_ : 0 < j), weightSpace H j ∧
      (weightSpace H 0 = ⊥ →
        IsOpenImmersion (multiplication iminus iplus).left ∧
          DenseRange (multiplication iminus iplus).left) := by
  sorry

end AlgebraicGeometry.GmAttractingBigCell
