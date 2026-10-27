/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.LfpSmoothFlatBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.FiniteTypeLocalDimension
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Lang surjectivity over a finite field

Source: Milne, Algebraic Groups, Section 17.k, Theorem 17.96 and Corollary 17.97,
printed pp.382–383 (blueprint: lem-sfb-lang-finite-field-group-surjectivity).

Points are scheme morphisms over the base field. For an affine group this is the
canonical identification with algebra homomorphisms from its coordinate algebra.
Precomposition with Spec of arithmetic Frobenius raises their values to `|k|`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- Lang's map `g ↦ g⁻¹ σ(g)` is surjective on algebraic-closure-valued points.
Source: Milne, Algebraic Groups, Theorem 17.96 and Corollary 17.97, printed p.383
(blueprint: lem-sfb-lang-finite-field-group-surjectivity).

Proof plan:
1. Base change to the algebraic closure. The identity section and
`lem-sbc-connected-rational-point-geometrically-connected` give connectedness.
`lem-sfb-finite-type-composition-base-change` and
`lem-sfb-scheme-lfp-smooth-flat-base-change` preserve finite type and smoothness.
Affineness gives separatedness (`lem-weil-pbc-affine-source-morphism-separated`),
smoothness gives regularity (`lem-weil-pbc-smooth-scheme-over-field-regular`), and
`lem-sc-regular-connected-integral` gives integrality. The dimension is finite by
`lem-kun-finite-type-local-dimension` and `lem-ag-group-identity-local-dimension`.
2. The coordinate endomorphism `c ↦ c^|k|` defines the Frobenius group endomorphism.
Its point action is precomposition with Spec of arithmetic Frobenius. The right
action `x · a = a⁻¹ x F(a)` satisfies the action laws by associativity and the
homomorphism property, without commuting factors.
3. The stabilizer at `x` has points satisfying `x F(a) x⁻¹ = a`.
`lem-sfb-inner-frobenius-fixed-points-finite` makes this set finite;
`lem-sfb-zero-dimensional-stabilizer-finite-orbit` gives dimension zero, even for
nonreduced stabilizers. By `lem-sfb-smooth-group-orbit-geometry` all orbits have
the same dimension as the group and their orbit maps are surjective.
4. The identity orbit has empty boundary: a nonempty boundary has a rational
closed point (`lem-sc-lft-over-field-jacobson-space` and
`lem-weil-pbc-closed-point-residue-field-base`), whose orbit would have strictly
smaller dimension by `lem-sfb-smooth-group-orbit-geometry`, a contradiction.
Thus the identity orbit is closed. Irreducibility and finite dimension force it
to be the whole group: a proper closed subset of equal dimension would extend
an irreducible closed chain beyond the group's dimension.
5. Each nonempty fibre of the identity orbit map is of finite type over the
algebraically closed field. Again `lem-sc-lft-over-field-jacobson-space` and
`lem-weil-pbc-closed-point-residue-field-base` supply a rational point in the fibre,
which is the required `g`. This last step gives surjectivity on valued points.
-/
theorem lang_finite_field_surjective {k K : Type u} [Field k] [Fintype k]
    [Field K] [Algebra k K] [IsAlgClosure k K]
    (G : Over (Spec (.of k))) [GrpObj G] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [Smooth G.hom]
    [ConnectedSpace G.left] :
    ∀ h : (Spec (.of K)).asOver (Spec (.of k)) ⟶ G,
      ∃ g : (Spec (.of K)).asOver (Spec (.of k)) ⟶ G,
        g⁻¹ * ((Spec.map (CommRingCat.ofHom
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toAlgHom.toRingHom)).asOver
            (Spec (.of k)) ≫ g) = h := by
  sorry

end AlgebraicGeometry
