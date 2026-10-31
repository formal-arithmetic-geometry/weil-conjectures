/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalKummerTameModule
public import WeilConjectures.AlgebraicGeometry.RootTowerLisseMorphismExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Elementary compatible-root boundary data

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
agent-extracted returned step 2 of the root-tower boundary argument.
(blueprint: def-sfb-parameter-root-boundary-data).

The affine tower, parameter stratum, zero-root evaluation and their profinite-test
maps are moved here from RootBoundaryComparison, retaining their public names.
The test map is the actual pullback lift, independent of the coordinate-face theorem.

## Main definitions

* `tower`, `stratumRing`, `stratumScheme`, `stratumInclusion`: the affine schemes.
* `zeroRoots`, `boundary`: quotient evaluation and its spectrum.
* `test`, `testMap`, `qP`: actual profinite tests and their structural morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RootBoundary
variable (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R)

/-- The existing compatible prime-to-p root algebra, viewed as an affine scheme.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data). -/
def tower : Scheme.{u} := Spec (.of (tameRootAlgebra p t))

/-- The quotient by all original boundary parameters.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data). -/
abbrev stratumRing := R ⧸ Ideal.span (Set.range t)

/-- The scheme-theoretic common-zero stratum, including the empty list of parameters.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data). -/
def stratumScheme : Scheme.{u} := Spec (.of (stratumRing t))

/-- The closed inclusion of the common-zero stratum.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data). -/
def stratumInclusion : stratumScheme t ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range t))))

/-- The root relations vanish when every root and every boundary parameter is set to zero.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data).

Proof: On each power relation the evaluated root is zero, its exponent is positive,
and the original parameter is zero in the quotient by the parameter ideal. On each
transition relation both sides evaluate to zero, because the quotient m/n is positive
for positive n dividing m. The kernel contains the generating relations, hence their ideal. -/
theorem roots_vanish : Ideal.span (tameRootRelations p t) ≤ RingHom.ker
    (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (Ideal.span (Set.range t)))
      (fun _ : Fin r × TameRootOrder p ↦ 0)) := by
  apply Ideal.span_le.mpr
  intro a ha
  apply RingHom.mem_ker.mpr
  rcases ha with ⟨i, n, rfl⟩ | ⟨i, n, m, hnm, rfl⟩
  · have ht : Ideal.Quotient.mk (Ideal.span (Set.range t)) (t i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    simp only [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
      zero_pow n.property.1.ne', ht, sub_self]
  · have hpos : 0 < m.val / n.val :=
      Nat.div_pos (Nat.le_of_dvd m.property.1 hnm) n.property.1
    simp only [map_sub, map_pow, MvPolynomial.eval₂Hom_X', zero_pow hpos.ne', sub_self]

/-- The actual quotient homomorphism setting every compatible root to zero.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data). -/
def zeroRoots : tameRootAlgebra p t →+* stratumRing t :=
  Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (Ideal.span (Set.range t)))
      (fun _ : Fin r × TameRootOrder p ↦ 0)) (roots_vanish p t)

/-- The canonical map of the common-zero stratum into the full compatible-root tower.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data). -/
def boundary : stratumScheme t ⟶ tower p t :=
  Spec.map (CommRingCat.ofHom (zeroRoots p t))

/-- The canonical boundary map lies over the stratum inclusion.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data).

Proof: The composite ring homomorphism from the base ring to the zero-root quotient
is the quotient map, since evaluation acts on constants by that quotient map. Apply
contravariance of Spec and the equality of these ring maps. -/
theorem boundary_square : boundary p t ≫ parameterRootProjection p t = stratumInclusion t := by
  unfold boundary parameterRootProjection stratumInclusion
  rw [← Spec.map_comp]
  congr 1
  ext a
  change zeroRoots p t
    (Ideal.Quotient.mk (Ideal.span (tameRootRelations p t)) (MvPolynomial.C a)) = _
  simp only [zeroRoots, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]
  rfl

/-- The recorded actual profinite test scheme, rather than a formal product or discrete set.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data). -/
abbrev test (X : Scheme.{u}) (P : Profinite.{u}) := (profiniteToProEtOf X).obj P

/-- The existing base-change map between actual profinite test schemes.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data). -/
abbrev testMap {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Profinite.{u}) :
    (test X P).left ⟶ (test Y P).left :=
  pullback.lift (pullback.fst _ _) ((test X P).hom ≫ f)
    (specULiftZIsTerminal.hom_ext _ _)

/-- The full-tower test projection to the affine base.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data). -/
abbrev qP (P : Profinite.{u}) := (test (tower p t) P).hom ≫ parameterRootProjection p t

/-- The actual boundary-test map lies over the stratum inclusion.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-parameter-root-boundary-data).

Proof: The defining pullback lift for the boundary-test map commutes with its
projection. Compose with the full-tower projection, use boundary_square, and reassociate. -/
theorem test_boundary_square (P : Profinite.{u}) :
    testMap (boundary p t) P ≫ qP p t P = (test (stratumScheme t) P).hom ≫ stratumInclusion t := by
  have h : testMap (boundary p t) P ≫ (test (tower p t) P).hom =
      (test (stratumScheme t) P).hom ≫ boundary p t := pullback.lift_snd _ _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f ↦ f ≫ parameterRootProjection p t) h).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun f ↦ (test (stratumScheme t) P).hom ≫ f) (boundary_square p t))))

end AlgebraicGeometry.ProEtale.RootBoundary
