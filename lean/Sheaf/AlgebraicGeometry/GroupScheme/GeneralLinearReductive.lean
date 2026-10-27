module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Connected.Basic
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Reductivity of the general linear group

Source: Milne, Algebraic Groups (2017), Lemma 19.16, Corollary 19.18 and
Example 19.19, printed p.401; Example 2.40, printed p.52
(blueprint: lem-sfb-general-linear-reductive).

The existing reductivity predicate includes smoothness, affine finite type,
geometric connectedness and scheme-theoretic triviality of the geometric unipotent radical.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeneralLinearGroup

/-- GL_n over any field is smooth affine of finite type, geometrically connected and reductive.
Source: Milne, Example 19.19 with Lemma 19.16 and Corollary 19.18, p.401;
Example 2.40, p.52 (blueprint: lem-sfb-general-linear-reductive).

Proof:
1. The coordinate algebra is k[x_ij, det(X)^{-1}], by def-sc-general-linear-group.
It is finitely generated, and its spectrum is the determinant principal open of affine space
(def-sbc-affine-space and lem-weil-pbc-affine-open-section-vanishing-prime). Affine space is
smooth by sbc-lem-affine-space-smooth, and its open is smooth by
lem-pc-open-immersion-smooth-composition. This proves affine finite type and smoothness.
2. Polynomial evaluation, localization and the tensor-product universal properties identify
its scalar extension to K with K[x_ij, det(X)^{-1}]. Use
lem-weil-pbc-ring-localization-universal-property,
lem-weil-pbc-algebra-tensor-pushout-universal-property and
lem-weil-pbc-fibre-product-affine-spectra. The inverse maps fix coefficients, variables and
inverse determinant. The comultiplications agree on variables, so this is a group isomorphism.
3. This polynomial ring is a domain by lem-weil-pbc-polynomial-ring-domain; the determinant
is nonzero by evaluation at the identity. Its localization is a nonzero domain. Its spectrum
is irreducible by lem-zl-spectrum-irreducible-nilradical-prime, hence connected by
lem-pc-irreducible-space-connected. Apply this over the algebraic closure.
4. Let U be a smooth connected normal closed unipotent subgroup over the algebraic closure.
It is affine finite type as a closed subgroup of GL. Its faithful unipotent representation
and lem-sfb-unipotent-rational-representation-fixed-vector give a nonzero vector fixed by U
in the standard n-dimensional representation; n >= 1 is precisely the dimension hypothesis.
5. Normality makes the fixed subspace stable under GL. For a nonzero vector w with w_j != 0,
if n > 1 a transvection I+E_ij gives w_j e_i in the subspace. Permutation matrices then give
all basis vectors. For n=1 the original nonzero vector spans. Thus U fixes the entire space.
6. Smoothness makes the coordinate algebra C of U reduced by
sbc-lem-smooth-geometrically-reduced. The entries x_ij-delta_ij vanish on all geometric
points, hence vanish in C by lem-wf-affine-nullstellensatz-vanishing, clause 2. The surjection
k[x_ij, det(X)^{-1}] -> C therefore has scalar image. The identity section splits k -> C,
so C=k. Thus U is the trivial group scheme, including its scheme structure. -/
theorem isReductive (k : Type u) [Field k] (n : ℕ) (_hn : 1 ≤ n) :
    ReductiveTorusCentralizer.IsReductive
      (Grp.mk (AlgebraicGeometry.GeneralLinearGroup (LinearGroupSchemes.Index.{u} n) k)) := by
  sorry

end AlgebraicGeometry.GeneralLinearGroup
