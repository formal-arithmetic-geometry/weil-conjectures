/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Quotient
import Sheaf.AlgebraicGeometry.EtaleAtPointFromDifferentials
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Conormal-kernel coordinates and their smooth zero slice

Source: Stacks Project, morphisms.tex, Tags 02GU, 02G1, 02GO; algebra.tex, Tags 00RU,
00DF. This is the coordinate-slice consequence assembled in the DAG, not a literal
statement of any one of those tags (blueprint: lem-trf-conormal-kernel-coordinate-slice).

Affine spaces are written in their polynomial-spectrum model. All differential fibres
have the residue field on the left. After restricting scalars, their tensor products
are taken over the original ambient algebra B. For an affine open containing p and a
closed subscheme through p this is canonically the usual residue-field fibre: the
residue-field base change of its coordinate ring is the residue field itself.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The canonical map on differential fibres for B to a B-algebra C, with coefficients L.
The target is written over B by restriction of scalars. On generators this sends
l tensor db to l tensor d(image b). Source: Stacks 00RU, 00DF
(blueprint: lem-trf-conormal-kernel-coordinate-slice). -/
noncomputable def conormalCoordinateFibreMap
    (k B C L : Type u) [CommRing k] [CommRing B] [CommRing C] [CommRing L]
    [Algebra k B] [Algebra k C] [Algebra B C] [IsScalarTower k B C] [Algebra B L] :
    (L ⊗[B] KaehlerDifferential k B) →ₗ[L] (L ⊗[B] KaehlerDifferential k C) :=
  LinearMap.baseChange L (KaehlerDifferential.map k k B C)

/-- Witnesses of the coordinate-slice assertion, with every comparison normalized by
its canonical map. This record merely bundles the witnesses of the theorem below.
Its affine neighbourhood is Spec C with its open immersion into Spec B; f and g are
its actual regular functions. The quotient C/(f) defines the zero slice, so if the
index set of f is empty this is canonically Spec C. The ideal containment is scheme
theoretic, including for nonreduced X. Polynomial variables are indexed by the disjoint
union of the first r and the remaining n-r coordinates.

The tensor products over B represent the usual fibres over kappa(p)=kappa(p/I).
The map defining K has target L tensor_B Omega((B/I)/k), canonically the same as
L tensor_(B/I) Omega((B/I)/k), since I annihilates both factors.
Source: Stacks 02GU, 02G1, 02GO, 00RU, 00DF; the DAG's coordinate-slice construction
(blueprint: lem-trf-conormal-kernel-coordinate-slice). -/
structure ConormalKernelCoordinateSlice
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    (I p : Ideal B) [p.IsPrime] where
  /-- The coordinate ring of the affine open neighbourhood. -/
  C : Type u
  [commRingC : CommRing C]
  [algebraBC : Algebra B C]
  [algebraKC : Algebra k C]
  [towerKBC : IsScalarTower k B C]
  /-- Spec C is an open subscheme of the given ambient affine scheme. -/
  openImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B C)))
  /-- A point of this neighbourhood lying over p. -/
  point : PrimeSpectrum C
  point_eq : PrimeSpectrum.comap (algebraMap B C) point = ⟨p, inferInstance⟩
  /-- The ambient differential-fibre dimension and the kernel dimension. -/
  n : ℕ
  r : ℕ
  n_eq : n = Module.finrank p.ResidueField
    (p.ResidueField ⊗[B] KaehlerDifferential k B)
  r_eq : r = Module.finrank p.ResidueField
    (LinearMap.ker (conormalCoordinateFibreMap k B (B ⧸ I) p.ResidueField))
  /-- Equations vanishing on X restricted to the neighbourhood. -/
  f : Fin r → C
  f_mem : ∀ i, f i ∈ I.map (algebraMap B C)
  /-- The complementary coordinate functions. -/
  g : Fin (n - r) → C
  /-- The affine-open differential-fibre identification, with its prescribed map. -/
  fibreIso : (p.ResidueField ⊗[B] KaehlerDifferential k B) ≃ₗ[p.ResidueField]
    (p.ResidueField ⊗[B] KaehlerDifferential k C)
  fibreIso_map : fibreIso.toLinearMap = conormalCoordinateFibreMap k B C p.ResidueField
  /-- The chosen equation differentials form a basis of the kernel K. -/
  kernelBasis : Module.Basis (Fin r) p.ResidueField
    (LinearMap.ker (conormalCoordinateFibreMap k B (B ⧸ I) p.ResidueField))
  kernelBasis_eq : ∀ i, fibreIso (kernelBasis i).val =
    TensorProduct.tmul B (1 : p.ResidueField) (KaehlerDifferential.D k C (f i))
  /-- All the chosen differentials together form a basis of V. -/
  ambientBasis : Module.Basis (Fin r ⊕ Fin (n - r)) p.ResidueField
    (p.ResidueField ⊗[B] KaehlerDifferential k B)
  ambientBasis_f : ∀ i, ambientBasis (Sum.inl i) = (kernelBasis i).val
  ambientBasis_g : ∀ j, fibreIso (ambientBasis (Sum.inr j)) =
    TensorProduct.tmul B (1 : p.ResidueField) (KaehlerDifferential.D k C (g j))
  /-- The actual coordinate map, rather than an unspecified etale chart, is etale. -/
  etale : Etale (Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := k) (Sum.elim f g)).toRingHom))
  /-- The zero slice contains X restricted to Spec C as a closed subscheme. -/
  contains : Ideal.span (Set.range f) ≤ I.map (algebraMap B C)
  /-- The zero slice and its remaining-coordinate map form the prescribed pullback. -/
  cartesian : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range f)))))
    (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval
      (fun j ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (g j))).toRingHom))
    (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) (Sum.elim f g)).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := k) (Sum.elim (fun _ : Fin r ↦
        (0 : MvPolynomial (Fin (n - r)) k)) MvPolynomial.X)).toRingHom))
  /-- The whole zero slice is smooth over k. -/
  smooth : Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap k (C ⧸ Ideal.span (Set.range f)))))
  /-- The quotient of V by K is the differential fibre of the zero slice. -/
  quotientIso :
    ((p.ResidueField ⊗[B] KaehlerDifferential k B) ⧸
      LinearMap.ker (conormalCoordinateFibreMap k B (B ⧸ I) p.ResidueField))
      ≃ₗ[p.ResidueField]
        (p.ResidueField ⊗[B] KaehlerDifferential k (C ⧸ Ideal.span (Set.range f)))
  /-- This identification is induced by the canonical differential-fibre map. -/
  quotientIso_map : ∀ v, quotientIso
    ((LinearMap.ker (conormalCoordinateFibreMap k B (B ⧸ I) p.ResidueField)).mkQ v) =
      conormalCoordinateFibreMap k B (C ⧸ Ideal.span (Set.range f)) p.ResidueField v

/-- Conormal-kernel coordinates with an etale coordinate map and a smooth zero slice,
for an arbitrary closed subscheme of a smooth finite-type affine k-scheme.
Source: Stacks Project, Tags 02GU, 02G1, 02GO, 00RU and 00DF, assembled as in the DAG
(blueprint: lem-trf-conormal-kernel-coordinate-slice).

Proof. Use lem-weil-pbc-jacobi-zariski-differential-maps and
lem-weil-pbc-tensor-right-exact: the conormal sequence, tensored with L=kappa(p), says K is spanned
by differential classes of elements of I. Smoothness makes the ambient fibre finite
dimensional. Select a basis from those ideal differentials and complete it to a basis
using differentials of actual functions of B. The affine differential-sheaf and stalk
localization identifications carry this basis to the geometric differential fibre.
lem-weil-pbc-smooth-ring-map-iff-smooth-affine and
lem-pur-etale-at-point-from-differentials give an open neighbourhood on which
the resulting map to affine n-space is etale. Choose an affine open inside it containing
p, using lem-weil-pbc-affine-opens-basis and lem-weil-pbc-etale-composition-cancellation.
Restrict the functions and use def-sc-relative-differential-sheaf and
lem-weil-pbc-spec-tilde-stalk-localization for fibreIso; the field identification uses
lem-weil-pbc-prime-residue-field-algebra.
Put J=(f) in its coordinate ring C. Since J is contained in IC, Spec(C/IC), the
scheme-theoretic intersection with X, factors through Spec(C/J). The tensor-quotient
formula C tensor_(k[T]) k[T_remaining] = C/J gives the displayed Cartesian square,
with the remaining coordinates precisely g modulo J, by
lem-weil-pbc-tensor-quotient-base-change and lem-weil-pbc-fibre-product-affine-spectra.
Apply lem-weil-pbc-etale-scheme-base-change,
lem-weil-pbc-etale-smooth-zero-dimensional-fibres, sbc-lem-affine-space-smooth and
lem-trf-smooth-composition to make Spec(C/J) smooth over k. Finally apply the
quotient conormal sequence to C to C/J and tensor with L. For h=sum a_i f_i, Leibniz
gives dh=sum a_i df_i in the residue fibre because each f_i vanishes at the point.
Thus its kernel is exactly the span of df_i, identified with K. The first isomorphism
theorem gives quotientIso, with quotientIso_map by the same conormal sequence.
For r=0 the ideal J is zero, so the zero slice is the whole neighbourhood. No step
assumes smoothness or reducedness of X, or a closed or rational marked point. -/
theorem exists_conormalKernelCoordinateSlice
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    [Algebra.Smooth k B] [Algebra.FiniteType k B]
    (I p : Ideal B) [p.IsPrime] (hp : I ≤ p) :
    Nonempty (ConormalKernelCoordinateSlice k B I p) := by
  sorry

end AlgebraicGeometry
