/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import WeilConjectures.RingTheory.SupportedHomogeneousDivision
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.MvPowerSeries.Trunc
import WeilConjectures.AlgebraicGeometry.GenericMonotoneVertexChart
import WeilConjectures.RingTheory.InitialExponentHomogeneousDivision
import WeilConjectures.RingTheory.SupportedFormalDivision
import Mathlib.Order.WellFounded

/-!
# Generic monotone Taylor diagrams and regular vertex generators

Source: ILO VIII 2.3.11--2.3.13; Bierstone--Milman, Invent. Math. 128 (1997),
sections 3.5, 7.1, 8 and the first paragraph of the proof of Theorem 9.6, pp.278--279
(blueprint: lem-trf-generic-monotone-diagram).

The conclusion records the actual Taylor ideal of the pulled-back closed subscheme.
All exponents use ascending total-degree lexicographic order. The polynomial division
assertion uses the existing indexed division family, so no quotient support is replaced
by an arbitrary choice. The chart preserves the residue field at the distinguished point.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.HilbertCoefficient

/-- The chart, its actual exponent diagram, and the conclusions about regular vertex lifts.
This is a specification of the conclusion, with no chosen existence witness. The ring map
`coord` is an etale coordinate chart on the affine neighbourhood, compatible with `p`.
The residue-field isomorphism retains the field at the original, possibly nonclosed, point.

`diagram_spec` defines the diagram by least nonzero terms, rather than prescribing an
unrelated upper set. The initial homogeneous polynomial is obtained by taking the
homogeneous component and its finite total truncation. Unique division is required for
every degree prefix and every family of regular vertex lifts, and supported generation
is required for the entire Taylor ideal, including the empty-family case.

Source: ILO VIII 2.3.11--2.3.13; Bierstone--Milman, sections 3.5, 7.1, 8 and
Theorem 9.6, first proof paragraph (blueprint: lem-trf-generic-monotone-diagram). -/
structure GenericMonotoneDiagram {k : Type u} [Field k] {X M : Scheme.{u}}
    (p : M ⟶ Spec (CommRingCat.of k)) (i : X ⟶ M) (a : X) where
  U : Scheme.{u}
  affine : IsAffine U
  e : U ⟶ M
  etale : Etale e
  center : U
  center_eq : e center = i a
  residue_iso : Function.Bijective (e.residueFieldMap center)
  n : ℕ
  coord : MvPolynomial (Fin n) k →+* Γ(U, ⊤)
  etale_coord : coord.Etale
  over_k : U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (coord.comp MvPolynomial.C)) = e ≫ p
  taylor : Γ(U, ⊤) →+* MvPowerSeries (Fin n) (U.residueField center)
  taylor_spec : isTaylorMap coord (U.Γevaluation center).hom taylor
  diagram : Set (Fin n →₀ ℕ)
  diagram_spec : ∀ d : Fin n →₀ ℕ,
    d ∈ diagram ↔ ∃ f : MvPowerSeries (Fin n) (U.residueField center),
      f ∈ taylorIdeal (RingHom.ker (pullback.snd i e).appTop.hom) taylor ∧
      MvPowerSeries.coeff d f ≠ 0 ∧
      ∀ b : Fin n →₀ ℕ, Finsupp.DegLex (· < ·) (· < ·) b d →
        MvPowerSeries.coeff b f = 0
  monotone : MonomialDiagram.IsMonotone diagram
  s : ℕ
  vertex : Fin s → Fin n →₀ ℕ
  vertices : MonomialDiagram.IsOrderedVertexFamily diagram vertex
  diagram_eq : diagram = MonomialDiagram.generated vertex
  F : Fin s → Γ(U, ⊤)
  regular_generators : RingHom.ker (pullback.snd i e).appTop.hom = Ideal.span (Set.range F)
  initial_coefficient : ∀ j : Fin s, MvPowerSeries.coeff (vertex j) (taylor (F j)) = 1
  initial_minimal : ∀ (j : Fin s) (b : Fin n →₀ ℕ),
    Finsupp.DegLex (· < ·) (· < ·) b (vertex j) →
      MvPowerSeries.coeff b (taylor (F j)) = 0
  any_lifts : ∀ G : Fin s → Γ(U, ⊤),
    (∀ j : Fin s, G j ∈ RingHom.ker (pullback.snd i e).appTop.hom) →
    (∀ j : Fin s, MvPowerSeries.coeff (vertex j) (taylor (G j)) = 1) →
    (∀ (j : Fin s) (b : Fin n →₀ ℕ),
      Finsupp.DegLex (· < ·) (· < ·) b (vertex j) →
        MvPowerSeries.coeff b (taylor (G j)) = 0) →
    (∀ q t : ℕ,
      MonomialDiagram.HasUniqueDivision
        (MonomialDiagram.generated (MonomialDiagram.prefixVertices vertex q))
        (MonomialDiagram.prefixVertices vertex q)
        (fun j ↦ MvPowerSeries.truncTotal ((vertex j.val).degree + 1)
          (MvPowerSeries.homogeneousComponent (vertex j.val).degree (taylor (G j.val)))) t) ∧
    (∀ f ∈ taylorIdeal (RingHom.ker (pullback.snd i e).appTop.hom) taylor,
      ∃ Q : Fin s → MvPowerSeries (Fin n) (U.residueField center),
        f = ∑ j : Fin s, Q j * taylor (G j) ∧
        ∀ j : Fin s, supported (Q j) (fun b ↦ b ∈ MonomialDiagram.quotientSupport vertex j))
  empty_vertices : taylorIdeal (RingHom.ker (pullback.snd i e).appTop.hom) taylor = ⊥ → s = 0

private theorem exists_first_exponent {L : Type u} [Field L] {n : ℕ}
    (f : MvPowerSeries (Fin n) L) (hf : f ≠ 0) :
    ∃ α : Fin n →₀ ℕ, MonomialDiagram.IsFirstExponent f α := by
  classical
  have hcoeff : ∃ α : Fin n →₀ ℕ, MvPowerSeries.coeff α f ≠ 0 := by
    by_contra h
    apply hf
    ext α
    simpa using not_exists.mp h α
  have hne : {α : DegLex (Fin n →₀ ℕ) |
      MvPowerSeries.coeff (ofDegLex α) f ≠ 0}.Nonempty := by
    obtain ⟨α, hα⟩ := hcoeff
    exact ⟨toDegLex α, hα⟩
  obtain ⟨α, hα, hmin⟩ :=
    (wellFounded_lt (α := DegLex (Fin n →₀ ℕ))).has_min _ hne
  refine ⟨ofDegLex α, hα, ?_⟩
  intro β hβ
  by_contra h
  exact hmin (toDegLex β) h hβ

private theorem supported_generation {L : Type u} [Field L] {n s : ℕ}
    (K : Ideal (MvPowerSeries (Fin n) L)) (α : Fin s → Fin n →₀ ℕ)
    (hdiagram : MonomialDiagram.initialDiagram K = MonomialDiagram.generated α)
    (G : Fin s → MvPowerSeries (Fin n) L)
    (hG : ∀ j : Fin s, G j ∈ K)
    (hfirst : ∀ j : Fin s, MonomialDiagram.IsFirstExponent (G j) (α j))
    (f : MvPowerSeries (Fin n) L) (hf : f ∈ K) :
    ∃ Q : Fin s → MvPowerSeries (Fin n) L,
      f = ∑ j : Fin s, Q j * G j ∧
      ∀ j : Fin s, supported (Q j) (fun b ↦ b ∈ MonomialDiagram.quotientSupport α j) := by
  obtain ⟨Q, R, heq, hQ, hR, _⟩ :=
    MonomialDiagram.exists_unique_supported_formal_division G α hfirst f
  have hRK : R ∈ K := by
    have hsum : (∑ j : Fin s, Q j * G j) ∈ K :=
      K.sum_mem fun j _ ↦ K.mul_mem_left _ (hG j)
    have hsub := K.sub_mem hf hsum
    rwa [heq, add_sub_cancel_left] at hsub
  have hzero : R = 0 := by
    by_contra hne
    obtain ⟨β, hβ⟩ := exists_first_exponent R hne
    have hβD : β ∈ MonomialDiagram.generated α := by
      rw [← hdiagram]
      exact ⟨R, hRK, hβ⟩
    exact hR hβ.1 hβD
  refine ⟨Q, ?_, ?_⟩
  · simpa only [hzero, add_zero] using heq
  · exact fun j b hb ↦ hQ j hb

/-- Generic coordinates make the Taylor diagram monotone and give regular normalized
vertex generators, with homogeneous prefix division and supported formal generation
for every choice of regular vertex lifts.

Source: ILO VIII 2.3.11--2.3.13; Bierstone--Milman, Invent. Math. 128 (1997),
sections 3.5, 7.1, 8 and Theorem 9.6, first proof paragraph
(blueprint: lem-trf-generic-monotone-diagram).

Proof (the seven DAG steps):
1. In an etale chart put R = O_{M,a}, L = kappa(a), S = L[[T]]. Apply
[lem-trf-taylor-normal-cone-splitting] to identify the homogeneous initial ideal
of IS with the extension of its normal associated-graded ideal. The least exponent
of a series is the least exponent of its lowest homogeneous part; homogeneous sums
and products are realized by sums and products of series. Thus their diagrams agree.
2. Apply [lem-trf-graded-generic-initial-borel] and intersect its generic open with
the nonempty open where the normal subspace projects isomorphically to the last c
coordinates. The infinite field k has a point in this open: a nonzero polynomial
over L cannot vanish on all k-valued matrices, by induction using the root bound.
For i < j, Borel invariance under T_i -> T_i + T_j and the coefficientwise description
of a monomial ideal put the full-transfer exponent in the diagram. Its coefficient
is 1; characteristic zero is used in Borel fixity, not in this final calculation.
3. Multiplication by monomials makes the diagram upward closed. By
[lem-trf-monomial-upper-set-finite-basis], its minimal elements form a finite antichain
and every exponent lies above a minimal element. These are exactly the ordered vertices.
The empty diagram is equivalent to the zero ideal.
4. Write variables as (U,V). The projection condition gives normal forms V+AU.
This substitution and its inverse preserve least fixed-degree lexicographic terms.
The homogeneous comparison in [lem-trf-taylor-normal-cone-splitting] therefore makes
the diagram N^{n-c} times the normal diagram. Vertices have zero U component.
Represent each vertex normal symbol by a germ in I intersect m^{d_i}. Its Taylor
expansion has the required first exponent. Multiply by a unit lifting its inverse
initial coefficient; represent these finitely many germs on a common neighbourhood.
5. For any such lifts and each degree prefix, take columns T^b H_i with b in Delta_i
and the complementary monomials. There is one column per degree-t monomial; each
starts with its assigned monomial with coefficient 1. The ordered matrix is triangular
with diagonal 1. Back substitution gives unique homogeneous division, including zero
quotients below a vertex degree and the empty prefix.
6. Apply [lem-trf-supported-formal-division] to all vertex expansions. For an element
of IS the remainder also belongs to IS. A nonzero remainder would have its least
exponent both in the diagram and outside it, a contradiction. This gives supported
generation for every lift family, without formal standard-basis normalization.
7. Apply [lem-trf-implicit-taylor-coordinate-calculus] with no implicit equations.
Its centered Taylor map is faithfully flat even at nonclosed points. Contract the
equality of extended finitely generated ideals to obtain stalk generation, then
spread equality of coherent ideals to a neighbourhood. For IS=0 the same argument
gives the empty generating family. For n=0 the proper ideal at a point of X is zero.
All chart changes and shrinkings are finite and can preserve the residue field. -/
theorem genericMonotoneDiagram {k : Type u} [Field k] [CharZero k]
    {X M : Scheme.{u}} (p : M ⟶ Spec (CommRingCat.of k)) (i : X ⟶ M)
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] [IsClosedImmersion i] (a : X) :
    Nonempty (GenericMonotoneDiagram p i a) := by
  classical
  obtain ⟨C⟩ := genericMonotoneVertexChart p i a
  have hdiagram : MonomialDiagram.initialDiagram
      (taylorIdeal (RingHom.ker (pullback.snd i C.e).appTop.hom) C.taylor) =
      MonomialDiagram.generated C.vertex := by
    rw [← C.diagram_eq]
    ext d
    exact (C.diagram_spec d).symm
  refine ⟨{
    U := C.U
    affine := C.affine
    e := C.e
    etale := C.etale
    center := C.center
    center_eq := C.center_eq
    residue_iso := C.residue_iso
    n := C.n
    coord := C.coord
    etale_coord := C.etale_coord
    over_k := C.over_k
    taylor := C.taylor
    taylor_spec := C.taylor_spec
    diagram := C.diagram
    diagram_spec := C.diagram_spec
    monotone := C.monotone
    s := C.s
    vertex := C.vertex
    vertices := C.vertices
    diagram_eq := C.diagram_eq
    F := C.F
    regular_generators := C.regular_generators
    initial_coefficient := C.initial_coefficient
    initial_minimal := C.initial_minimal
    any_lifts := ?_
    empty_vertices := ?_
  }⟩
  · intro G hG hcoeff hminimal
    have hfirst : ∀ j : Fin C.s,
        MonomialDiagram.IsFirstExponent (C.taylor (G j)) (C.vertex j) :=
      fun j ↦ ⟨by rw [hcoeff j]; exact one_ne_zero, hminimal j⟩
    constructor
    · intro q t
      exact MonomialDiagram.initialExponentHomogeneousDivision
        (fun j : {j : Fin C.s // (C.vertex j).degree ≤ q} ↦ C.taylor (G j.val))
        (MonomialDiagram.prefixVertices C.vertex q) (fun j ↦ hfirst j.val) t
    · intro f hf
      exact supported_generation _ C.vertex hdiagram (fun j ↦ C.taylor (G j))
        (fun j ↦ Ideal.mem_map_of_mem C.taylor (hG j)) hfirst f hf
  · intro hzero
    by_contra hs
    let j : Fin C.s := ⟨0, Nat.pos_of_ne_zero hs⟩
    have hj : C.vertex j ∈ C.diagram :=
      ((C.vertices.1 (C.vertex j)).2 ⟨j, rfl⟩).prop
    obtain ⟨f, hf, hcoeff, _⟩ := (C.diagram_spec (C.vertex j)).mp hj
    rw [hzero, Ideal.mem_bot] at hf
    exact hcoeff (by rw [hf, map_zero])

end AlgebraicGeometry.HilbertCoefficient
