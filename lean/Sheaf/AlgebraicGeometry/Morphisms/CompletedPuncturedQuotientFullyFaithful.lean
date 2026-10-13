/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Sheaf.RingTheory.Depth

/-! # Full faithfulness on the punctured completion

Source: Stacks Project, Tags 0BM6, 0AVY and 0ALZ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Quotient restriction of finite etale covers of the punctured completion is fully faithful.

Source: Stacks Project, Tag 0BM6, applied in the complete case of Tag 0BLS;
Tags 0AVY, 0ALZ and 0ALJ.
(blueprint: lem-sbc-completed-punctured-quotient-fully-faithful)

Proof: The maximal-ideal completion C is Noetherian, local, complete and flat over A.
Its maximal ideal is the extension of that of A, and the only prime of C above the
maximal ideal of A is its maximal ideal. Hence W is the punctured spectrum of C.
The depth hypothesis gives H¹_m(A) = H²_m(A) = 0 (0AVY). Flat base change for
local cohomology (0ALZ) gives H¹_mC(C) = H²_mC(C) = 0. In particular both are
annihilated by a power of the image g of f. Completeness and g in the maximal ideal
give (g)-adic completeness: any (g)-adic Cauchy sequence converges in the maximal
ideal topology and the ideals (g)^n are closed; Krull intersection gives uniqueness.
Hence (C,(g)) is henselian (0ALJ). Apply 0BM6: finite etale covers of W restrict fully
faithfully to W intersected with Spec(C/(g)). The morphism j restricted to W is
exactly that intersection. The morphism-property over category is the category
of finite etale covers, so the result is the fully faithful structure below.
For f = 0 the functor is base change by an isomorphism; empty covers are included. -/
theorem fullyFaithful_completed_punctured_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
    let W := c ⁻¹ᵁ U
    let j := Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {algebraMap A C f})))
    Nonempty (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤
      (j ∣_ W)).FullyFaithful := by sorry

end AlgebraicGeometry.Scheme
