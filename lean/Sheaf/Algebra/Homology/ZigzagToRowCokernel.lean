/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker G1
-/
module

public import Sheaf.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The canonical map from zig-zags to row-cokernel homology

Source: Stacks Project, Algebra, Tag 00M1, proof and functoriality paragraph
(blueprint: lem-weil-pbc-double-complex-zigzag-to-row-cokernel-map).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace HomologicalComplex₂

open Classical in
/-- The endpoint of a zig-zag induces a natural linear map to row-cokernel homology.
Source: Stacks Project, Algebra, Tag 00M1, proof, canonical homomorphisms and the
right-hand square of the functoriality diagram
(blueprint: lem-weil-pbc-double-complex-zigzag-to-row-cokernel-map).

Here `C A = A.opcycles 0` is formed in the abelian category of chain complexes:
its degree `q` is the cokernel of `d : A₁,ᵩ → A₀,ᵩ`. The projection `π A` is a
chain map, and `opcyclesMap Φ 0` is the induced row-cokernel chain map.
The first three clauses record the cokernel and its differential and morphism formulas.
The fourth clause is (a); the fifth is (b); the last two specify the induced map
on representatives and its naturality (c). No exactness is assumed.

Proof: (1) Commuting squares make `δ` descend through each horizontal cokernel;
`δ² = 0` makes these cokernels a complex. Commutation of `Φ` with `d` makes it
descend, and commutation with `δ` makes the descended maps a chain map. The
projections are surjective with kernel the horizontal image.
(2) For a zig-zag of positive degree, its last equation is
`δ a₀,ₙ = d a₁,ₙ₋₁`; the cokernel projection kills the right side. At degree zero
the outgoing differential vanishes. This uses the relations of
`def-weil-pbc-double-complex-zigzag-module`.
(3) For a trivial zig-zag `D b`, the endpoint is `d b₁,ₙ + δ b₀,ₙ₊₁`;
its projection is the boundary `δʳᵗ π b₀,ₙ₊₁`. Thus its homology class is zero,
using `def-weil-pbc-module-chain-complex-homology`.
(4) The endpoint projection followed by the homology class map is linear on
zig-zags, and kills their intersection with trivial zig-zags by (3). The quotient
universal property gives the unique linear map `ρ`, with the stated formula.
(5) On a representative `a`, both composites in the naturality square give the
class of `π Φ₀,ₙ a₀,ₙ`, by the projection formula in (1). Representatives generate
the quotient, so the linear maps agree. No row or column exactness is used. -/
theorem exists_zigzagToRowCokernel
    {R : Type u} [CommRing R] (n : ℕ) :
    let C := fun A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) => A.opcycles 0
    let π := fun A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) => A.pOpcycles 0
    let e := fun A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) =>
      DirectSum.component R (ZigzagIndex n)
        (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩
    ∃ ρ : ∀ A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ), zigzagModule A n →ₗ[R] (C A).homology n,
      (∀ A q, Function.Surjective ((π A).f q) ∧
        LinearMap.ker ((π A).f q).hom = LinearMap.range ((A.d 1 0).f q).hom) ∧
      (∀ A q, (A.X 0).d (q + 1) q ≫ (π A).f q =
        (π A).f (q + 1) ≫ (C A).d (q + 1) q) ∧
      (∀ A B (Φ : A ⟶ B) q,
        (π A).f q ≫ (HomologicalComplex.opcyclesMap Φ 0).f q =
          (Φ.f 0).f q ≫ (π B).f q) ∧
      (∀ A (a : zigzagCycles A n),
        (C A).d n (n - 1) ((π A).f n (e A a.val)) = 0 ∧
        ∃ c : (C A).cycles n, (C A).iCycles n c = (π A).f n (e A a.val)) ∧
      (∀ A (a : zigzagCycles A n), a.val ∈ zigzagBoundaries A n →
        ∀ c : (C A).cycles n, (C A).iCycles n c = (π A).f n (e A a.val) →
          (C A).homologyπ n c = 0) ∧
      (∀ A (a : zigzagCycles A n) (c : (C A).cycles n),
        (C A).iCycles n c = (π A).f n (e A a.val) →
          ρ A (((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).mkQ a) =
            (C A).homologyπ n c) ∧
      (∀ A B (Φ : A ⟶ B),
        (ModuleCat.Hom.hom
          (HomologicalComplex.homologyMap (HomologicalComplex.opcyclesMap Φ 0) n)).comp (ρ A) =
          (ρ B).comp (zigzagMap Φ n)) := by
  sorry

end HomologicalComplex₂
