/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Sheaf.Algebra.Homology.RowCycleLiftsToZigzag
import Sheaf.Algebra.Homology.ZigzagModule
import Sheaf.Algebra.Homology.ZigzagModuleFunctorial
import Sheaf.Algebra.Homology.ZigzagToRowCokernel
import Sheaf.Algebra.Homology.ZigzagTrivialIfRowBoundary

/-!
# Homology of cokernel complexes of an exact double complex

Source: Stacks Project, Algebra, Lemma Tag 00M1 (lemma-no-spectral-sequence),
including its preceding cokernel-complex construction and functoriality paragraph
(blueprint: lem-weil-pbc-double-complex-cokernel-homology-iso).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace HomologicalComplex₂

/-- For a first-quadrant homological double complex with commuting squares and rows
and columns exact in positive degrees, the homology of the column-cokernel complex
is naturally isomorphic to that of the row-cokernel complex.

As in the landed zig-zag modules, the row-cokernel complex `Aʳᵗ` is `A.opcycles 0`,
formed in the abelian category of chain complexes: its degree `q` is the cokernel of
`d₁,ᵩ : A₁,ᵩ → A₀,ᵩ`, with differential induced by `δ`, and a bicomplex morphism `Φ`
induces `opcyclesMap Φ 0`. The column-cokernel complex `Aᵘᵖ` is the same construction
applied to `A.flip` (no signs: `flip` only exchanges the indices): its degree `p` is
the cokernel of `δ_{p,1} : A_{p,1} → A_{p,0}` with differential induced by `d`, and `Φ`
induces `opcyclesMap (flip.map Φ) 0`. Row exactness is `ShortComplex.Exact` of
`d_{p+1,q}, d_{p,q}` for `p > 0`; column exactness the same for `δ` and `q > 0`.
The single family `θ` is chosen before quantifying over morphisms, and its homs
satisfy the naturality square `H_n(Φʳᵗ) ∘ θ^A = θ^B ∘ H_n(Φᵘᵖ)`.

Source: Stacks Project, Algebra, Tag 00M1 (lemma-no-spectral-sequence), setup and proof
(blueprint: lem-weil-pbc-double-complex-cokernel-homology-iso).

Proof: (1) Transpose the bicomplex. Its row-cokernel complex is the original
column-cokernel complex, and its zig-zag module is the same, by exchanging coordinates
(`def-weil-pbc-double-complex-zigzag-module`). (2) The endpoint map from zig-zag homology
to row-cokernel homology (`lem-weil-pbc-double-complex-zigzag-to-row-cokernel-map`)
is surjective by lifting a cycle through the exact rows
(`lem-weil-pbc-double-complex-row-cycle-lifts-to-zigzag`), and injective by eliminating
a zig-zag whose endpoint is a boundary
(`lem-weil-pbc-double-complex-zigzag-trivial-if-row-boundary`). Thus it is an isomorphism
`ρ`. (3) Apply (2) to the transpose to obtain the column-side isomorphism `λ`.
(4) Set `θ = λ⁻¹ ≫ ρ`. (5) A bicomplex morphism acts on zig-zags coordinatewise
(`lem-weil-pbc-double-complex-zigzag-module-functorial`), and the endpoint maps commute
with it by the naturality clause of the endpoint-map lemma. Composing the two
commutative squares with `λ⁻¹` gives the displayed naturality equation. Homology and
exactness throughout are `def-weil-pbc-module-chain-complex-homology` and
`def-weil-pbc-exact-sequence`. -/
theorem doubleComplexCokernelHomologyIso (R : Type u) [CommRing R] :
    let D := HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)
    let E := fun A : D =>
      (∀ (p q : ℕ), 0 < p →
        (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
          (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
            HomologicalComplex.zero_f])).Exact) ∧
      (∀ (p q : ℕ), 0 < q →
        (ShortComplex.mk ((A.X p).d (q + 1) q) ((A.X p).d q (q - 1))
          (by simp)).Exact)
    let flip := flipFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    ∃ θ : ∀ (A : D), E A → ∀ n : ℕ,
        (A.flip.opcycles 0).homology n ≅ (A.opcycles 0).homology n,
      ∀ (A B : D) (hA : E A) (hB : E B) (Φ : A ⟶ B) (n : ℕ),
        (θ A hA n).hom ≫
            HomologicalComplex.homologyMap (HomologicalComplex.opcyclesMap Φ 0) n =
          HomologicalComplex.homologyMap
              (HomologicalComplex.opcyclesMap (flip.map Φ) 0) n ≫ (θ B hB n).hom := by
  sorry

end HomologicalComplex₂
