/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Successive canonical upper truncations

Source: Stacks Project, Homology, Section 12.15 (Tag 0118), and Derived Categories,
Remark 13.12.4 (Tag 08J5) (blueprint: lem-weil-pbc-truncation-step-ses).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Successive canonical upper truncations and their cohomology quotient.
Source: Stacks, Homology Tag 0118 and Derived Categories Remark 08J5
(blueprint: lem-weil-pbc-truncation-step-ses).

Proof, following the node's seven steps:
1. Define the inclusion by the identity below `q - 1`, the cycles inclusion at
`q - 1`, and zero above. Its composite into `K` is the earlier truncation inclusion.
2. Form the two-term quotient: the cokernel of the kernel inclusion at `q - 1`
and cycles at `q`. The differential induced by `d` is mono by
`lem-weil-pbc-coimage-mono`, and its image is the boundaries.
3. The quotient map is the cokernel projection at `q - 1`, identity on cycles at
`q`, and zero elsewhere. It commutes with the differential and kills the inclusion.
4. These sequences are short exact in each degree, hence short exact as complexes
by `lem-weil-pbc-cochain-complexes-degreewise-exact`; their quotient is `cokernel i`.
5. Projection from cycles to homology defines the map to the single complex. It
kills boundaries, factors through the quotient, and the factor is unique since
its projection is epi.
6. The quotient has zero homology at `q - 1` because its differential is mono.
At `q` its homology is cycles modulo boundaries, and the induced map is the identity
under this identification. In other degrees both homologies vanish. Thus the
factor is a quasi-isomorphism.
7. A chain map preserves cycles and boundaries. It restricts to both truncations
and descends to the quotient, commuting with the cohomology projection; uniqueness
of descent gives naturality.
-/
theorem exists_upperTruncationStepSES {C : Type u} [Category.{v} C] [Abelian C] :
    ∃ (i : ∀ (K : CochainComplex C ℤ) (q : ℤ),
          K.truncLE (q - 1) ⟶ K.truncLE q)
      (j : ∀ (K : CochainComplex C ℤ) (q : ℤ),
          K.truncLE q ⟶ (singleFunctor C q).obj (K.homology q))
      (barj : ∀ (K : CochainComplex C ℤ) (q : ℤ),
          cokernel (i K q) ⟶ (singleFunctor C q).obj (K.homology q)),
      (∀ (K : CochainComplex C ℤ) (q : ℤ),
        i K q ≫ K.ιTruncLE q = K.ιTruncLE (q - 1)) ∧
      (∀ (K : CochainComplex C ℤ) (q : ℤ),
        (ShortComplex.mk (i K q) (cokernel.π (i K q))
          (cokernel.condition (i K q))).ShortExact) ∧
      (∀ (K : CochainComplex C ℤ) (q r : ℤ),
        r ≠ q - 1 → r ≠ q → IsZero ((cokernel (i K q)).X r)) ∧
      (∀ (K : CochainComplex C ℤ) (q : ℤ),
        ∃ (e₀ : (cokernel (i K q)).X (q - 1) ≅
              cokernel (kernel.ι (K.d (q - 1) q)))
          (e₁ : (cokernel (i K q)).X q ≅ K.cycles q),
          (cokernel.π (i K q)).f (q - 1) ≫ e₀.hom =
            (K.ιTruncLE q).f (q - 1) ≫ cokernel.π (kernel.ι (K.d (q - 1) q)) ∧
          (cokernel.π (i K q)).f q ≫ e₁.hom = (K.truncLEXIsoCycles q).hom ∧
          cokernel.π (kernel.ι (K.d (q - 1) q)) ≫ e₀.inv ≫
              (cokernel (i K q)).d (q - 1) q ≫ e₁.hom ≫ K.iCycles q =
            K.d (q - 1) q ∧
          Mono ((cokernel (i K q)).d (q - 1) q) ∧
          e₁.inv ≫ (barj K q).f q ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
            K.homologyπ q) ∧
      (∀ (K : CochainComplex C ℤ) (q : ℤ),
        (j K q).f q ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
          (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q ∧
        (∀ r : ℤ, r ≠ q → (j K q).f r = 0) ∧
        j K q = cokernel.π (i K q) ≫ barj K q ∧
        (∀ b : cokernel (i K q) ⟶ (singleFunctor C q).obj (K.homology q),
          cokernel.π (i K q) ≫ b = j K q → b = barj K q) ∧
        IsZero ((cokernel (i K q)).homology (q - 1)) ∧ QuasiIso (barj K q)) ∧
      (∀ {K L : CochainComplex C ℤ} (f : K ⟶ L) (q : ℤ),
        truncLEMap f (q - 1) ≫ i L q = i K q ≫ truncLEMap f q ∧
        ∃ (g : cokernel (i K q) ⟶ cokernel (i L q)),
          truncLEMap f q ≫ cokernel.π (i L q) = cokernel.π (i K q) ≫ g ∧
          barj K q ≫ (singleFunctor C q).map (HomologicalComplex.homologyMap f q) =
            g ≫ barj L q) := by
  sorry

end CochainComplex
