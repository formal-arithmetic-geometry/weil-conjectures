/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Restriction of the complementary smart truncation comparison -/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The comparison from any cokernel of a restricted smart cutoff inclusion
to the restricted complementary truncation is a quasi-isomorphism.
Source: Mathlib Algebra/Homology/Embedding/AreComplementary.lean,
`shortComplexTruncLEX₃ToTruncGE` and its `QuasiIso` instance.
(blueprint: lem-sp-restricted-complementary-truncation-comparison).

Proof: put E = L.extend embeddingUpNat. Restriction to natural vertical indices
preserves cokernels, since colimits of complexes are computed degreewise. Thus the
cokernel universal property identifies Q with
(cokernel (E.ιTruncLE (a-1))).restriction embeddingUpNat, via an isomorphism
compatible with the cokernel projections. The equation hg
identifies g, under this isomorphism, with the restriction of
E.shortComplexTruncLEX₃ToTruncGE (a-1) a. The embeddings are complementary since
(a-1)+1=a, so Mathlib makes this integer-indexed map a quasi-isomorphism.
For a>0, E is zero in negative degrees, its cutoff is also zero there, and hence
its cokernel is zero there; the lower truncation is zero below a. Thus source and
target have zero degree -1, and restriction preserves their homology even at zero:
there the incoming image is zero in both integer and natural complexes. At positive
indices the three terms and differentials computing homology are unchanged.
For a<=0, the cutoff below a is zero, and truncation from below at a changes only
zero terms (including the boundary cokernel of a zero incoming map). The comparison
is an isomorphism. This includes a=0, a=1, and a column concentrated in degree zero.
Transfer the restricted quasi-isomorphism across the source isomorphism. -/
theorem restrictedComplementaryTruncationComparison_quasiIso
    (L : CochainComplex C ℕ) (a : ℤ) (Q : CochainComplex C ℕ)
    (π : (L.extend ComplexShape.embeddingUpNat).restriction
      ComplexShape.embeddingUpNat ⟶ Q)
    (hzero : HomologicalComplex.restrictionMap
      (CochainComplex.ιTruncLE (L.extend ComplexShape.embeddingUpNat) (a - 1))
        ComplexShape.embeddingUpNat ≫ π = 0)
    (hπ : IsColimit (CokernelCofork.ofπ π hzero))
    (g : Q ⟶ (CochainComplex.truncGE (L.extend ComplexShape.embeddingUpNat) a).restriction
      ComplexShape.embeddingUpNat)
    (hg : π ≫ g = HomologicalComplex.restrictionMap
      (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a)
        ComplexShape.embeddingUpNat) :
    QuasiIso g := by
  sorry

end CochainComplex
