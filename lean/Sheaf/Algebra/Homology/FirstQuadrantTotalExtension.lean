/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
import Sheaf.CategoryTheory.DoubleComplexTotal

/-! # Extension by zero and first-quadrant totalization

Source: Stacks Project, Section 12.18, Definition 12.18.3 (Tag 012Z),
by the diagonal direct-sum formula for the total complex.
(blueprint: lem-sc-total-extension-nat-arrow-iso)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ComplexShape

namespace HomologicalComplex₂

/-- Extending both indices by zero commutes naturally with totalization.
Source: Stacks Project, Section 12.18, Definition 12.18.3 (Tag 012Z);
the reindexing verification below is written by J2.
(blueprint: lem-sc-total-extension-nat-arrow-iso)

Proof: write E for extension of the inner index and then the outer index.
For n<0, every integer pair p+q=n has a negative coordinate, so every summand
of Tot(E K) in degree n is zero. Its degree-n object is therefore a zero object,
as is the extension of Tot(K) in that degree; use their unique isomorphism.
For n>=0, the only potentially nonzero summands have p,q>=0. Restricting the
integer diagonal to those pairs identifies it bijectively with the natural
pairs a+b=n.toNat. On each summand use the two extendXIso isomorphisms
(E K)^{a,b} ≅ K^{a,b}. Define a map of coproducts by these isomorphisms and
an inverse by their inverses. The remaining integer summands are zero and
have unique maps. Checking each coprojection proves both inverse identities.
For consecutive nonnegative degrees these maps commute with the horizontal
and vertical differential: extension uses the same component differentials,
and the total sign (-1)^p equals (-1)^a when p is the integer image of a.
For the boundary -1 to 0 the source is zero; for negative degrees all terms
are zero; other differentials vanish by the shape condition. Thus the maps
are an isomorphism of integer-indexed complexes. Each component is built
from extendXIso and coprojections, both natural in K, so for f:K→L they
identify Tot(E f) with the extension of Tot(f). These two complex
isomorphisms and the naturality square give the asserted arrow isomorphism.
This includes n=0, where the sole surviving summand is (0,0). -/
theorem totalMap_extend_nat_arrow_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : HomologicalComplex₂ C (up ℕ) (up ℕ)} (f : K ⟶ L)
    [HasTotal (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ) ⋙
      embeddingUpNat.extendFunctor (CochainComplex C ℤ)).obj K) (up ℤ)]
    [HasTotal (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ) ⋙
      embeddingUpNat.extendFunctor (CochainComplex C ℤ)).obj L) (up ℤ)] :
    Nonempty (Arrow.mk (total.map
      (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ) ⋙
        embeddingUpNat.extendFunctor (CochainComplex C ℤ)).map f) (up ℤ)) ≅
      Arrow.mk (HomologicalComplex.extendMap (total.map f (up ℕ)) embeddingUpNat)) := by
  sorry

end HomologicalComplex₂
