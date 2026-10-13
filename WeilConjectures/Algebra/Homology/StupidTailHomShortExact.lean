/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Single

/-! # Short exact Hom sequences for a stupid source tail

Source: Stacks Project, Tag 0A8X, product Hom differential;
Tag 0117, natural long exact cohomology sequence.
(blueprint: lem-pc-stupid-tail-hom-short-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The Hom maps for the bottom source term, the entire source, and its next stupid
tail occur as the three components of a morphism of short exact sequences.
The arrow isomorphisms include the identifications of each Hom complex and its map,
so the statement supplies naturality in the second variable as well as exactness.

Source: Stacks Project, Tag 0A8X, product Hom differential;
Tag 0117, natural long exact cohomology sequence.
(blueprint: lem-pc-stupid-tail-hom-short-exact).

Proof: let T be the stupid tail of P in degrees at least k+1 and let G be P.X k
placed in degree k. Since P vanishes below k, inclusion of T and projection to G
give a degreewise split short exact sequence 0 to T to P to G to 0. Applying
internal Hom into M gives 0 to Hom(G,M) to Hom(P,M) to Hom(T,M) to 0.
Construct the maps by extending a family at k by zero and restricting a family
to degrees at least k+1. The formula d_M h - (-1)^n h d_P proves both are chain
maps: for the extension map, its source-composition term vanishes because the
only possible incoming source differential is from the zero term P.X (k-1);
restriction is compatible because the differential at a source degree p only
uses p and p+1. In each Hom degree, splitting the product index set into the
singleton k, the tail, and the zero terms below k makes this sequence split.
Use the same maps for N. Postcomposition by f commutes with extension and
restriction componentwise, giving a morphism of these short exact sequences.
Take S and T to be these two short exact Hom sequences and φ to have
these three postcomposition maps as its components. The product identifications
with the named Hom complexes give the required arrow isomorphisms.
The product splitting uses no exactness of an infinite product; it is a
splitting of an existing product into two factors, valid for unbounded P, M, N. -/
theorem exists_homComplex_stupid_tail_shortExact
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k : ℤ) (hbelow : ∀ n : ℤ, n < k → IsZero (P.X n))
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : M ⟶ N) : ∃ S T : ShortComplex (CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      ∃ φ : S ⟶ T, S.ShortExact ∧ T.ShortExact ∧
        Nonempty (Arrow.mk φ.τ₁ ≅ Arrow.mk (((homComplexFunctor (R := R)).obj
          (op ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj
            (P.X k)))).map f)) ∧
        Nonempty (Arrow.mk φ.τ₂ ≅ Arrow.mk
          (((homComplexFunctor (R := R)).obj (op P)).map f)) ∧
        Nonempty (Arrow.mk φ.τ₃ ≅ Arrow.mk (((homComplexFunctor (R := R)).obj
          (op (P.stupidTrunc (ComplexShape.embeddingUpIntGE (k + 1))))).map f)) := by sorry

end CategoryTheory
