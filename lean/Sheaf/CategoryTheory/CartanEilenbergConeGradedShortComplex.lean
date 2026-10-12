/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Short-complex comparison for the Cartan--Eilenberg cone filtration

Source: Stacks Project, Homology, Tag 0133, canonical augmentation, and Tag 012X,
column filtration of a total complex. This is the augmented-cone refinement used
in the parent node's second proof step.
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- The three terms and two differentials of a graded cone are those of its column cone.
Source: Stacks Project, Homology, Tags 0133 and 012X; augmented-cone refinement
of the parent filtration-properties node, proof step 2.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-short-complex-iso).

Proof: fix p and a total degree m. The cone object is the biproduct of K^(m+1)
and the diagonal coproduct of the extended bicomplex. The formula hF presents
step p as the sum of precisely the summands of complex index at least p.
Projection onto complex index p annihilates step p+1. Its restriction to step p
therefore descends to the degree-m cokernel of the successive-step inclusion;
evaluation on cochain complexes preserves this cokernel. Inclusion of the index-p
summands into step p followed by its cokernel projection is inverse to this
map. On the retained summand one composite is the identity. To check the other,
cancel the epic cokernel projection and check on the generating summands of
step p: the index-p summand gives the identity, and each larger-index summand
factors through step p+1 and is killed by the cokernel projection. These are
jointly generating because step p is their finite image supremum.

The retained object is the index-(m-p) object of the column mapping cone: its
K^p summand occurs exactly at m=p-1, and its I-column summand at m>=p. Identify
the former using the extension of the single complex at resolution degree zero,
and the latter using extendXIso. For p<b both are zero by hKbelow and hIbelow;
for m<p-1 both are zero by extension by zero. Thus the same construction works
for empty intervals, zero columns, and every integer p and m.

Perform this construction in the three degrees m=n-1,n,n+1. The cone differential
on K is -d_K, whose image has complex index p+1 and vanishes in the quotient.
The horizontal bicomplex differential also raises complex index and vanishes.
The resolution differential preserves complex index. Since the bicomplex is
flipped, it is the first total differential and has coefficient one. Finally,
on K^p in degree p-1 the off-diagonal differential is aug.f p; haug identifies
its retained component with the extension of (a.f p).f 0. All other components
of the extended single complex are zero. Consequently the two squares commute
with exactly the differentials of the column cone at degrees n-p-1,n-p,n-p+1.
The three degreewise isomorphisms and these two squares define the short-complex
isomorphism. No exactness or quasi-isomorphism assumption is used. -/
theorem cartanEilenberg_cone_graded_shortComplex_iso
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p n : ℤ) :
    Nonempty ((F.gradedPiece p).sc n ≅
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).sc (n - p)) := by
  sorry

end CategoryTheory.Functor
