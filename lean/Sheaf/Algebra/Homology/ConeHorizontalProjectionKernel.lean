/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Algebra.Homology.ConeHorizontalProjection
public import Sheaf.Algebra.Homology.ConeHorizontalStepStable
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

/-! # Kernel of the signed horizontal column projection

Source: Stacks Project, Homology, Tag 012X, first-filtration formula before
Lemma 12.25.1 (label lemma-double-complex), with the cone refinement in
lem-sp-cone-horizontal-quotient-iso-exists, proof step 1.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- The next horizontal tail is exactly the kernel of the restricted signed projection.
Source: Stacks Project, Homology, Tag 012X, first-filtration column calculation;
existence node lem-sp-cone-horizontal-quotient-iso-exists, proof step 1.
(blueprint: lem-sp-cone-horizontal-projection-kernel)

Proof: In each degree the horizontal tail is the sum of the diagonal source and target summands
with horizontal index at least p. In the biproduct coordinates the signed projection is (-1)^p
times the source coordinate at p and the target coordinate at p. Both coefficients are invertible.
Its kernel is therefore precisely the sum of coordinates with index strictly greater than p, which
is the next tail. The inclusion of F.step (p+1) into F.step p is monic in each degree and hF
identifies its ambient image with that next tail. Pulling this equality back along the monic arrow
of F.step p gives the stated kernel equality. For n<p-1 the column object and p-tail are zero; at
n=p-1 only the source coordinate is present, so the same argument applies. -/
theorem coneHorizontal_projection_kernel
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B)
    (F : DecreasingFiltration (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)))
    (hF : ∀ p n : ℤ, F.complexStep p n = coneHorizontalStep f p n)
    (p : ℕ) (n : ℤ) :
    imageSubobject ((Subobject.ofLE (F.step ((p : ℤ) + 1))
      (F.step (p : ℤ)) (F.antitone_step (by omega))).f n) =
      kernelSubobject ((F.step (p : ℤ)).arrow.f n ≫ coneHorizontalProjection f p n) := by
  sorry

end HomologicalComplex₂
