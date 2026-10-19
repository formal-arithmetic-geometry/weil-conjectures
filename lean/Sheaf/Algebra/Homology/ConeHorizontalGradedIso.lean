/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Algebra.Homology.ConeHorizontalStepStable
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Sheaf.Algebra.Homology.ConeHorizontalQuotientIso
import Sheaf.Algebra.Homology.ConeHorizontalProjectionDifferential

/-! # The graded complexes of the horizontal cone filtration

Source: Stacks Project, Homology, Tag 012X, first filtration and its graded complexes.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- The nonnegative graded complexes of the explicit horizontal cone filtration
are shifts of column cones.
Source: Stacks Project, Homology, Tag 012X, first filtration and graded complexes;
the sign correction is the columnwise-cone refinement in the parent node, step 3.
(blueprint: lem-sp-cone-horizontal-graded-iso)

Proof: evaluation preserves cokernels. The quotient of the sum with horizontal
indices at least p by the sum with indices at least p+1 retains exactly the
source and target summands of horizontal index p. Their diagonal inclusions
induce isomorphisms onto this quotient, because the diagonal coproduct is a
finite direct sum. The horizontal differential goes into the next step and
therefore disappears. Put k=n-p and e=(-1)^p. On these summands the differential
has source block -e*d_A, target block e*d_B and off-diagonal block f. The
column cone shifted by -p has source block -e*d_A, target block e*d_B and
off-diagonal block e*f. Multiply the source summand by e and leave the target
summand fixed. The diagonal blocks commute with these scalars, and the
source scalar times e*f equals f since e squared is one. These maps therefore
commute with the differentials. The same scalars give their inverses. Include
the source term at k=-1: it is essential at n=p-1.
For k<-1 both summands are zero, and the same construction uses their unique
maps. Thus the comparison is valid in every integer degree. -/
theorem coneHorizontal_graded_iso
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B)
    (F : DecreasingFiltration (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)))
    (hF : ∀ p n : ℤ, F.complexStep p n = coneHorizontalStep f p n)
    (p : ℤ) (hp : 0 ≤ p) :
    Nonempty (F.gradedPiece p ≅
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap (f.f p.toNat) ComplexShape.embeddingUpNat))⟦-p⟧) := by
  classical
  let q := p.toNat
  have h : Nonempty (F.gradedPiece (q : ℤ) ≅
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap (f.f q) ComplexShape.embeddingUpNat))⟦-(q : ℤ)⟧) := by
    have hquot := fun n ↦ (coneHorizontal_quotient_iso f F hF q n).exists
    choose a ha using hquot
    have hi : ∀ n, IsIso (a n) := fun n ↦ (ha n).1
    let e := fun n ↦ asIso (a n)
    refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    change a i ≫ _ = _ ≫ a (i + 1)
    let π := F.complexQuotientπ (q : ℤ) ((q : ℤ) + 1) (by omega)
    have hπ : Epi (π.f i) := by
      dsimp only [π, DecreasingFiltration.complexQuotientπ]
      infer_instance
    apply (cancel_epi (π.f i)).1
    calc
      π.f i ≫ a i ≫ _ =
          ((F.step (q : ℤ)).arrow.f i ≫ coneHorizontalProjection f q i) ≫ _ := by
        rw [← Category.assoc, (ha i).2]
      _ = (F.step (q : ℤ) : CochainComplex C ℤ).d i (i + 1) ≫
          (F.step (q : ℤ)).arrow.f (i + 1) ≫ coneHorizontalProjection f q (i + 1) :=
        coneHorizontal_projection_differential f F hF q i
      _ = (F.step (q : ℤ) : CochainComplex C ℤ).d i (i + 1) ≫
          π.f (i + 1) ≫ a (i + 1) := by rw [(ha (i + 1)).2]
      _ = π.f i ≫ (F.gradedPiece (q : ℤ)).d i (i + 1) ≫ a (i + 1) := by
        exact (π.comm_assoc i (i + 1) (a (i + 1))).symm
  simpa only [q, Int.toNat_of_nonneg hp] using h

end HomologicalComplex₂
