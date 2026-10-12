module

public import Sheaf.CategoryTheory.HypercohomologyLeftEdge
public import Mathlib.Algebra.Homology.SingleHomology

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

/-- Source: Stacks Project, derived.tex, Tag 015J.
(blueprint: lem-pc-hypercohomology-left-edge-single-aux)

Proof: For the single complex, the cycle inclusion identifies its degree-n cycles
with the sole term. The canonical lift of the mapped inclusion is characterized by
its composite with the mapped cycle inclusion. The definition of the hypercohomology
left edge and its truncation maps then gives the mapped homology projection; this is
the single-complex edge calculation from Tag 015J. The displayed equality follows
by cancellation through that canonical characterization. -/
theorem cochainHypercohomologyLeftEdge_single_aux (A : B) (n : ℕ) :
    let S := (HomologicalComplex.single B (ComplexShape.up ℕ) n).obj A
    let T := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj S
    let a := T.liftCycles (G.map (S.iCycles n)) (n + 1) (by simp) (by
      change G.map (S.iCycles n) ≫ G.map (S.d n (n + 1)) = 0
      rw [← G.map_comp, S.iCycles_d, G.map_zero])
    a ≫ T.homologyπ n ≫ G.cochainHypercohomologyLeftEdge S n =
      G.map (S.homologyπ n) := by
  sorry

end CategoryTheory.Functor
