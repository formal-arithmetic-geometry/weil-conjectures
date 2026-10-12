module

public import Sheaf.CategoryTheory.HypercohomologyLeftEdge

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- Canonical lift case of the hypercohomology left-edge cocycle equation.
Source: Stacks Project, derived.tex, Tag 015J; this is the representative
calculation for the canonical cycle lift.
(blueprint: lem-pc-hypercohomology-edge-cocycle-canonical)

The canonical lift is the map on cycles induced by left exactness.  The proof
uses a Cartan--Eilenberg resolution and computes the degree-zero representative
of the truncation edge; the resulting quotient is the image under `G` of the
cycles-to-homology quotient.  This is the fixed-lift special case of the
cocycle equation and is strictly simpler because no uniqueness argument for a
supplied lift is involved.
-/
theorem cochainHypercohomologyLeftEdge_canonical
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (K : CochainComplex B ℕ) (n : ℕ) :
    (let T := ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
     let c := T.liftCycles (G.map (K.iCycles n)) (n + 1) (by simp)
       (by
         change G.map (K.iCycles n) ≫ G.map (K.d n (n + 1)) = 0
         rw [← G.map_comp, K.iCycles_d, G.map_zero])
     c ≫ T.homologyπ n ≫ G.cochainHypercohomologyLeftEdge K n =
       G.map (K.homologyπ n)) := by
  sorry

end CategoryTheory.Functor
