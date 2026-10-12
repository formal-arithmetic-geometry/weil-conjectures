module

public import Sheaf.Topology.ConstantSubsheafPositiveRefinementData

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Construct the coproduct factorization from a finite signed partition record.
Source: Stacks Project, Cohomology, Lemma 0A38, first proof paragraph, with the
factorization made explicit by gluing on the finite disjoint partition.
https://stacks.math.columbia.edu/tag/0A38
(blueprint: lem-sc-constant-subsheaf-positive-refinement-factor)

Proof: Write P for the coproduct of the extensions on d.A. For each original index i,
cover U i by d.Z i and the d.A j with d.parent j = i, using d.hcover. On d.Z i take
the zero section of P. On d.A j take d.sign j times the canonical unit section of
that extension, followed by its coproduct injection into P. The pieces are pairwise
disjoint by d.hdisjoint and d.hdisjointZ, so these sections agree on all intersections
(the only section of an abelian sheaf on the empty open is zero). Sheaf gluing gives
a section t i of P on U i with precisely these restrictions.

A section t of any abelian sheaf H on U determines a morphism j_U! Z to H: map the
constant integer presheaf on U to H restricted to U by integer multiples of the
restrictions of t, sheafify, apply extension by zero, and compose with the counit.
The resulting morphism sends the canonical unit to t. It is uniquely determined by
this value: maps from the constant integer presheaf are determined by one and
naturality, and both sheafifications and the slice extension preserve this universal
property (a presheaf map is fixed on every direct-sum injection).

Apply this construction to t i and take the coproduct of these morphisms to obtain l.
After composition with Sigma.desc d.f, the restriction of t i on each d.A j is
sign j times the unit image of f j, hence the restriction of d.s i by d.hsigned;
on d.Z i both are zero by d.hzero. Sheaf separation on the cover gives the unit
image d.s i on all of U i. By d.hs this is the unit image of the old component of g.
The uniqueness just established makes the two component morphisms equal. Coproduct
extensionality yields l followed by Sigma.desc d.f = g. Empty partitions and the
case n = 0 use the same gluing argument and force the old unit sections to be zero. -/
theorem positive_refinement_factor
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (m : ℕ) (U : Fin m → Opens X)
    (g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K)
    (d : PositiveRefinementData X K C ι isoC m U g) :
    ∃ l : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶
          (∐ fun i => (abelianOpenExtensionByZero (d.A i)).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (d.A i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))),
      l ≫ Sigma.desc d.f = g := by sorry

end TopCat.Sheaf
