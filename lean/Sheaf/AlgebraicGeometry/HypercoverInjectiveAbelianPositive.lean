module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-! Intermediate degree component for `lem-weil-pbc-hypercover-free-resolution`. -/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SplitEtaleHypercover
/-- The positive-degree homology vanishing component of the hypercover section theorem.
Source: Stacks Project, Hypercoverings, Tag 01GW.
(blueprint: lem-weil-pbc-hypercover-injective-abelian-positive)

Proof: Apply the injective extension argument to the exact free hypercover
resolution in the indicated degree.

This is one strictly lower component of the full conjunction. -/
theorem hypercover_injective_abelian_positive
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X)
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) [Injective I] :
    ∀ p : ℕ, 0 < p → IsZero
      (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) := by
  sorry

end AlgebraicGeometry.SplitEtaleHypercover
