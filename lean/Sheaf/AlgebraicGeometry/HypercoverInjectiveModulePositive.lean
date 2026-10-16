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
(blueprint: lem-weil-pbc-hypercover-injective-module-positive)

Proof: Apply the injective extension argument to the exact free hypercover
resolution in the indicated degree.

This is one strictly lower component of the full conjunction. -/
theorem hypercover_injective_module_positive
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) (R : Type (w + 1)) [CommRing R]
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} R)) [Injective I] :
    ∀ p : ℕ, 0 < p → IsZero
      (((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{w + 1} R)).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) := by
  sorry

end AlgebraicGeometry.SplitEtaleHypercover
