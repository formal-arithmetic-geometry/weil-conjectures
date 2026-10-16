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
/-- The degree-zero injectivity and cycle-range identification component of the
    hypercover section theorem.
Source: Stacks Project, Hypercoverings, Tag 01GW.
(blueprint: lem-weil-pbc-hypercover-injective-abelian-zero)

Proof: Apply the injective extension argument to the exact free hypercover
resolution in the indicated degree.

This is one strictly lower component of the full conjunction. -/
theorem hypercover_injective_abelian_zero
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X)
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) [Injective I] :
    Function.Injective (I.obj.map (terminal.from
          (U.simplicial.obj (op (SimplexCategory.mk 0)))).op) ∧
      (∀ s : I.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk 0)))),
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}).obj
          (U.simplicial.rightOp ⋙ I.obj)).d 0 1 s = 0 ↔
          s ∈ Set.range (I.obj.map (terminal.from
          (U.simplicial.obj (op (SimplexCategory.mk 0)))).op)) := by
  sorry

end AlgebraicGeometry.SplitEtaleHypercover
