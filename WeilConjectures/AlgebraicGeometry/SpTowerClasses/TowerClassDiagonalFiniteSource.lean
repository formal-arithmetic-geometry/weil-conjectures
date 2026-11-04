/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryForgetComparison
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSourceAux
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSourceAuxDerived
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSourceAuxSource

/-! # The ordinary supported finite source of a normalized diagonal -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau lineModule
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The scalar adjunct of the supported comparison has precisely the canonical
supported integral quotient at every finite level.

Source: latest blueprint geometric classes proof (3), the supported source
normalization in the finite diagonal calculation.
(blueprint: lem-sp-tower-class-diagonal-finite-source).

Proof: compose the inverse reduction comparison, the supplied supported source
isomorphism and the exact geometric single comparison. Transpose this composite
through the scalar adjunction. Fullness of the single functor gives its unique
ordinary module map q. Naturality of the two adjunction units and the two
normalized coefficient-unit comparisons turn d.source_normalization into an
equality of the corresponding ordinary maps after restriction and evaluation.
The exact-right-adjoint single-unit equation identifies the geometric side with
the ordinary coefficient pullback adjunct. Its prescribed section formula sends
each coefficient integer to its residue times one on the base-changed chart.
The reduction and scalar generator section equations give the same formula on
the other side. The transported supported integral unit is epic: the etale
open/closed integral section sequence is short exact and exact inverse image
preserves its epimorphism; the two site comparisons are isomorphisms. Hence
precomposition with that unit detects equality of these ordinary sheaf maps.
The unique generator-normalized supported quotient is therefore exactly the
composite displayed below. All statements compare degree-zero sheaf maps;
no faithfulness of finite evaluation on arbitrary derived maps is used. -/
theorem exists_diagonalFiniteSource {b : SpTowerShriek.Base l E}
    {S : Scheme.{u}} [IsNoetherian S]
    {c : Chern l E (diagonalSurface S)} (hc : c.Normalized l E)
    (d : Diagonal l E b S c) :
    let X := (constant (diagonalSurface S)).obj (diagonalIntegralSource S)
    let N := d.geometry.push.obj
      (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    ∀ (a : c.reduction.derived.obj
        ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj X) ≅
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) 0).obj (c.reduction.ordinary.obj X))
      (_ha : c.reduction.model.sourceNormalization a
        (c.reduction.model.adjunction.unit.app X)),
    let s := c.scalar.T.mapIso a.symm ≪≫ d.sourceIso ≪≫
      (d.geometry.push.singleFunctorCompRightDerivedFunctorIso).app
        (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    ∃ q : c.reduction.ordinary.obj X ⟶
        (WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).obj N,
      ((c.scalar.adjunction.homEquiv _ _) s.hom ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).mapDerivedCategorySingleFunctor
            0).hom.app N =
        (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Rrings l (diagonalSurface S))) 0).map q) ∧
      ∀ n : ℕ,
        (abEvaluation (diagonalSurface S) n).map
            (c.reduction.model.adjunction.unit.app X) ≫
          (c.reduction.forget.F ⋙ abEvaluation (diagonalSurface S) n).map q ≫
          (finiteScalarForgetIso l E c n).hom.app N =
        finiteSupportedQuotient l E d.geometry n := by
  intro X N a ha s
  obtain ⟨q, hq⟩ := scalar_adjunct_single l E c (c.reduction.ordinary.obj X) N s
  refine ⟨q, hq, fun n ↦ ?_⟩
  have := supported_integral_unit_epi S
  exact finite_source_of_precompose l E c (supportedIntegralUnit S)
    (c.reduction.model.adjunction.unit.app X) q
    ((d.geometry.ordinaryAdjunction.homEquiv _ _) d.coefficientPullback.iso.hom) n
    (finiteSupportedQuotient l E d.geometry n)
    (ordinary_source_precompose l E hc d a ha q hq)
    (supportedIntegralUnit_comp_finiteSupportedQuotient l E d.geometry d.coefficientPullback n)

end AlgebraicGeometry.ProEtale.SpTowerClasses
