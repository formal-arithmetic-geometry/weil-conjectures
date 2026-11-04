/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassSupportedScalarPushAuxReduction
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSourceAuxDerived

/-! # The supported scalar push comparison from ordinary data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau lineModule
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The supported scalar push comparison follows from two ordinary facts: K-flatness
of the ordinary supported reduction in degree zero, and an ordinary isomorphism from
its scalar extension to the direct image of the coefficient module whose ordinary
adjunct has the prescribed coefficient formula after the supported integral unit.

Proof: the universal scalar counit is invertible on the K-flat single, so the
ordinary isomorphism gives the derived one. The derived source equation follows from
`scalar_reduction_source_eq`, and the exact single comparison of the direct image
identifies the single of the ordinary coefficient pullback adjunct with the
geometric unit. -/
theorem exists_supportedScalarPushComparison_of_ordinary
    {b : SpTowerShriek.Base l E} (S : Scheme.{u})
    (c : Chern l E (diagonalSurface S)) (hc : c.Normalized l E)
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S))
    (p : CoefficientPullback l E b (diagonalImmersion S) g)
    (a : c.reduction.derived.obj
        ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))) ≅
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) 0).obj
        (c.reduction.ordinary.obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))
    (ha : c.reduction.model.sourceNormalization a
      (c.reduction.model.adjunction.unit.app
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))
    (hM : CochainComplex.IsKFlatIndependentCoefficients
      (R := WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology (diagonalSurface S))
        (fun n ↦ (Rrings l (diagonalSurface S)).obj (op n))
        (fun n ↦ (Rrings l (diagonalSurface S)).map (homOfLE (Nat.le_succ n)).op))
      ((HomologicalComplex.single (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) (.up ℤ) 0).obj
        (c.reduction.ordinary.obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)))))
    (φ : c.scalar.model.E.obj (c.reduction.ordinary.obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))) ≅
      g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))))
    (hφ : (constant (diagonalSurface S)).map (supportedIntegralUnit S) ≫
        c.reduction.model.adjunction.unit.app
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)) ≫
        c.reduction.forget.F.map ((c.scalar.ordinaryAdjunction.homEquiv _ _) φ.hom) =
      integerGenerator (diagonalSurface S) (Rrings l (diagonalSurface S))
          c.reduction.forget ≫
        c.reduction.forget.F.map (scalarGenerator l E (diagonalSurface S) ≫
          (WeilConjectures.SemilinearSections.res
            (coefficientSystemMap l E (diagonalSurface S))).map
              ((g.ordinaryAdjunction.homEquiv _ _) p.iso.hom))) :
    ∃ s : c.scalar.T.obj
        ((DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Rrings l (diagonalSurface S))) 0).obj
          (c.reduction.ordinary.obj
            ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)))) ≅
        (SpTowerShriek.push l E b g).obj
          (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))),
      diagonalExtendedUnit l E c ≫ (c.scalar.T.map a.hom ≫ s.hom) = unitArrow l E p := by
  have := isIso_scalarSingleCounit_app l E c _ hM
  refine ⟨asIso ((scalarSingleCounit c).app _) ≪≫
    (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
      (Arings l E (diagonalSurface S))) 0).mapIso φ ≪≫
    (g.push.singleFunctorCompRightDerivedFunctorIso.app
      (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))).symm, ?_⟩
  have key := scalar_reduction_source_eq l E c hc _ _ a ha _ _
    (scalarSingleCounit_transpose l E c _ _ hM φ.hom)
    ((constant (diagonalSurface S)).map (supportedIntegralUnit S)) _ hφ
  have hu := coefficient_unit_single l E g p
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] at key
  unfold diagonalExtendedUnit
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% key, ← c.scalar.T.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_assoc, ← hu, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

end AlgebraicGeometry.ProEtale.SpTowerClasses
