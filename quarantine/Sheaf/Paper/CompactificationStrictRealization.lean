/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.CompactificationCompletedRealizationData

/-! # Strict proper/open reconstruction of the recorded compact-support action -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactificationCompletedRealization
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Proper/open reduction identifies the actual strict tower with the recorded
compact-support tower, before taking a total limit.
Source: blueprint sk-prop-sf-pf-reduction, proof of lem-fix-operation-reduction,
paragraph 2; Stacks 0A07, 0941, 0943
(blueprint: lem-fix-compactification-strict-realization).

Proof: choose the coherent coefficient reduction calculus. For a constructible K, put H = j!K.
The strict open reduction comparison identifies its finite reductions with j! of the reductions
of K, and identifies its completion unit. Finite open extension preserves both constructibility
and the common cohomological interval; thus H is complete and constructible. Apply proper direct
image to its strict reduction comparison. Perfect coefficient projection for the proper factor
commutes with quotient transitions, so this gives an isomorphism of derived strict systems, not
a lifting of unrelated evaluation isomorphisms. Restriction of scalars gives beta into the
recorded compact-support tower. The proper direct-image/total-limit comparison shows that its
source is complete. The representative independence comparison for compact support gives gamma
to its specified total limit. Its finite projections are the scalar-adjunction mates defining
the recorded finite reduction isomorphisms; this gives the first identity. Taking the limit of
beta and composing with the actual reduction unit therefore has the projection normalization of
the canonical qcqs realization. Uniqueness in that normalization gives the second identity.
Evaluating the strict proper/open comparison gives the last identity, by the unit projection
formula and naturality of finite scalar extension. Every comparison is constructed on the strict
quotient diagrams before localization and before total limit. -/
theorem strictRealization [QuasiCompact c.i] :
    ∃ S : CoefficientDerivedSystemCalculus l E Y,
    Nonempty (CoefficientDerivedSystemCoherence l E Y S) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E c.Z
        ((openExtension (completed l E) c.i).mapDerivedCategory.obj K.obj)) ∧
    ∃ (β : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⋙
          strictReduction l E Y S ≅
        (sfIntegralConstructible l E X).ι ⋙ supportTower l E c k hl)
      (γ : sfCompactSupportFiniteIntegralFunctor l k hl c E ⋙
          (sfIntegralConstructible l E Y).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ supportTower l E c k hl ⋙
          coefficientConstantTowerLimit l E Y),
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      γ.hom.app K ≫ (coefficientConstantTowerProjection l E Y n).app
          ((supportTower l E c k hl).obj K.obj) ≫
          (supportEvaluation l E c k hl n).hom.app K.obj =
        (coefficientFiniteAdjunction l E Y n).unit.app
            ((sfCompactSupportFiniteIntegralFunctor l k hl c E).obj K).obj ≫
          (scalarReductionDerivedRestriction l E Y n).map
            (sfCompactSupportFiniteReductionIso l k hl c E K n).hom) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      (sfQcqsCompactSupportRealization l E k hl c).hom.app K =
        S.adjunction.unit.app ((image (completed l E) c).obj K.obj) ≫
          (coefficientConstantTowerLimit l E Y).map (β.hom.app K) ≫ γ.inv.app K) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (coefficientConstantTowerEvaluation l E Y n).map (β.hom.app K) ≫
          (supportEvaluation l E c k hl n).hom.app K.obj =
        (strictEvaluation l E S n).hom.app ((image (completed l E) c).obj K.obj) ≫
          (scalarReductionDerivedRestriction l E Y n).map
            ((scalarReductionDerivedExtension l E Y n).map
                ((sfQcqsCompactSupportRealization l E k hl c).hom.app K) ≫
              (sfCompactSupportFiniteReductionIso l k hl c E K n).hom)) := by
  sorry

end WeilConjectures.CompactificationCompletedRealization
