# AlgebraicGeometry.Scheme.Modules.affineRealizationComparison_pullback

## Reason

The old statement inferred the chart arrow through comma-category objects while
its coefficients used the actual fibre-product schemes. With transparency
respected, this presentation fails to synthesize quasi-coherence of the same
fibre-product coefficients. Name the exact original left component as an arrow
between the actual schemes, and construct its original tensor-composition
coefficient map with a named equality transport. The coefficient-map equation
proves equality with the old congrArg transport, using proof irrelevance.

Package the unchanged universal section formula in a proposition structure;
its constructor, projection and proved equivalence expose exactly every original
section equation. Define the cohomology pullback function as the original
cohomologyMap followed by H.map of the adjunct, and prove its evaluation equation.
Use these names in the theorem. No geometric hypothesis, coefficient, section,
cohomology class, or conclusion is added, removed or weakened. Empty charts,
zero coefficients, identity arrows and degree zero remain included.

The proof names the existing uniquely normalized comparison family and proves
its normalization and inverse-comparison equations. All existing comparison and
restriction definitions remain verbatim. The same DAG route proves the square.
No target declaration or adopted source-library declaration changes. The
independent reader should verify the component equations and the target meanings.

## Old

```lean
theorem affineRealizationComparison_pullback {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left] (h : V' ⟶ V) :
    ∃ θ : liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1}
        ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left).obj
        (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V')),
      ( let b := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h
      let ψ : (tensorPullback b.left).obj (affineRealizationCoefficient f G V) ⟶
          affineRealizationCoefficient f G V' :=
        (tensorSectionsComp b.left (Limits.pullback.snd V.hom f)).hom.app G ≫
          eqToHom (congrArg (fun j ↦ (tensorPullback j).obj G) b.w)
      ∀ (U : (Limits.pullback V.hom f : Scheme.{u}).Etale)
        (s : (etaleTensorSectionsSheaf (affineRealizationCoefficient f G V)).obj.obj (op U)),
        θ.hom.app (op U) (ULift.up s) = ULift.up
          (qcoherentPullbackSection b.left _ _ ψ U
            ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b.left).obj U)
            (pullback.fst U.hom b.left) pullback.condition s)) ∧
      ∀ x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q,
        affineRealizationAffineComparison f G q V'
          (Sheaf.H.map
            ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left).homEquiv
                _ _ |>.symm θ) q
            (Etale.cohomologyMap
              ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left
              (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q x)) =
          affineRealizationRestriction f G q h
            (affineRealizationAffineComparison f G q V x)
```

## New

```lean
theorem affineRealizationComparison_pullback {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left] (h : V' ⟶ V) :
    ∃ θ : liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} (affineRealizationChartMap f h)).obj
        (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V')),
      HasQcoherentPullbackSectionFormula (affineRealizationChartMap f h)
        (affineRealizationCoefficient f G V) (affineRealizationCoefficient f G V')
        (affineRealizationCoefficientMap f G h) θ ∧
      ∀ x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q,
        affineRealizationAffineComparison f G q V'
          (coherentEtalePullbackMap (affineRealizationChartMap f h)
            (affineRealizationCoefficient f G V) (affineRealizationCoefficient f G V') θ q x) =
          affineRealizationRestriction f G q h
            (affineRealizationAffineComparison f G q V x)
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AffineComparisonPullback --uses
 affineRealizationComparison_pullback` lists these two modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineComparisonPullback | A4, this assignment | Prove the same square using the typed constructions and the stated normalized pullback theorem. |
| Sheaf.AlgebraicGeometry.AffineCohomologyRawRestriction | unclaimed | Adapt the proof to the exact section formula and cohomology-map equations; both public theorem signatures stay verbatim. |

The DAG citer is `lem-weil-pbc-affine-cohomology-raw-restriction`. Its unchanged
raw-to-ordinary naturality statement uses exactly the same comparison square;
its proof and dependencies are updated in this packet. The root node's
statement_change records the exact old statement and this citer audit.

The consumer uses a proved typed raw-evaluation equation. A direct application
of the expanded old equation incurred a kernel timeout when comparing the two
pullback presentations. The new proof uses the same normalization, derived
evaluation and unit-evaluation declarations, together with the proved generic
restrictionComposition helper. Its section conversion is performed on variable
schemes by explicit cached congruence before specialization. The old proved
raw-evaluation declaration remains untouched; its now-unused import is removed.

## Status

landed 20261026T152140-L-1081818 2026-10-26 (merge of deliver/A4/Sheaf.AlgebraicGeometry.AffineComparisonPullback)
