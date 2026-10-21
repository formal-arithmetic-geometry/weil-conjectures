# Sheaf.Paper.CompletedDirectImageLimits

## Reason

Prove three session-start holes and retain the seeded ordinary-mate proof, while
preserving every existing declaration signature
and public import. The normalization predicate is definitionally factored
through the same equation over general abelian categories. Preflight requests a
change record because its conservative command check notices `open`, local attributes, and local options.
The added K-injective preservation fact is a private theorem. It is registered
only within the section containing the private normalization lemma, with no
module-wide or global registration.

## Old

The original module header commands were:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
```

There was no `evaluationPreservesKInjective` helper, no local registration of that
helper, and no local irreducibility annotations or derived-comparison sections.
All 25 original public signatures are retained verbatim. The sole changed
definition body is `IsCompletedReductionPullbackComparison`, described below.

## New

The corresponding header commands are:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
```

The private proof helper is:

```lean
private theorem evaluationPreservesKInjective (B : Type*) [Category B] [Abelian B]
    (n : ℕᵒᵖ) : ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).PreservesKInjectiveComplexes :=
  ⟨fun J _ ↦ evaluationMapKInjective B J n⟩

```

The registration is scoped exactly as follows:

```lean
section NormalizedTowerEvaluation
attribute [local instance] evaluationPreservesKInjective
-- The proved private normalizedTowerEvaluation theorem only.
end NormalizedTowerEvaluation
```

The public coefficient constructions, the public evaluation predicate, and all
later proofs lie outside that section. The public evaluation-existence theorem
applies the private normalization theorem without introducing another instance.
This keeps a broad evaluation-instance search out of the rest of the module and
avoids extra instance conversions in public definition bodies.

The transition-proof section also uses this local attribute:

```lean
attribute [local irreducible] pbcScalarAdjunction proEtaleRingModuleAdjunction
```

Individual proofs use local backward-transparency options. The derived-comparison
section uses `synthInstance.maxSize 2048` and `maxRecDepth 2048`. These are scoped
elaboration settings; no kernel check or compile limit is disabled or raised.
The evaluation instance is scoped to the private normalization lemma. Derived evaluation detects
isomorphisms by a proved private lemma, specialized in the original tower
projection proof; this avoids repeating the homology conversion on the large
coefficient categories. All 25 original
signatures are textually identical. The completed coefficient constructions,
comparison normalizations, and five original theorem statements are unchanged.
There is no target or definition meaning change requiring a renewed statement
review. All added imports are proof-only; all original public imports remain.

### Comparison predicate

Previously `IsCompletedReductionPullbackComparison d f τ` spelled out the
ordinary-complex counit equation directly. Its body is now the specialization of
the new public definition `IsDerivedReductionPullbackComparison`. The latter's
body is exactly that equation with its functors and counits as parameters:

```lean
∀ K, M K →
  η.hom.app (DerivedCategory.Q.obj K) ≫
      LG.map (P.mapDerivedCategoryFactors.hom.app K) ≫
        reductionComplexCounit G LG εG ((P.mapHomologicalComplex (.up ℤ)).obj K) =
    H.mapDerivedCategory.map (reductionComplexCounit F LF εF K) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K)
```

The parameters are respectively the two ordinary reduction-tower functors,
ordinary module pullback, ordinary tower pullback, the ordinary comparison iso,
the two actual derived reduction functors, and their actual counits. `M` is
K-flatness over the completed source coefficient sheaf. Thus unfolding the generic
predicate and the already existing aliases recovers the original body by
reflexivity: every quantifier, equation, direction and normalization is unchanged.
In particular the generic theorem's smaller flat-term resolving class is not
introduced into the public predicate.

This factoring is necessary for compilation: spelling out the concrete formula
again at the existence theorem made kernel instance conversions exceed 60 seconds;
the refactored complete module compiled in 46.2 seconds. The generic definition is
public because a private declaration cannot occur in a public definition body.
It introduces no instance, choice, axiom, sorry, or changed target meaning.

The proof-only `import all Sheaf.Paper.AdicCoefficientDatum` also loads that
module’s existing generated counit equation. With only the ordinary transitive
import, simplifying `reductionComplexCounit` generated a second equation with the
same name, which conflicted when `QuotientCornerFrobeniusStructures` later loaded
the original private interface. The explicit private-interface import reuses the
existing equation; it changes no public import or declaration.

## Users

`tools/downstream.py Sheaf.Paper.CompletedDirectImageLimits --uses
IsCompletedReductionPullbackComparison` reports nine downstream modules and no
consumer mentioning that predicate. The helper instance remains private. No consumer requires an adaptation. Current holders are
recorded below; no held consumer is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedDirectImageLimits | P5 | Proofs and definitional predicate factoring. |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | No signature or instance change. |
| Sheaf.Paper.CompletedProjectionCoherence | unclaimed | No signature or instance change. |
| Sheaf.Paper.CompletedPullbackUnitTower | V1 | No signature or instance change. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | No signature or instance change. |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | No signature or instance change. |
| Sheaf.Paper.ProEtaleConstantReductionTower | XRd43db5c7223de0ad | No adaptation. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | No adaptation. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | No adaptation. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | W3 | No adaptation. |

## Validation

The complete module compiled in 38.2 seconds with the private-interface import.
All nine consumers compiled without edits. A temporary example proved equivalence
to the original predicate formula verbatim by `Iff.rfl` (33.9 seconds). It and all
unchanged consumer copies were removed from the delivery packet.

The seed snapshot already contained T1's ordinary-mate proof, while the current
shared snapshot contains a sorry at that declaration. This packet retains and
compiles the seeded proof as well as the three newly completed proofs. It does not
restore the seed snapshot's review metadata: the node keeps the current metadata.

## Status

landed 20261021T012421-L-2187815 2026-10-21 (merge of deliver/P5/Sheaf.Paper.CompletedDirectImageLimits)
