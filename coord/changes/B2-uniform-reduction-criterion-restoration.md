# AlgebraicGeometry.Scheme.pbcUniformReductionCriterion

## Reason

Restore the missing module from quarantine/Sheaf/Paper/PbcUniformReductionCriterion.lean,
as assigned by coord/rework.tsv (5f7b33eac, 2026-10-20). Its archived complete proof
compiles against the current dependency sources. The repair restores both declarations,
their original Lean attachment, and the complete recorded proof dependency route.

The only edit within the archived source is a shorter proof of the private
etaleComparison_reflects_isGE helper, replacing an explicit homology-comparison and
faithfulness calculation by the existing proved exact-functor reflection lemma.
All public and private signatures, definitions, imports, and docstrings are unchanged.

## Old

The file is absent from lean/. Its archived public signatures are:

```lean
theorem pbcUniformReductionCriterion_backward (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    PbcUniformReductionProfile T (pbcIntegralDatum l E) K →
      (PbcHasUniformConstructibleReductions T (pbcIntegralDatum l E) K ∧
        PbcHasCompatibleEtaleOrigins T (pbcIntegralDatum l E) K)

theorem pbcUniformReductionCriterion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (PbcHasUniformConstructibleReductions T (pbcIntegralDatum l E) K ∧
      PbcHasCompatibleEtaleOrigins T (pbcIntegralDatum l E) K) ↔
      PbcUniformReductionProfile T (pbcIntegralDatum l E) K
```

## New

The exact same signatures and their complete archived proofs are restored under
lean/Sheaf/Paper/PbcUniformReductionCriterion.lean. The private reflection proof ends:

```lean
  apply (DerivedCategory.isGE_iff X a).2
  intro q hq
  exact G.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    ((DerivedCategory.isGE_iff _ a).1 h q hq)
```

No definition changes. No new holes. The revised complete module compiled in
11.0 seconds against the current dependency source overlay.

## Users

Source scans of lean/ and quarantine/ find precisely these two direct consumers.
Their archived uses of the restored signatures have been read. Neither signature
changes, so neither consumer requires adaptation. The two corresponding DAG parents
retain their proof dependency on lem-weil-pbc-uniform-reduction-criterion.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PbcConstructibleReductionCriterion (quarantined) | unclaimed | Both applications have identical types; no adaptation. |
| Sheaf.Paper.PbcUniformCompleteTriangulated (quarantined) | unclaimed | The equivalence in hPredicate has identical type; no adaptation. |

There are no source-library edits, no forced adaptations, and no target type changes.
The node already records the restored declarations and the proof route used here,
so its attachment and dependencies need no edits. The lower-bound reflection uses
an existing proved API inside the same elementary argument.

## Status

landed 20261020T235543-L-1188850 2026-10-20 (merge of deliver/B2/Sheaf.Paper.PbcUniformReductionCriterion)
