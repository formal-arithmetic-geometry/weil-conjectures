# WeilConjectures.integralOpenTensorQuotientModel

## Reason

The proof introduces generic section-variable commands around private categorical
helpers. This record documents their scope for the interface check, as in the
landed M6 ringed-open scalar proof. Every existing public declaration signature,
public import and definition body is preserved. The item theorem's proof is the
only existing declaration body changed. New proof imports are private. There
are no new public instances, attributes or definitions.

## Old

The original universe command was:

```lean
universe t u
```

The `ExactSquares` helper section and generic categorical helper variables
were absent. The existing concrete variable command is unchanged:

```lean
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X V : Scheme.{t}} (j : X ⟶ V) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)
```

## New

```lean
universe t u c v r
```

The same concrete variable command remains verbatim. The additional universes
and generic sections in the item bind only private proved helpers for exact-square
localization and conjugation by isomorphisms. Horizontal ring-map evaluation and
section-preserving pushforward helpers are private in the new comparison module.
A private structure packages the generic comparison and its generator proof.
The generator formula is folded in a private predicate; private partial
applications retain its concrete coefficient parameters without repeatedly
expanding the statement. Native projections supply universes and site instances
explicitly. The six private aliases ending in the class proposition `Nonempty`
are marked `instance_reducible`, as Lean recommends for such definitions.
The item uses abstract reassociation lemmas for the
final seven-map and six-map composites. Local irreducibility attributes control
elaboration inside these files. The ordinary comparison is constructed
from existing data and proved adjunctions, without choosing data from an
unproved existence statement. The public theorem signature is byte-identical
to the repository version; there is no change to its hypotheses or conclusion.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralOpenTensorQuotientModel | M7 | The proof is filled from two genuine intermediate statements. |
| Sheaf.SixFunctors.IntegralOpenReductionQuotientSquare | unclaimed | Public signature and imports unchanged; no adaptation. |

These are the item and its sole direct Lean importer. No shared definition,
statement, instance, simp/ext attribute or public import has changed, so no
consumer adaptation is required. The three new statement modules have their own
DAG nodes and are proof dependencies only.

## Status

landed 20261027T050623-L-245985 2026-10-27 (merge of deliver/M7/Sheaf.SixFunctors.IntegralOpenTensorQuotientModel)
