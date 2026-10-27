## What changed

Filled all five proof holes in `Sheaf.AlgebraicGeometry.ClopenStratificationModels`.
All existing public declaration signatures, public imports, definitions and visibility
are unchanged. Two proved private helpers supply the intrinsic composite-pullback
isomorphism and fixed-module finite local constancy under inverse image.

The geometric restriction is the published `Stratification.pullback`, after adding
the supplied constructibility fields. The union composes the original immersions,
proves retrocompactness from the closed component range, and checks disjointness
and coverage directly. The model assertions retain the exact specified schemes,
base-changed or original cover objects, and module models.

The shorter coefficient argument uses the existing constant-module equivalence and
its canonical pullback comparison. Full faithfulness lifts fixed-module compositors
to isomorphisms of the specified intrinsic tensor pullbacks. For constructibility,
the existing encoding theorem handles finite-stalk/model conversion and positive
strata on the empty scheme. The reverse direction explicitly reindexes the finite
sigma type by `Fin` of its cardinality. No new statement or definition is needed.

Updated the node's proof, proof dependencies and proof origin to match the Lean;
removed only obsolete entries from its top-level tool approvals. Compiled the file
through `lcompile.py`; delivery additionally runs its own compile and preflight.

## Proved and sorry left

Closed 5 of 5 original holes, all in namespace `AlgebraicGeometry.Scheme`:

- `clopenStratification_pullback`
- `clopenStratification_union`
- `clopenStratification_pullback_models`
- `clopenStratification_union_models`
- `isConstructibleProEtaleModuleSheaf_iff_clopen`

All realize `lem-pur-clopen-stratification-models`. Added 0 holes and split off 0
statements. No `sorry` remains in the delivered module. Existing dependency proofs
are reused without modification. This is a proof of the item from existing library
declarations, not a claim that every transitive dependency is closed.

The proof includes empty component schemes, empty strata, the empty partition of
the empty scheme, arbitrary finite index universes, and the zero coefficient ring:
no step chooses a point. Zero-cardinality sigma indexing is accepted in the
fixed-module predicate and its published comparison supplies a positive intrinsic
stratification when required.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleOrdinaryPullbackComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse`
- `Sheaf.Paper.ProEtaleFiniteModelStalks`

The first three are replaced by the canonical constant-module pullback encoding
and fixed-module compositor; their corresponding direct node dependencies
`def-sfb-proetale-ordinary-pullback-comparison`,
`lem-trf-constant-coefficient-composition`, and
`lem-sfb-proetale-object-inverse-image-restriction` are removed. Direct dependencies
`lem-sf-proetale-lisse-finite-models` and
`lem-weil-pbc-proetale-finite-model-stalks` are subsumed by the published
constructibility encoding comparison. Those two remain used transitively inside
that comparison and are not claimed to be globally unnecessary.

`lem-weil-pbc-constructible-open-restriction` is no longer a separate direct proof
dependency: `Stratification.pullback` already supplies constructible preimages.
Retained the original public imports and their exported interface. No module or
upstream declaration is withdrawn, and no global pruning claim is made about
other consumers of the removed imports.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect dependency signature was found. The original plan
was longer than necessary: the already-proved constant-module encoding comparisons
supply the intrinsic coefficient compatibility and the finite-stalk/model bridge.
The direct use of the still-holed general ordinary comparison is unnecessary for
these non-normalized existence assertions. The existing positive-stratification
comparison also removes the need to repeat the empty-scheme construction here.
The unit record has no realized steps or statement nodes bypassed by this route.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
