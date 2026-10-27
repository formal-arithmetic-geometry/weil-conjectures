## What changed

Proved `CategoryTheory.NormalizedLimitSquare.normalizedLimitSquareCoherence` in
`Sheaf.Paper.NormalizedLimitSquareCoherence`. The proof constructs the shared normalized Roos
corners from the derived universal property, uses the existing canonical additive Roos
comparison, descends horizontal coherence through localization, cancels the corner
normalizations, and checks strict augmentations by naturality. All arguments work with the
statement's independent site, coefficient and derived universes.

The original dependent `Coherence` record was too expensive for Lean's kernel. Its data is
now an iterated dependent pair `SquareData`, and its nine unchanged equations form
`SquareLaws`; `Coherence` asserts the existence of data satisfying those laws. `augmentation` names the
actual limit-cone map followed by its specified component of the derived unit, and `towerMap` names the
existing termwise transformation with its two-step functors explicitly typed. These are
real constructions. The original statement's hypotheses and mathematical conclusion are
unchanged. See `coord/changes/B9-normalized-limit-coherence.md` for the representation repair.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.NormalizedLimitSquare.normalizedLimitSquareCoherence`.

Holes closed: 1. Holes added: 0. Actual remaining holes in this delivery: 0.
No theorem was split off. All private helpers are proved.

## No longer needed

Removed the proof imports `Sheaf.Paper.ExactProductFunctorRoosChainMaps` and
`Sheaf.Paper.ExactProductFunctorRoosCompatibility`. Their respective nodes
`lem-cbc-exact-product-functor-roos-chain-maps` and
`lem-cbc-exact-product-functor-roos-compatibility` are unnecessary for this proof:
the existing `roosAdditiveComparison` API supplies the exact chain maps, their signed
coordinates and their augmentation identity; horizontal coherence supplies the square.

The proof does not invoke `exactProductFunctorStrictLimit`
(`lem-cbc-exact-product-functor-strict-limit`). It constructs the same normalized
comparison from the generic, proved localization and Roos helpers instead. Its unused public import was removed. The redundant public import of
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients` was also
removed; the proof retains `import all` of that module for its proved private helpers. No module is withdrawn, no source-library
declaration is removed, and these nodes may still be needed by other consumers.

## Where the brief, the DAG or earlier work was wrong

The proposed direct application of `exactProductFunctorStrictLimit` has a maximum-universe
interface, while this item fixes independent coefficient universes. The proof instead uses
the generic Roos universal-property helpers and the universe-independent Grothendieck
helpers already present in the library. No universe or hypothesis was added to the item.
The DAG proof and proof dependencies have been updated to the actual argument.

Profiling identified the original dependent record's kernel type check as the main
performance cost (about eight seconds on the compile server even after naming its
fields). The equivalent dependent-pair representation removes that check. No file was
split to evade the compile limit.

The old docstrings and source record refer to the historical October 15 blueprint proof
path. The current blueprint was read in `literature/blueprint/latest/`; the mathematical
square is the same auxiliary comparison calculation. Existing docstrings are preserved.

Optional lint re-analysis is disabled in the final module because it pushes the full
file over the compile limit. Elaboration, kernel type checking and the delivery axiom
probe remain enabled. There are no changed time limits, skipped kernel checks or split
files. The final Lean source has no diagnostic profiler or heartbeat settings.

`Coherence` is now the proposition `∃ d : SquareData ..., SquareLaws ... d e`; thus its
`Nonempty` theorem states precisely the same existence of normalized comparison data
and every original equation. The old record had no current Lean consumers. The unused
product, limit and base-derived-category parameters of `towerSquare` were removed; its
actual construction and derived tower instances are unchanged.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
