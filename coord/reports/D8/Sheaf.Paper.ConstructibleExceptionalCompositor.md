## What changed

Proved `WeilConjectures.compactSupportTerm_hom_finite` in its own new module: use integral
residue Tor, the existing uniform compact-support bound, finite-ring étale origin,
constructible internal Hom and finite-type direct-image finiteness. The source scheme
for the direct image need not be separated. Transport the finite Hom witness back by
scalar adjunction. All auxiliary lemmas in this new module are proved and private. The point-unit comparison
comes from the adopted `CompositionPairing` module and uses only the equivalence
between point sheaves and modules; no duality or trace result is used.

The normalized integral support equality is proved by projection naturality, a Milnor
finite-group argument and functor extensionality. The formal exceptional-mate argument
proves the Hom formula, pasted counit, component uniqueness, shift compatibility and
right refinement equation. The main theorem combines these with the new geometric
left-compositor coherence lemma.

Moved the existing public data into `ConstructibleExceptionalCompositorData` without
changing names, signatures or definition bodies; the item publicly re-exports it. This
breaks the import cycle required by the separate geometric left-coherence statement.
See `coord/changes/constructible-exceptional-compositor-data.md` for consumer checks.
No adopted source-library declaration is changed or removed.

## Proved and sorry left

Original holes: two. Closed `WeilConjectures.constructibleIntegralSupport_eq` and
`WeilConjectures.ConstructibleExceptionalCompositor.constructibleExceptionalCompositor`.

Added one hole:
`WeilConjectures.ConstructibleExceptionalCompositor.constructibleLeftCompositorCoherence`
(node `lem-sf-constructible-left-compositor-coherence`). It isolates the canonical left
compact-support construction, its coefficient equations, left refinement square and
shift equation. The parent proves the exceptional Hom/counit/uniqueness/right
refinement/shift consequences by actual Lean mate calculations. This is a decomposition
of the main theorem, not a claim that the remaining geometric coherence is proved.

The new finite-Hom lemma is proved, with zero holes. Every private helper is proved.
The packet therefore closes two holes and adds one, net one. The new finite-Hom
module passed `lcompile.py` with no holes. The integral data proof passed
`lcompile.py`; its projection extraction was then refined to avoid expensive
definitional conversion during a fresh import-order compile.
The import-order compile and delivery checks are recorded by the delivery tool.

## No longer needed

All original public imports remain exposed through the data-module re-export.
The original unit realization and all its named steps remain in place.
The parent DAG no longer directly cites the geometric proof dependencies
`CompactifiedTowerComparisons`, `FiniteStructuralMapsCommShift`,
`IntegralRealizationShiftCoherence`, `PbcRationalTransport` and
`StageSystemFunctorDescent`. Their geometric content remains needed by the new
left-coherence lemma and is retained in its DAG proof dependencies. The still-unproved
lemma imports only the data needed by its signature. No corresponding mathematics
is withdrawn, and no module is pruned globally.

For finite Hom, the already proved adopted source-library internal-Hom and direct-image
finiteness results replace a new spectral-sequence development. No new Ext finiteness
hole or module is required. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The integral equality requires joint injectivity of normalized derived-limit
projections. Finite evaluations of general derived systems are not faithful. The
proof supplies the missing finite-Hom/Mittag–Leffler argument explicitly instead.

The geometric left-compositor coherence is distinct from the formal mate consequences;
the original module mixed the data needed to state that result with the parent theorem.
The data refactor exposes this dependency without changing mathematical statements.
The original DAG's mate steps are now actual proofs, using existing Mathlib conjugation
and the adopted source-library adjunction shift instance.

## New nodes

`lem-sf-compact-support-term-hom-finite`: finite shifted Hom into a positive finite
compact-support term. Its module is completely proved.

`lem-sf-constructible-left-compositor-coherence`: the remaining geometric left coherence
step, with its full source proof in words. It contains the packet's only `sorry`.

`def-sf-constructible-exceptional-compositor-data`: attaches the moved published data and
the proved normalized integral realization interface, allowing the geometric lemma to
be imported without a cycle. Existing finite-map attachment is moved with it.

Change record: `coord/changes/constructible-exceptional-compositor-data.md`.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
