## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionInjective` by a complete
Lean proof from the structure-sheaf global-sections comparison. The existing declaration's
signature and visibility are unchanged. Its docstring, proof and updated DAG use only the structure-sheaf part and the faithful
geometric fibre (the second reading replaced the outdated longer docstring plan).

Added `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedGlobalSections`, stating the
canonical bijectivity B -> Gamma(V,O). Its proof is left to the next item. The theorem gives
an actual property of an existing canonical ring map; it chooses no data or witness.
Its docstring and node expand the injectivity detail omitted by the source.

In the item, added private proof imports of the new module,
`Sheaf.RingTheory.DepthLeSupportDimension`, `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`,
and `Mathlib.RingTheory.MvPowerSeries.Inverse`. The two original proof imports were removed.
The new module imports the existing declarations named by its proof plan.

The complete Lean assembly proves that the punctured spectrum of A is nonempty using
depth <= dimension; that Gamma(V,O) is local using the surjectivity half of the comparison;
that V is connected using the proved idempotent criterion; and that equality after pullback
implies equality on a geometric fibre using explicit pullback lifts. Faithfulness of the
already proved geometric-fibre functor finishes the proof. No cover connectedness,
nonempty-cover assumption, or normality is added. The unit's 0EY9 full-faithfulness input
and all its realized steps remain unchanged.

## Proved and sorry left

Closed:
`AlgebraicGeometry.Scheme.finiteEtale_powerSeries_punctured_section_restriction_injective`
(node `lem-sbc-power-series-punctured-section-injective`). The item's module has no sorry.

Added and left:
`AlgebraicGeometry.Scheme.bijective_powerSeries_punctured_globalSections`
(node `lem-sbc-power-series-punctured-global-sections`). Its entire proof is `:= by sorry`.

This is a decomposition: one upper hole closed and one strictly narrower structure-sheaf
comparison hole added, net zero declaration holes before accounting for pruned imports.
The lower statement contains no covers, no cover morphisms, and no pullback functor.
The passage from that comparison to the original hom-set injectivity is fully checked Lean.
The faithful fibre theorem and depth-support-dimension theorem already have complete proofs.
No other sorry is added by this delivery.

## No longer needed

Removed direct imports from the item:
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction` and
`Sheaf.RingTheory.FlatLocalDepthFormula`. Hartogs is still needed by the global-sections
comparison and is imported there: it is not pruned from this branch.

The flat local depth formula is unnecessary for this route. Its associated-prime consequence
is obtained directly from the existing flat associated-prime base-change theorem and the
fact that B/pB is a power-series domain. The existing depth bound by dim(A/p) excludes m_A.
The node `lem-weil-pbc-flat-local-depth-formula` is removed from the item's proof dependencies.
These source modules no longer occur in the item's import branch:

- `Sheaf.RingTheory.AnnihilatorElementFlatBaseChange`
- `Sheaf.RingTheory.DepthOverQuotientRing`
- `Sheaf.RingTheory.FlatLocalDepthFormula`
- `Sheaf.RingTheory.FlatLocalDepthReduction`
- `Sheaf.RingTheory.FlatModInjective`
- `WeilConjectures.Mathlib.RingTheory.Filtration`

The corresponding nodes are `lem-weil-pbc-annihilator-element-flat-base-change`,
`lem-weil-pbc-depth-over-quotient-ring`, `lem-weil-pbc-flat-local-depth-formula`,
`lem-weil-pbc-flat-local-depth-reduction`, and `lem-weil-pbc-flat-mod-injective`.
This is pruning for this item, not a claim that other targets no longer need these modules.
The source Filtration module is also unnecessary here; Mathlib's Krull-intersection theorem
is named directly by the lower node. The completion comparison for finite locally free
bundles, its internal Hom application, and formal-etale uniqueness on all thickenings are
not needed in this proof. Those steps had no separately named dependency modules to prune.

## Where the brief, the DAG or earlier work was wrong

The parent node's first step was considerably larger than the two stated dependencies:
neither the Hartogs restriction-adjunction theorem nor the flat local depth formula by itself
states the canonical global-sections comparison or its formal-completion injectivity.
The new node isolates just that first structure-sheaf comparison, with a source and complete
proof in words, instead of introducing the entire internal Hom completion framework.

The Stacks source was read at https://stacks.math.columbia.edu/tag/0EY9
(`pione.tex`, `lemma-fully-faithful-power-series-over-depth2`). Its first comparison
B -> Gamma(V,O) -> B is precisely the lower lemma; the source explicitly omits the
injectivity detail. The complete detail follows the parent's associated-point argument,
now citing the existing associated-prime base-change, depth bound, Krull intersection,
and associated-localization detection nodes.

Mathlib searches were run through msearch.py, as recorded in searches.jsonl. For the new
statement: LeanSearch returned HTTP 500 and is recorded as unavailable; Loogle
`AlgebraicGeometry.Scheme.Hom.appTop, Function.Bijective` returned no hits; grep
`powerSeries.*(appTop|globalSections)|punctured.*(appTop|globalSections)` returned no hits.
Repository searches found no existing declaration of the comparison, and blueprint searches
for global sections and power series found no duplicate. No signature correction or forced
adaptation is needed.

Edge cases checked: nonreduced A is handled by associated primes, not generic points alone;
A of dimension zero cannot satisfy the depth hypothesis; the zero ring is excluded by
IsLocalRing's Nontrivial field; empty P or Q causes no exception to the geometric-fibre
extensionality argument; d=0 is outside the unchanged hypothesis hd. V is never assumed
affine, integral, normal, or connected: its connectedness is proved in the delivery.

## New nodes

`lem-sbc-power-series-punctured-global-sections`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-power-series-punctured-global-sections.json`,
records the canonical bijection B -> Gamma(V,O), Stacks 0EY9's structure-sheaf comparison.
It inherits the parent's chapter, unit and nearest blueprint ancestor, with the exact
local-computation sentence and the intervening node chain. Its proof uses existing Hartogs,
flat constants, associated-prime base change, depth-dimension, Krull intersection and
associated-localization detection statements, then the elementary inverse argument.
One new module and one new sorry, strictly below the cover-morphism assertion.
No change record is needed: no existing statement, definition or public import changes.

## Second reading by V2

1. Compared both delivered modules with the repository using diff. The existing theorem's
   signature, universe, visibility and public imports are byte for byte unchanged. The other
   module is new, with no definitions or changed interfaces. No change record is required.
2. Compiled both modules in dependency order through lcompile.py. The item has no sorry;
   the sole new sorry is the named global-sections comparison listed above. No forbidden
   declaration or hollow definition occurs. Scratch-copy axiom probes show only propext,
   Classical.choice, Quot.sound and sorryAx (from the explicitly reported lower theorem).
3. Read Stacks 0EY9's displayed comparison and independently checked its omitted injectivity
   argument: associated primes pB specialize to pB+I in V, and Krull intersection at these
   zero-section points kills the formal kernel. Flat associated-prime base change applies
   because B/pB is a power-series domain; no reducedness assumption is used. The statement
   is strictly narrower than hom-set injectivity and states a property of a canonical map,
   choosing no data. Checked nilpotents, empty covers, excluded depth-zero local rings,
   and d>0. Fresh Loogle (appTop plus surjectivity), Lean Finder (global sections on formal
   power-series opens) and repository searches found no existing comparison. The lower
   theorem needs substantial formal geometry and cannot be closed by a short local repair.
4. Read the argument downward: the global-sections comparison gives a local section ring,
   hence connected V; a geometric point of the punctured section and faithful fibre then
   detect equality. The pullback lift is the actual pointwise reduction. The new module's
   private imports are the dependencies of its remaining proof plan; the item's proof
   imports supply the comparison, dimension bound, idempotent criterion and local
   power-series instance. All removed old dependencies are recorded above: Hartogs moves
   to the lower comparison; flat local depth and its six listed module imports are pruned
   from this branch. Read sk-prop-input-spreading.json: its realized lists are empty, and
   its stated 0EY9 full-faithfulness route remains in place. No unit step is bypassed.
5. Compared the node records with the Lean declarations and actual proof. The parent's
   updated proof/dependencies describe precisely the connectedness and faithful-fibre
   route. The new node has the exact Lean signature, complete natural-language proof,
   source, dependency union, searches, creation record, blueprint ancestry, chapter and
   unit. Existing node changes are confined to proof, proof_deps and proof_origin.

Changes in this reading: replaced the item's stale internal-Hom-completion docstring
with the actual connectedness/fibre proof, and appended this independent review. No proof
term, declaration signature, definition, import or dependency was changed. Verdict: valid
one-for-one decomposition with the reported branch pruning, not a net hole closure.
