## Worker report

Item: lem-trf-space-etale-source-atlas-detection. Group Q88, stage 1, 2026-10-22.

Files written: dag/nodes/sec-trace-formula/lem-trf-space-etale-source-atlas-detection.json, citations.json, and this report. The required search command also wrote searches.jsonl in this sandbox. The item is split with its statement and statement dependencies unchanged. No repository files, Lean files or launcher files were written; no compiler or git commands were run by the worker.

## New nodes

None. Zero Mathlib leaves. The necessary scheme source-descent lemma already exists as lem-trf-etale-descent-through-source-cover; representability, composition, base change, and scheme-map tests already exist as lem-trf-space-representable-etale-scheme-tests. Creating either again would be a duplicate.

## Attachments

None. The project-source search in lean/WeilConjectures for the exact blueprint id, AlgebraicSpace, chartwise, and etale/source/atlas wording gives no declaration stating all three clauses. Some unrelated occurrences of chartwise concern blowups and section gluing. A declaration in lean/Sheaf for scheme source descent is already attached to its own dependency and is not an attachment for this algebraic-space item.

## WANTED

None. All sources needed here are in literature/stacks-project.

## Audit and changes

The imported node had an empty proof. Read spaces-properties.tex, lemma-etale-over-space (Tag 03EC), especially its proof of (3), lines 2019-2092; lemma-etale-local (Tag 03FS), lines 2112-2162; and descent.tex, lemma-etale-etale-local-source (Tag 036W), lines 6950-6963. The item agrees with 03EC(3) and 03FS(1) iff (2); clause (2) makes explicit the same pullback argument when the covering source is an algebraic space. Stacks omits some equivalent-condition details, so the proof writes them rather than treating the source as a scheme. No statement dispute or source error was found.

Read dag/chapters/sec-trace-formula.json and dag/units/sk-i-curve-zero.json, and retained the historical ancestry recorded in blueprint.from. This is the elementary geometric infrastructure of the polarized-descent helper, not a new proof of the contracting-correspondence unit. No route, unit, chapter, or target was changed. The blueprint ancestor command returns lem-trf-local-term-locality. Whole-blueprint searches for `etale source`, `03EC`, and `03FS` each returned zero blueprint nodes. DAG searches for the tags and labels found the existing scheme-descent and scheme-test nodes used here, the parent chartwise-permanence item, and unrelated geometric applications. The parent depends on this item and is deliberately not cited, avoiding a cycle.

Mathlib searches were run with the required msearch.py command: LeanFinder in two phrasings, Loogle, grep, and LeanSearch. Every new record copies an actual searches.jsonl record with its exact tool and query. The inherited searches are retained as historical records. Loogle and grep returned zero hits. Both LeanFinder phrasings and LeanSearch returned scheme/ring results, including Etale.of_comp and scheme base-change stability, not algebraic-space source-cover detection. Read the current local Mathlib/AlgebraicGeometry/Morphisms/Etale.lean:39-157: Etale.of_comp cancels the other arrow and has a scheme target. Thus those hits are not a one-line specialization of the item. The inherited unavailable LeanSearch attempt remains labelled unavailable; the new successful attempt is recorded separately.

Nothing remains unfinished in this one-level split. Its cited unsplit helper is pre-existing work for a later worker, not a new hidden lemma.

## Not duplicates

No new nodes. The existing lem-trf-etale-descent-through-source-cover concerns three schemes; the item concerns maps to algebraic spaces and arbitrary algebraic-space covering sources. The existing lem-trf-space-representable-etale-scheme-tests gives representability, permanence, and opposite-arrow cancellation, not source-cover descent. The broader parent lem-trf-space-chartwise-etale-permanence cites the item and cannot be substituted for it.

## Review by Q88

I read the sources listed above and every cited node's statement, rather than using their proofs as interfaces. The statement was kept verbatim: in particular, R is not assumed to be a scheme, and no quasi-compactness, separatedness, Noetherian, or finite-type condition was added. There are no new nodes whose hypotheses or definitions need a separate audit.

Step 1 uses lem-trf-space-representable-etale-scheme-tests for representability of both scheme-source maps and for the surjective etale transformation induced by p. Its statement expressly gives these clauses. The two test objects A and B are therefore schemes, before the scheme descent theorem is invoked. The pullback identification is written on compatible pairs, so no unproved comparison lemma is hidden in the word identification. The scheme-test definition in def-trf-algebraic-space says exactly that B -> A is surjective etale and B -> T is etale. The statement of lem-trf-etale-descent-through-source-cover then applies to h=A -> T and p=B -> A with all three objects schemes. Its explicit lack of separation, finite-type, and Noetherian hypotheses was checked. Testing arbitrary T -> Y, including non-etale tests, is essential here; testing only an atlas would have been circular. The final conclusion is precisely the scheme-test definition of representable etale.

Step 2 uses lem-trf-space-fibre-products-etale-covers only for existence and the universal property of R times_X h_W, which its statement gives. The fact that this pullback is a scheme with a surjective etale projection to W follows from the actual representability and scheme-test hypotheses on p, via def-trf-algebraic-space. No atlas or scheme hypothesis on R is needed. Its other projection to R is the base change of a, hence representable etale by the explicitly stated arbitrary algebraic-space base-change clause of lem-trf-space-representable-etale-scheme-tests. That same statement supplies composition with f p. The equality p b = a h_d comes from the fibre-product universal property, and Step 1 applies to f a and the actual surjective etale scheme map d:V -> W. The proof therefore uses only a previously proved clause of the item, not a new node restating this clause.

Step 3 uses def-trf-algebraic-space for existence of a representable surjective etale scheme atlas. The forward direction is evaluation of the definition of chartwise etale at that atlas. The reverse direction applies Step 2 with R=h_U. Its use of Step 2 is internal assembly, not a self-dependency in the DAG. citations.json contains verbatim statements for all eight step/node pairs, including the atlas-existence and scheme-test sentences.

I checked delivery-errors B1-B10: no new statement-only nodes, duplicate notions, undefined data, fabricated searches or unsupported Mathlib matches were introduced. I checked C1-C8: all non-elementary facts are stated by the cited nodes, the scheme tests are arbitrary, the parent is not cited, and no off-unit tool is needed (all proof dependencies share the item's unit). I checked D1-D5: the proof carries the pullback and descent argument; no clause was moved into a new node and the equivalence omitted by Stacks is explicitly assembled. For E1-E7 I checked the precise pullback base X, arrow orders, representability before introducing a representing scheme, and both descent hypotheses. Every proof step is under 1000 characters, so none hides a long unreviewed auxiliary claim.

Small cases: identity covers reduce to the assumed etaleness; an empty surjective source forces its scheme target empty, and the scheme descent statement includes this case. The empty algebraic space has an empty scheme atlas, so clause (3) has no existence exception. An arbitrary non-scheme R is handled by pulling back p, rather than pretending R itself is representable. If surjectivity were removed, the empty cover of a nonempty W would make the descent inference invalid, confirming that the used hypothesis is essential. No correction to the source or item was necessary; the repair made during writing was to include the actual pairwise pullback comparison and to make the citations quote the complete relevant statements, covering every clause used.
