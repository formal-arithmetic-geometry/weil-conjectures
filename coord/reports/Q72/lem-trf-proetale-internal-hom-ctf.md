# Q72: lem-trf-proetale-internal-hom-ctf

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proetale-internal-hom-ctf.json`: inherited statement, now split in five proof steps; no statement change and no new nodes.
- `citations.json`: verbatim excerpts for every node cited by every step.
- `report.md`: this review and delivery report.

## Attachments

None. I searched the project source for the exact blueprint id and for pro-etale finite-Tor internal-Hom declarations. I also opened WeilConjectures/SixFunctors/Etale/Derived/Stability/Matrix.lean:76 and :314. The etale declaration proves an etale assertion; AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_derivedHom_mapDerivedCategory requires explicit etale finite-Tor inputs and concludes only for their specified pullbacks. This does not state the item for arbitrary intrinsically constructible pro-etale inputs, so I continued the split rather than asserting an exact attachment. No upstream sorry declaration was treated as finished proof evidence.

## WANTED

None. The split follows the existing blueprint route and existing DAG statements.

## Corrections and retained work

The inherited statement is mathematically coherent and was left unchanged: it allows a finite-type scheme without separatedness and asks for ambient pro-etale derived internal Hom of two bounded constructible finite-Tor objects. The inherited Mathlib searches and their results were retained exactly. I also ran four Q72 msearch.py searches, recorded verbatim in searches.jsonl and appended to mathlib_searches where the query was not already present. LeanFinder found light condensed monoidal structures and internal projectivity; LeanSearch found underived sheaf Hom and module-sheaf morphism definitions. I read the light condensed monoidal source and the sheaf-Hom source. Neither states constructible finite-Tor derived-Hom preservation on scheme sites; the exact-name Loogle and Tor/Hom source grep returned zero hits. The two different natural-language phrasings test the same assertion in different words, and no Mathlib leaf is claimed. No new node was necessary.

The proof is not a restatement of the item. Step 1 performs the genuine reduction from pro-etale inputs to etale representatives and transfers the Tor intervals. Step 2 supplies the dimension parameter required by the etale theorem. Steps 3–5 then apply the existing etale preservation theorem, compare internal Hom across sites, and transfer the output back. Empty schemes are included: the structure morphism has the empty fibre and all resulting complexes are zero.

## Not duplicates

There are no new nodes. The existing `thm-sf-hom-ctf` is the etale finite-Tor preservation theorem with a dimension bound; `thm-sf-hom-comparison-constructible` is the cross-site internal-Hom comparison; `lem-sf-proetale-constructible-origin` and `lem-sf-comparison-tor-amplitude` supply origin and Tor transfer. None states this item's pro-etale conclusion for arbitrary inputs, so the item is not attached or duplicated.

## Review by Q72

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `coord/dag-sync.md`, `GOAL.md`, and delivery-errors B–E, together with the `sec-trace-formula` chapter and `sk-d-trace-class` unit. I read the inherited node and its source, the current main-20261015 statements and proofs of thm-sf-hom-ctf, thm-sf-hom-comparison-constructible and lem-sf-comparison-tor-amplitude, the constructible-origin statement, the parent blueprint argument in `lem-trf-exceptional-internal-hom-exchange`, and the exact statements of every cited node. For the existing geometric/comparison tools I also read Stacks morphisms.tex Tag 0A3V (lemma-morphism-finite-type-bounded-dimension), and proetale.tex Tags 09AK (lemma-compare-constructible) and 09AL (lemma-compare-constructible-derived), verifying each tag in the tag map. There are no new nodes requiring a separate source review. The source search in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no exact declaration or blueprint tag attachment.

Step 1 uses the equivalence in `lem-sf-proetale-constructible-origin` to choose bounded constructible étale representatives, then uses clause (ii) of `lem-sf-comparison-tor-amplitude` exactly for the hypothesis it states: a bounded-below étale representative whose pro-etale pullback has the chosen Tor interval. I checked that the representatives supplied by the equivalence are bounded, hence bounded below, and that both K and L satisfy the clause.

Step 2 uses `lem-fin-finite-type-fibre-dimension-bound` with the finite-type structure morphism to the quasi-compact spectrum of the field k. Its statement supplies an integer bound for fibre topological Krull dimensions; identifying the unique fibre with T gives the m required by `thm-sf-hom-ctf`. No separatedness or affine-intersection hypothesis is added.

Step 3 applies the exact statement of `thm-sf-hom-ctf` on the étale site to the two representatives and the common m. Its hypotheses match the fixed coefficient ring, finite-type scheme, bounded constructibility and finite Tor intervals, and its conclusion gives bounded constructibility and finite Tor amplitude for the étale derived internal Hom.

Step 4 cites the displayed isomorphism in `thm-sf-hom-comparison-constructible`, with the first input in the étale finite-Tor category and the second bounded constructible. It also explicitly cites the bifunctoriality in def-pur-derived-internal-hom for applying the chosen input isomorphisms; this is an actual clause of that definition, not an assumed preservation theorem. I checked that the chosen representative identifications transport its right-hand side to the requested `R𝓗om_A(K,L)` and that no stalk formula is used.

Step 5 uses clause (i) of `lem-sf-comparison-tor-amplitude` on the étale Hom object. The coefficient prime is invertible on every k-scheme because ℓ≠p; the unit argument is written before the first Tor-comparison application in step 1. The clause gives the same Tor interval and bounded constructibility after pullback; the step-4 isomorphism transfers both properties to the target. Every cited statement says precisely the fact taken from it, and the quotes in `citations.json` are verbatim.

I checked the empty scheme (all sheaves and derived objects are zero), a geometric point with finite projective coefficient complexes (the formula reduces to bounded ordinary Hom complexes), and the line with doubled origin (finite type but non-separated, with no invocation of a separated-only lemma). For the origin inclusion into the affine line, the derived internal Hom can have positive-degree cohomology; the general dimension-dependent interval permits it. No sharp coefficient-only interval is claimed, and no step replaces finite Tor amplitude by site-perfectness. Ramified E and n>1 retain the same A throughout; no regularity or field assumption on A has been used. No step hides a separate lemma, no proof step exceeds 2000 characters, no cycle reaches the item, and no SGA source is used. The off-unit theorem uses are declared in `split_report.tool_uses` with their purposes.

## Unfinished work

None in the one-level split. The initial server DAG/review checks, dry run and push passed. Self-review then corrected the proof’s source paths to existing current blueprint/Stacks files, replaced plain mathematical notation with TeX, moved the invertibility check before its first use, made the isomorphism transport explicit, and narrowed each citation quote to a complete relevant clause. The revised delivery is subjected to a new final dry run and push; the final response names the resulting commit.
