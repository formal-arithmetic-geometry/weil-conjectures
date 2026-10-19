# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-local-spectrum-open-classification.json`: split into five proof steps; no whole-statement Mathlib match.
- `citations.json`: six verbatim statement excerpts, covering each dependency occurrence in the five steps.
- `searches.jsonl`: six searches through the required msearch command, retained with their actual responses/digests.

New nodes: 0. New Mathlib leaves: 0. Two existing Mathlib leaves are reused.

## Attachments

None. I searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, local spectra/local rings, and finite discrete spaces. There is no declaration giving this entire classification. The inspected project file `WeilConjectures/Mathlib/Topology/KrullDimension.lean` proves results about complements of opens in irreducible spaces, not this statement about opens of a possibly reducible local spectrum. Mathlib's `IsLocalRing.closedPoint_mem_iff` gives the first clause only; `IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top` additionally assumes a domain and does not give the general conclusion. Neither is an attachment of this item.

## Wanted sources

None. All proof sources are available locally.

## Findings and changes

The original statement is correct, including dimension zero, nonreduced rings, reducible spectra, and the empty open. I appended inline meanings of “local” (the nonunits form the proper maximal ideal) and “finite discrete”; these clarify existing notions and do not change any hypothesis or conclusion. This is not a statement dispute. The original proof was empty. I supplied the dimension-chain argument and the finite-space topology argument rather than introducing nodes that merely repackage clauses of the item.

The principal source is `literature/stacks-project/varieties.tex`, Tag 09N8, label `lemma-affine`, lines 7747–7775, specifically its reduction to a local spectrum and case split at the closed point. Its cited algebra input is Tag 00FR, `algebra.tex`, label `lemma-Noetherian-irreducible-components`, lines 6135ff. Its final scheme input is Tag 02O0, `schemes.tex`, label `lemma-scheme-finite-discrete-affine`, lines 2085ff. Both already have DAG nodes, so no new nodes were needed. The scheme-affineness node records a different valid source derivation through 01ZV; I checked its statement, which is exactly the finite-discrete fact used here, against 02O0 and its Mathlib instance.

I read the item's chapter and unit records, the current blueprint ancestor `lem-a1-middle-extension-endpoints` in main-20261015, and the intermediate `lem-a1-open-dimension-one-higher-image-vanishing` node. This is a lower-level input to the already recorded affine-open route; it changes no chapter or unit route and is not the unit's key node, so no unit record was edited. The existing ancestry and precise from.place are retained. Whole-blueprint searches for “local spectrum”, “dimension one”, “minimal prime”, and “finite discrete”, together with whole-DAG tag/keyword searches, found no equivalent blueprint statement.

The Mathlib searches used leanfinder twice with different phrasings, leansearch, loogle, and grep twice, all through msearch. Their hits cover related Artinian schemes, finite-discrete affineness, the closed-point clause, or a domain-only dichotomy, not the entire item. I inspected `Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1329` and `:1353`, `Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean:43`, and `Mathlib/AlgebraicGeometry/Limits.lean:700`. The final two confirm the already recorded leaves. No searches were invented, and inherited search records in the original item were preserved separately from this session's appended records.

## Not duplicates

No new nodes. The whole-DAG searches for 00FR and minimal primes selected `lem-weil-pbc-noetherian-finitely-many-minimal-primes`; searches for finite discrete scheme affineness selected `lem-weil-pbc-finite-discrete-scheme-affine`. Both are used directly.

## Review by Q47

I checked the statement against 09N8's local-spectrum paragraph, with 00FR and 02O0 open. The ring is commutative, Noetherian and local, and the dimension bound is at most one, not exactly one. No domain, reducedness, finite-type, or nonempty-open assumption enters the proof. The proper nonunits ideal formulation makes explicit why every prime lies below the unique maximal ideal, without hiding an application of existence of maximal ideals.

Step 1 cites `def-weil-affine-spectrum` for the prime-ideal space and Zariski topology. Its statement explicitly gives both. The basic open calculation is written out: an open containing the maximal ideal contains a D(f) with f outside that ideal, hence a unit, hence D(f) is the whole space. This is an elementary use of the definition of the Zariski topology; no general specialization theorem is silently invoked.

Step 2 cites `def-weil-pbc-krull-dimension-ring`, whose statement defines length-n strict prime chains and their supremum. A smaller prime under a nonmaximal prime would give a chain of length two ending at the maximal ideal. Likewise an intermediate prime above it gives such a chain. Both contradictions are elementary and do not require existence of minimal primes or a domain assumption.

Step 3 cites `lem-weil-pbc-noetherian-finitely-many-minimal-primes`. I opened its statement: for every Noetherian ring it states finiteness of minimal primes, defining minimal as having no strictly smaller prime. The item's Noetherian hypothesis is precisely the needed hypothesis, and step 2 places every point of W in this finite set. This is the only Noetherian finiteness input; I marked the step non-elementary rather than citing a definition of Noetherianity as though it implied finiteness in one line.

Step 4 again cites the affine-spectrum definition for the Zariski topology. The argument computes V(p) as {p,m} using step 2, intersects with W to make each singleton closed, and uses finiteness from step 3 to make its complement closed. It then expresses every subset as a union of open singletons. Thus finite T1 implies discrete is proved in the step, rather than hidden as a new lemma or quoted without a node. Earlier steps' conclusions are used as earlier steps, without circular dependencies.

Step 5 cites `def-pc-scheme` for the induced open subscheme being a scheme and `lem-weil-pbc-finite-discrete-scheme-affine` for affineness. The former's statement explicitly includes open subschemes; the latter's statement assumes only a scheme with finite discrete underlying space and concludes that its canonical map to Spec of global sections is an isomorphism. The hypotheses are supplied by steps 3–4, so this citation proves the requested affineness without strengthening hypotheses. The current blueprint update of the scheme definition adds local affineness, agreeing with this usage. Both external statement inputs are already Mathlib leaves, hence no off-unit route exception is needed.

For edge cases I checked a field and the dual numbers over a field (one-point spectrum, only the empty open avoids m), a discrete valuation ring (punctured spectrum a single generic point), and the nodal local ring k[x,y]_(x,y)/(xy) (two distinct minimal primes). In the last example V((x))={ (x),m } and V((y))={ (y),m }, so removing m really separates the two generic points, even though the ambient local space is not discrete. The empty scheme is included by 02O0 and by the finite/discrete Mathlib instance. The zero ring has no proper maximal ideal and is excluded by the stated local convention. No new statement needs a separate edge-case audit.

I checked B–E: no new node shapes or duplicate obligations arise; all six citation excerpts are literal substrings of their cited statements; all non-elementary inputs are cited statements, and the remaining algebra/topology arguments are explicitly elementary. No proof step exceeds 2000 characters (the longest is 569). There are no SGA sources, no moved clauses masquerading as nodes, no proof-only facts taken from a dependency's proof, and no compilation or repository writes. The corrections made during this review were inline clarification of the two notions and explicit handling of the empty and zero-dimensional cases.

The first full dry run rejected four citation excerpts as shorter than the required 40 characters. I replaced those excerpts with the complete cited statements, preserving verbatim text and the same dependency coverage. This changed no mathematical step.

## Unfinished work

None in the split. Server validation and direct delivery are run after this report is written; their actual terminal results determine the final delivery answer.
