# Stage-1 report: lem-trf-stable-modification-spreading

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-stable-modification-spreading.json` — item, split; four proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-stable-modification-finite-presentation-spread.json` — statement-only node; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-stable-modification-stability-locus.json` — statement-only node; Mathlib searches found no match.
- `citations.json` — verbatim node-statement quotes for every proof-step citation.

## Attachments

None. I searched the slopmaster2 and upstream source trees for the item id, its title and stable-modification terms; no finished declaration with the required statement was present.

## WANTED

- `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, especially Lemma 3.2.2, Lemma 5.1(ii), Remark 3.1.1(ii), and the second paragraph of the proof of Theorem 1.5, pp. 34–36. The DAG source cites the online Temkin PDF, but this local repository has no archived copy.

## What was checked and changed

The imported item was unsplit and had no proof. I retained its statement and hypotheses, added the two genuinely smaller statement-only lemmas, and supplied a four-step proof. The first new node isolates finite-presentation descent of the prescribed proper pair and its generic identifications. The second isolates the constructibility of the semistable/stable fibre locus and the dense open where the pair maps are isomorphisms. Neither new node claims the full item or contains proof steps. I searched the whole DAG and blueprint for duplicates and found none; the existing valuation stable-reduction, Riemann–Zariski refinement, and semistable base-change nodes are cited where applicable.

## Review by Q90

I read the item source citation (Temkin, §3.1, Remark 3.1.1(ii), Lemma 3.2.2, Lemma 5.1(ii), and the second paragraph of Theorem 1.5) and the existing statements of `lem-trf-riemann-zariski-finite-refinement` and `lem-trf-semistable-marked-base-change`. Step 1 uses exactly the finite-presentation-spread node: its statement supplies the $L$-quasi-model, valuation lift, compatible proper pair, and pullback isomorphism. Step 2 uses both new nodes: the first supplies the finite-presentation family and the second supplies the stable neighbourhood, semistability, eta-modification property, and dense generic isomorphism open. Step 3 checks that the pullback identification includes both curve and marking maps and invokes the existing base-change statement for the geometric semistability and stability clauses. Step 4 uses the Riemann–Zariski statement that a quasi-model gives an open injection and the stability-locus statement's dense open. I checked that every hypothesis used (integral finite-type base, separable closure, valuation lift, flat finite-presentation curve and marking, proper pair maps, and generic isomorphisms) occurs in the cited statements or the item itself. I also tested edge cases conceptually: empty marking is allowed, and if the specified modification is already an isomorphism the dense open may be all of the base. No statement error or duplicate node was found.

## Source error

None found in the imported statement or in the cited route.

## Unfinished work

The two new lemmas remain statement-only stage-1 leaves, as required. Their nonexistence in Mathlib was recorded by the mandated searches. The Temkin PDF still needs archival promotion by the maintainer.

## Not duplicates

- lem-trf-stable-modification-finite-presentation-spread vs lem-trf-stable-modification-spreading: the new node only descends the finite-presentation pair and generic isomorphisms; it asserts no semistability, stability, or dense open.
- lem-trf-stable-modification-finite-presentation-spread vs lem-trf-marked-curve-finite-type-model: the existing node descends the original marked curve, while the new node descends an additional proper modification pair over a valuation ring.
- lem-trf-stable-modification-finite-presentation-spread vs lem-trf-marked-nodal-dualizing-degrees: the new node is a descent statement for pair morphisms and does not assert dualizing-sheaf degrees.
- lem-trf-stable-modification-finite-presentation-spread vs lem-trf-riemann-zariski-finite-refinement: the new node spreads curve and modification data; the existing node only supplies valuation-space points, quasi-model opens, and common refinements.
- lem-trf-stable-modification-finite-presentation-spread vs lem-trf-semistable-marked-base-change: the new node constructs a finite-presentation spread; the existing node states permanence under arbitrary base change and does not construct a spread.
- lem-trf-stable-modification-finite-presentation-spread vs lem-trf-stable-modification-uniqueness-normal: the new node gives existence by approximation from V; the existing node gives uniqueness over a normal integral base.
- lem-trf-stable-modification-finite-presentation-spread vs lem-trf-valuation-stable-reduction: the new node descends an already specified modification; the existing node constructs a stable modification over a finite-height valuation ring.
- lem-trf-stable-modification-stability-locus vs lem-trf-stable-modification-spreading: the new node is only the constructibility and shrinking assertion for an already spread pair; it does not descend the pair from V.
- lem-trf-stable-modification-stability-locus vs lem-trf-marked-curve-finite-type-model: the existing node descends the unmodified curve, while the new node detects semistable/stable fibres and the dense isomorphism locus of a proper pair.
- lem-trf-stable-modification-stability-locus vs lem-trf-marked-nodal-dualizing-degrees: the new node concerns constructibility and opens of a family; the existing node computes degrees of a marked dualizing sheaf.
- lem-trf-stable-modification-stability-locus vs lem-trf-riemann-zariski-finite-refinement: the new node shrinks a given family to its stable locus; the existing node describes quasi-compact valuation spaces and common refinements.
- lem-trf-stable-modification-stability-locus vs lem-trf-semistable-marked-base-change: the existing node proves arbitrary-base-change permanence, whereas the new node proves constructibility and a neighbourhood shrink for a finite-presentation family.
- lem-trf-stable-modification-stability-locus vs lem-trf-stable-modification-uniqueness-normal: the new node detects where one spread is stable and is an isomorphism generically; the existing node compares two stable modifications by a unique isomorphism.
- lem-trf-stable-modification-stability-locus vs lem-trf-valuation-stable-reduction: the new node assumes a stable valuation fibre and spreads its stability to a neighbourhood; the existing node is the existence theorem producing that valuation-fibre modification.
