# NI stage-1 report: lem-sfb-norm-algcl-profinite-cech-exact

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-norm-algcl-profinite-cech-exact.json`: corrected statement and eight-step split; the imported universal global exactness assertion is false.
- `dag/nodes/sec-six-functors-basics/lem-sfb-countable-split-profinite-cover.json`: one new statement-only pure-topology auxiliary, unsplit; no Mathlib match.
- `citations.json`: a verbatim statement quote for every node cited by every item step.
- `searches.jsonl`: actual msearch records. Earlier searches in the repository item were retained; the sandbox was initially empty of node/report work.

One new node, zero new Mathlib leaves. No Lean files or compilers were used, and no repository or launcher file was written.

## Attachments

None. Searches in `lean/WeilConjectures/` for the item tag and the profinite/noncomplete Cech notions found no declaration stating the item. In particular the unrelated topological Cech-comparison declarations do not supply this result. The Mathlib hits about Nobeling's locally constant integer functions are not this Cech complex.

## WANTED

WANTED: an exact external reference for the countably split Cantor-cover construction in `lem-sfb-countable-split-profinite-cover`. Its complete original construction is below. The motivating blueprint paragraph contains no assertion about such a cover.

WANTED: an exact external reference for the noncomplete-coefficient Cech counterexample itself. It is an agent argument below the motivating blueprint paragraph, explicitly marked as such. It is not attributed to Bhatt–Scholze.

The existing uniformizer theorem cites Serre, *Local Fields*, Ch. II §2 Proposition 3 and Ch. I §1 Proposition 1, as wanted literature. This delivery uses that existing node's stated clauses 1, 4 and 5 and creates no substitute theorem for it.

## Statement corrected

STATEMENT-DISPUTED: the imported assertion “for every profinite surjection, every positive-degree continuous Omega-valued Cech cocycle has an actual continuous Omega-valued primitive” is false already in degree one. Keeping the noncomplete coefficient field is essential. The correction states the counterexample and the valid explicit split-cover/local replacement; it does not claim to establish the false global input under a different coefficient convention.

Choose increasing closed finite intermediate fields F_k covering Omega. Choose a_k outside F_k with |a_k| <= ell^(-k). On the countably split Cantor cover below, let f be zero on the diagonal, a_k on (t_k^-,t_k^+), and -a_k on its reverse. The off-diagonal points are clopen and a_k tends to zero, so f is continuous into Omega. Every fibre has at most two points, so its degree-one cocycle equation holds identically. A hypothetical continuous primitive g has closed preimages g^(-1)(F_j) covering nonempty compact T. Baire gives a nonempty open U contained in one of them. U contains both points of a double fibre with k >= j, so a_k = g(t_k^+) - g(t_k^-) belongs to F_j, hence F_k, a contradiction.

The correct positive assertion requires no change of coefficients: a continuous section sigma of q gives g(t_0,...,t_(n-1)) = f(sigma(q(t_0)),t_0,...,t_(n-1)). Every q becomes split after the profinite base change T -> V. The item proves the formula and the cocycle identity explicitly, including degree one and the empty cover.

The parent `lem-sfb-norm-algcl-bar-augmentation` cites this item for the false universal positive exactness input. That use must be reopened by the maintainer; the corrected item cannot discharge that parent as currently written. I have not edited the parent. The same concern applies to any use that turns norm-Omega coefficients into a globally acyclic coefficient object on all profinite tests. This is a fault of the agent-created auxiliary, not evidence that the blueprint's open-image theorem itself is false.

The inherited title and source are maintainer-owned metadata and are retained in the submitted item; the statement, proof_origin and split_report explicitly record the correction. The maintainer should rename the title to “Failure of global profinite Cech exactness for norm-topological algebraic scalars; local replacement”.

## Pure-topology construction for the new node

Here is a proof of the new auxiliary for the independent reviewer; its node remains statement-only as required.

Let V = {0,1}^N with the product topology and its usual lexicographic order. Let D be the set of binary sequences that are eventually alternating. It is countable: specify a finite initial word, the index after which alternation starts, and the next bit. It is infinite and dense, since every finite cylinder contains such a sequence. In fact every nonempty cylinder contains infinitely many, by altering a bit arbitrarily far beyond the specified initial word and then alternating. Enumerate D without repetition as (v_k). Every v_k has infinitely many zeroes and ones, so is approached from both lexicographic sides by eventually constant sequences, which belong to V minus D. Eventually constant sequences also show that V minus D is dense.

For v outside D, let c_k(v) = 0 if v < v_k and 1 if v > v_k. Define c(v) = (c_k(v))_k. Set T to be the closure of the graph {(v,c(v)): v outside D} in V times {0,1}^N and let q be the first projection. The ambient space is a countable product of two-element discrete compact spaces. Tychonoff gives compactness; clopen cylinders separate points and form a basis, giving Hausdorffness and total disconnectedness. The weighted metric sum_i 2^(-i-1)|x_i-y_i| on each binary product, and the sum of the two factor metrics, induce its topology: fixing the first m coordinates bounds the tail, and a ball of radius less than the smallest specified coordinate weight fixes those coordinates. Restriction gives a compatible metric on closed T. A closed subset of a compact space is compact: add its open complement to an open covering and discard that extra member of a finite subcover. Thus T and V are metrizable profinite spaces.

For v != v_j, the threshold at v_j is locally constant near v. Indeed the first binary digit where v differs from v_j gives a cylinder on which the comparison has the same sign. Therefore at any point of T over v, every coordinate c_j is forced except possibly the one j for which v=v_j. For v outside D the graph itself supplies the unique point. For v=v_k, the points approaching v_k from below and from above outside D show, for every finite cylinder neighbourhood in the ambient product, that both choices of the kth coordinate occur in the graph closure. The other finitely many specified coordinates are locally constant since their thresholds differ from v_k. This proves that the fibre is exactly two points t_k^- and t_k^+, differing only in the kth auxiliary bit. It also proves q is surjective and T is nonempty.

In R = T times_V T, the clopen condition “the first point has kth auxiliary bit 0 and the second has kth auxiliary bit 1” singles out exactly (t_k^-,t_k^+). To see this, any unequal kth bits over a common v force v=v_k by the previous paragraph. The reverse condition singles out the reverse ordered pair. Hence these are clopen singletons. Every other relation point is diagonal, by the fibre classification.

Finally let U be nonempty open in T. The defining graph is dense in T, so choose a graph point (w,c(w)) in U with w outside D. Its q-fibre is a singleton and hence is contained in U. The closed subset T minus U is compact. Its projection is compact and therefore closed in Hausdorff V, so B = V minus q(T minus U) is an open neighbourhood of w, and q^(-1)(B) is contained in U. Every nonempty open B contains infinitely many v_k, as established with cylinders. Choose k >= N with v_k in B. Then both t_k^- and t_k^+ belong to U. This proves the exact tail-density conclusion used by the counterexample.

This is a construction of a topological cover, independent of the scalar field, the Cech differential and cohomological exactness. It is strictly smaller than the item and is not one of its clauses moved into a new node. Its complete construction is not hidden behind the word “standard”.

## Searches and reuse

Before creating the topology node I searched the whole DAG and project Lean for split Cantor covers, double fibres, singleton-fibre density, and irreducible profinite covers; no node with these properties was found. `tools/blueprint_refs.py search` for `Cantor`, `split Cantor`, `double fibre`, and `countable split profinite` found no blueprint duplicate. Searches for `Cech`, `positive profinite`, and `noncomplete` found no blueprint statement of the corrected item. The inherited source paragraph (3) was read in full: it delegates the open-coefficient theorem, and does not state universal Cech exactness for noncomplete coefficients.

For the new node, two semantic phrasings, a LeanSearch query, two Loogle patterns, and source greps ran through msearch and were read. `exists_retractionCantorSet` and `cantorToHilbert_surjective` in Mathlib/Topology/MetricSpace/HausdorffAlexandroff.lean:27–100 were inspected. They construct surjections/retractions and give no double-fibre or tail-density control. The other hits give finite clopen approximations or metrization, not this cover. The node's mathlib_searches records the queries actually logged, with the actual digest records and a no-match verdict. The item retains its earlier searches and adds the searches made here; neither its original false assertion nor the corrected counterexample is a Mathlib leaf.

Reused existing nodes rather than creating duplicates: `lem-sfb-algcl-countable-closed-finite-cover`, `lem-sfb-baire-closed-cover-interior`, `lem-weil-l-adic-extension-integers-dvr`, and `lem-sfb-finite-quotient-fiber-product`. The Baire node already is a Mathlib leaf. The uniformizer theorem is declared in split_report.tool_uses as the generic local-field input of another unit; it does not replace a six-functor proof step.

## Not duplicates

The new topology node has no Stacks tag shared with an existing node. `lem-sfb-countable-split-profinite-cover` vs `lem-sfb-finite-quotient-fiber-product`: the existing node proves profinite fibre-product topology and its finite-partition inverse-limit description, and does not construct a surjection with dense double fibres. `lem-sfb-countable-split-profinite-cover` vs `lem-sfb-profinite-metric-function-quotients`: the existing node factors a continuous map on S times G^r through metrizable quotients, and gives neither double fibres nor clopen off-diagonal points. `lem-sfb-countable-split-profinite-cover` vs `lem-sfb-normed-scalar-profinite-cech-exact`: that node concerns positive exactness for a complete finite-extension coefficient field; the new node is only a pure-topology construction and makes no exactness assertion.

## Review by NI

I read the item and its motivating main-20261015 direct-images proof, paragraph (3), against the chapter and unit records. The seed is explicitly an agent-formulated WANTED noncomplete input. Its complete finite-extension neighbour does not apply: a primitive in a completion or a replacement of all continuous functions by finite-stage functions would change the problem. This led me to test actual degree-one cocycles and find the counterexample above. I corrected the statement openly, rather than treating a theorem for complete coefficients as a proof.

For step 1 I checked every clause of the new topology statement against the construction above. The only inputs the item takes are exactly its fibre classification, the clopen oriented pairs and the double-fibre tail-density property. The source for the new node is only the motivating blueprint paragraph, not a claimed external topology theorem; I marked the reference as wanted and supplied the full original construction here. The Cantor graph closure stays within the permitted profinite universes.

For step 2 I read the existing countable closed-cover node's entire statement and Stanford L19, Proposition 1.1.9, first bullet, p. 3. The cited statement actually gives an increasing closed exhaustion by finite intermediate fields; it is stronger and more precise than just countability of isomorphism classes. E = Q_ell satisfies its finite-extension hypothesis. No claim that f or g has image in a single finite field is made.

For step 3 I read the full statement of the existing DVR theorem and its referenced blueprint definition. Clauses 1, 4 and 5 give the norm-one units, the uniformizer with norm strictly between zero and one, and the integer power decomposition. Applied to F_k with its restricted extended norm, every hypothesis is present. The definition of algebraic closure supplies a root of X^2 - pi_k. Its absence from F_k follows by the integer-exponent norm calculation, and scaling by a nonzero power of ell preserves that absence. This small argument is written out in the step, so it requires no additional lemma node. I did not present the unavailable Serre chapter as read.

In step 4 the topology statement really says that each oriented off-diagonal singleton is clopen. The finite truncations therefore are continuous. I checked the direct epsilon estimate in Omega, with no appeal to completeness or to an undefined infinite sum. At the exceptional oriented pair with index below N, its clopen singleton is the required neighbourhood; elsewhere the complement of the finite exceptional set is open. In step 5 I checked all triples by the fibrewise potential identity. This is an elementary cancellation and does not assert a global potential.

In step 6 I read Stacks Topology Tag 0CQN, lemma-baire-category-locally-compact, and the Baire leaf's entire statement. The cover consists of closed subsets of the actual compact Hausdorff nonempty T, so the Baire hypotheses hold. The tail-density clause supplies k >= j, and monotonicity from the exhaustion gives F_j subset F_k. Thus the contradiction is an equality of values in the original field. Every non-elementary fact here is a cited statement, not something taken from a cited node's proof.

For steps 7 and 8 I checked the two contraction formulas, the signs, and the first-coordinate-deletion case. The common q-image ensures the distinguished point used by every face is the same. The fibre-product node's statement supplies exactly that T times_V T is profinite, with the correct subspace topology. The diagonal is a continuous section and the tuple identifications are coordinate maps, so the split contraction gives the asserted pulled-back primitive without an unproved derived comparison. I read the stated fibre-product lemma and Stacks Topology Tags 08ZY (lemma-profinite) and 0A2P (lemma-describe-limits) for its ambient setting.

Edge checks: degree n=1 uses no negative cochains; empty T=V gives only zero functions in the replacement clause; a finite cover with a set section has the usual contraction, so cannot be this counterexample. The construction works at ell=2, since the coefficient field has characteristic zero and the nonsquare proof uses valuation exponents, not residue characteristic. The complete-field exactness node is consistent with this counterexample: the Baire argument relies on Omega being a countable union of closed finite fields, a property not asserted for its completion. A singleton or finite topology cannot satisfy the new lemma's tail-density property, so the construction necessarily remains nonempty and infinite. No source is SGA.

I checked delivery-errors B–E point by point: the new node is self-contained and statement-only; definitions are supplied inline or cited; TeX has single decoded backslashes; no search is invented; no blueprint duplicate was found; every cited statement was opened and quoted in citations.json; no proof-only content of a cited node was used; the new input is a pure-topology construction rather than a relocated exactness clause; the original false statement has an explicit counterexample and a named correction; the actual cochain maps and their signs are written out. None of the non-elementary item steps exceeds 2000 characters. The ancestor command returns None because the inherited created.item chain ends in a module name rather than a node; I preserved that provenance and named the motivating paragraph in from.place and split_report.blueprint.

## Unfinished work and consequences

The original global exactness assertion cannot be proved because it is false. The corrected diagnostic and local replacement are completely split by one level, with the pure-topology construction isolated as the only new unsplit node. Its proof is supplied above for review, while the new JSON correctly contains only its statement. The parent's dependence on the disproved global claim requires a separate maintainer decision and repair outside this worker's ownership.
