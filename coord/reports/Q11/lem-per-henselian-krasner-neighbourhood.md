# Stage-1 delivery: lem-per-henselian-krasner-neighbourhood

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-krasner-neighbourhood.json`: statement, split; five proof steps, no Mathlib match for the full arbitrary-rank result.
- `citations.json`: verbatim statement excerpts for every node cited in every proof step.
- `report.md`: this report. `searches.jsonl` is the unmodified output log of the required search command.

New nodes: 0. New Mathlib leaves: 0. Two existing Mathlib leaves are reused.

## Attachments

None. I searched WeilConjectures in `/home/ubuntu/weil-src-slopmaster2` for the exact blueprint tag and for Krasner, henselian valuations, and the relevant notions. The only Krasner use is the p-adic algebraic-closure argument in `NumberTheory/Padics/Extension.lean`, lines 75–128. It has different objects and only treats a complete rank-one base. No declaration states this item exactly. The upstream master is reference material; its declarations are not treated as finished proofs.

## WANTED

WANTED: N. Bourbaki, Algebre commutative, chapter VI section 8 exercises 12 and 14(a), cited in ILO XX 4.4, printed p.374, for lem-per-henselian-krasner-neighbourhood. This volume is not present in the local obtained-literature list. The proof supplied here is explicitly agent-written, not attributed to an unread exercise.

## What needed repair

The imported item had no proof. Its mathematical statement is correct. Its TeX control sequences were escaped twice; these are repaired in the statement, and the additive valuation axioms, valuation ring and basic-ball topology are spelled out. No hypothesis is added and no conclusion is changed. There is no statement dispute.

ILO XX 4.4 only invokes forms of Krasner's lemma for dense henselian valued fields and refers to Bourbaki; it does not give this finite-Galois argument. Stacks Tag 09EI, `more-algebra.tex`, `lemma-krasner`, was read: it concerns root perturbation over a complete one-dimensional local domain and does not supply the arbitrary-rank theorem. I do not cite it as a proof dependency.

A possible gap in a naive proof is the passage from equality of valuation rings to equality of numerical values. I repaired that explicitly: valuation-ring equality gives preservation of all comparisons by field ratios, and the finite order of each automorphism rules out a strict change in the value of any element. This needs neither rank one nor completeness.

## What remains unfinished

Nothing in this one-level split. The existing unsplit `lem-per-henselian-finite-extension-topology` supplies the uniqueness-of-prolongation theorem; its proof is a separate queue item. This delivery uses only the uniqueness clause, not the finite-separable-topology comparison in that node, so there is no appeal to a topology assertion potentially proved using Krasner itself.

## Blueprint and duplicate searches

I read the chapter `sec-deligne-laumon-a1`, unit `sk-p-dl-a1-perverse`, the item's full provenance, and the nearest blueprint ancestor. `tools/blueprint_refs.py ancestor` names `lem-per-artin-gabber-affine-curve`; its inherited completion-rigidity/dense-field branch is preserved. Searches for `Krasner` and `henselian valued` returned no blueprint nodes. The `fixed field` blueprint search returned three unrelated arithmetic/lattice nodes. Searching statements across the whole DAG found the existing henselian finite-extension theorem, finite Galois fixed-field theorem, and intermediate-field fixing-subgroup theorem; those are used rather than recreated. No unit key node is being split, so no unit realization record is changed.

## Not duplicates

No new nodes are created. In particular, no duplicate of `lem-per-henselian-finite-extension-topology`, `lem-weil-pbc-finite-galois-fixed-field` or `lem-exc-etale-galois-fixed-field-subgroup` is introduced.

## Mathlib searches

The item's inherited search records are retained. Seven additional searches were run through the required msearch command and recorded verbatim from searches.jsonl: LeanFinder with two phrasings, LeanSearch, two Loogle queries, and two source grep queries. All services responded successfully. The returned signatures were read, including the complete normed-field Krasner theorem in `Mathlib/Analysis/Normed/Field/Krasner.lean`, lines 45–155, the fixed-field theorem in `Mathlib/FieldTheory/Galois/Infinite.lean`, line 85, and the decomposition/inertia subgroup definitions in `Mathlib/RingTheory/Valuation/RamificationGroup.lean`. IsKrasner requires real-valued normed-field data and its available general instance assumes a complete base. HenselianLocalRing of a field concerns that field as a local ring, not the valuation ring in the hypothesis. The decomposition subgroup definitions provide no theorem that it is the entire Galois group. None is a one-line specialization proving the item for arbitrary valuation rank.

## Review by Q11

I read the full B–E checklist in coord/delivery-errors.md with the relevant source texts and node statements open. There are no new statements to audit under B; the item's valuation and topology notions are explicit and its original four definition dependencies are retained. I also read those four definition statements: they define valuation rings, henselian local rings, field extensions and separable algebraic extensions, respectively. None is cited as if it proved a valuation-extension or Galois theorem.

For Step 1, I opened `lem-per-henselian-finite-extension-topology` and checked its precise uniqueness clause: two prolongations have equal valuation subrings. The base valuation is nontrivial and henselian by the item, and N/F is finite algebraic because it is finite Galois. Composing w with an F-automorphism really does restrict to the same valuation on F. This is the only non-elementary input in this step. I do not infer equality of values from equivalence without an argument.

For Step 2, `lem-weil-pbc-finite-galois-fixed-field` explicitly says G is finite. I read its full statement and its source, Stacks Tags 09I1 (`fields-lemma-finite-Galois`) and 09DW (`fields-theorem-galois-theory`). The finite-order deduction is written out by repeated powers and cancellation. The ratio criterion for valuation-ring membership converts Step 1 into preservation of weak and strict comparisons, and the cyclic chain argument forces equality of values. This is an elementary deduction from the cited statements, rather than a hidden independent isometry lemma.

Step 3 uses only Step 2, the given strict inequalities and the defining valuation inequality. I checked the identities sigma(alpha-beta)=sigma(alpha)-beta and alpha-sigma(alpha)=(alpha-beta)-sigma(alpha-beta), using that sigma fixes beta. The minimum is exactly w(alpha-beta), so the asserted lower bound contradicts the hypothesis in the correct direction. The zero-difference case beta=alpha also works with infinity. No non-elementary assertion is omitted from this step.

For Step 4 I opened `lem-exc-etale-galois-fixed-field-subgroup` and the Mathlib declaration it records, InfiniteGalois.fixedField_fixingSubgroup, line 85. Its statement applies to every intermediate field in a Galois extension, not merely to the base field or to a normal intermediate extension. Here L=F(beta) is an intermediate field and N/F is Galois. The automorphisms fixing beta equal the pointwise fixing subgroup of L by the smallest-subfield definition, with the argument given in the step. Thus the citation gives exactly alpha in L once Step 3 proves it is fixed.

For Step 5 I checked both clauses of `lem-weil-pbc-finite-galois-fixed-field`: finiteness makes the radii a finite set, and its fixed-field clause handles an empty set of moving automorphisms. When the set is nonempty, each alpha-sigma(alpha) is nonzero, so each radius is a finite value and the finite maximum exists in any total order. The resulting ball contains alpha and is open by the stated topology convention. Its inequalities are strict for every moving conjugate, as required. For alpha in F there are no moving conjugates and U=N works for all beta. The test cases N=F, alpha in F, beta=alpha, negative radii, positive characteristic finite separable extensions, and a higher-rank ordered value group require no additional assumption; no discreteness, Archimedean comparison or infinite limit is used.

Every cited node is unmerged and its quoted statement really supplies the indicated clause; citations.json contains literal excerpts, including the exact stored TeX escaping. I checked that the proof dependencies are exactly the union of step uses, with no dependence back on this item in the nodes used. The two off-unit Galois nodes are already Mathlib leaves, so no exceptional tool-use route is needed. The only non-Mathlib theorem used is in the item's own unit. Every step is under 1000 characters; there are no long steps hiding a lemma, no new node restating a clause of the item, and no source forbidden by the route lock is cited. The proof follows the inherited dense-field comparison route and is candidly marked agent-written where the obtained source omits the argument.
