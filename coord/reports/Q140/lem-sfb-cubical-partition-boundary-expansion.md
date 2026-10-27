## Worker report

Files written, all inside the Q140 sandbox:

- `dag/nodes/sec-six-functors-basics/lem-sfb-cubical-partition-boundary-expansion.json`: item, now split into six elementary finite-sum steps; no Mathlib match. The statement, statement dependencies, original source, creation record, and historical searches are unchanged. Added actual current search records and the split report.
- `citations.json`: all three step/node citation pairs, with verbatim quotations from the current cited statements.
- `verify_finite.py`, `write_split.py`, and `searches.jsonl`: local working material, not additional DAG nodes.

New nodes: 0. Mathlib leaves: 0.

Attachments: none. Searched `lean/WeilConjectures/` for the exact blueprint id, cubical/partition boundary, and shuffle/inversion terminology. No project declaration states this item. The related signed complementary Koszul pairing in `WeilConjectures/RingTheory/KoszulComplementaryEquivalences.lean` concerns complementary exterior powers, not translated cubical faces. Also read `lean/Sheaf/AlgebraicTopology/IntegralCubicalChainDiagonal.lean`: its parent diagonal theorem and relevant structural conditions contain sorry, so they are not attachment evidence.

WANTED: an exact external reference for the signed integral cubical lattice partition diagonal and paired-face expansion, for lem-sfb-cubical-partition-boundary-expansion. The current blueprint's direct-images proof paragraph (3) is the inherited route location only; it contains no such formula. The proof is explicitly agent-written. No SGA source is used.

What was wrong: the item was a statement-only child of the previous diagonal split. There is no mathematical statement error to correct. The inherited ancestor lookup prints None because the created.item chain has no imported blueprint ancestor; the existing null from.node and via chain are retained, with the already precise route place. The current `dag/units/sk-thm-sf-ctf-stability.json` records a unit in sec-six-functors whereas this item's inherited chapter and current blueprint route are sec-six-functors-basics; I read both the unit record and the latest unit text and changed neither. No unit statement or route is replaced.

Unfinished: no proof argument remains in this item. Its existing definition and contraction dependencies remain independent project work; I have not proved those in Lean or claimed them finished. There are no new unsplit nodes. No repository or launcher file was written, no direct git command or compiler/Lake/build tool was run, and no agent was started.

## Search and source audit

Read the chapter and unit records, the latest blueprint unit and its direct-images proof paragraph (3), the full current item, the Q87 parent delivery report including original steps 2 and 3, the contraction statement, and all three existing notion statements (free modules, tensor product, chain complexes). The two original sign and paired-face arguments are fully realized by the six steps here. The current blueprint does not supply a published proof of this combinatorial formula, so proof_origin.by is agent and the external-reference request remains explicit.

Whole-DAG searches for cubical, partition boundary, paired faces, inversion and shuffle found the parent diagonal, the contraction, and simplex/bar-chain relatives, without an exact separate boundary-expansion proof. Whole-blueprint searches `cubical` and `partition boundary` each returned zero matching imported blueprint nodes; same_as remains []. No new node is proposed, so there is no new/existing duplicate pair to justify.

Actual current Mathlib searches are logged in searches.jsonl and recorded without invented queries. The four required search types were run, plus a second LeanFinder phrasing and a source-locating grep. Loogle returned TensorProduct.sum_tmul and TensorProduct.tmul_sum; read their implementations at Mathlib/LinearAlgebra/TensorProduct/Defs.lean:402 and :409. They distribute over finite sums and follow immediately by repeated bilinearity, but give no cubical expansion or face pairing. LeanSearch and both LeanFinder phrasings returned simplicial/bar-resolution and Dold–Kan results; read Rep.standardComplex.d_of at Mathlib/RepresentationTheory/Homological/Resolution.lean:189 and its tuple-deletion definition above it. It does not give the translated cubical boundary or ordered-subset signs. The specific cubical/Serre-diagonal grep had zero hits. No exact or one-line generalized match for this item was found. Historical imported searches were preserved, not re-labelled as this worker's calls.

## Review by Q140

I read the source materials listed above and checked the item sentence by sentence. The rank r may be zero, I is any coordinate subset (including empty), v is arbitrary in the full integer lattice, and no positivity or nonempty-part assumption is introduced. The tensor sign is determined by the degree of the first factor, and the inversion convention is c<a throughout. The existing contraction statement introduces exactly the same cubical groups and boundary formula. Its contraction and exactness conclusions are not needed for this calculation; step 1 takes only its displayed boundary definition. The tensor definition really states bilinearity, which is exactly what steps 1 and 5 use, with R=Z and the indicated free abelian groups. Both node files were opened; citations.json quotes their actual statements, not their proofs.

Step 1 expands the given two-factor differential and distributes tensors over finite sums. The contraction citation supplies the actual signed boundary, including the upper translated face minus lower face, and the tensor citation supplies bilinearity. Iterating addition gives finite distributivity with no separate theorem needed. There is no appeal to a tensor comparison or homology theorem. Empty factor direction sets simply contribute no faces.

Step 2 writes both indexing maps and their inverses. Since B and C partition I minus i, i belongs to neither; this is exactly the hypothesis needed for insertion/removal to be inverse. These are index bijections, not a claim that distinct indices give distinct tensor elements. Consequently reindexing a finite sum preserves all multiplicities, including coincident terms. No choice, infinitary sum, or external indexing theorem is hidden.

Step 3 checks both cardinality decompositions and counts the new pairs (i,c) with c<i in the first inversion set. These are disjoint from the old B-cross-C pairs and exhaust all new pairs. The first boundary position is p, so N+q+p is exactly the exponent. The equality with s is just the power law for -1.

Step 4 counts the other new pairs (b,i) with i<b. It explicitly retains the tensor factor (-1)^|B| and the second boundary position q. Substitution |B|=p+t leaves a difference 2t, so both coefficients agree over Z. This checks the sign convention rather than appealing to an unnamed shuffle lemma.

Step 5 substitutes the two partitions in the actual generator differential and uses u_(B union {i})=u_B+u_i. Its cited tensor statement permits expansion of the differences. Both middle tensor elements have identical vertices and direction sets in the same total bidegree (|B|,|C|); their coefficients are literally -s and s. The two remaining outer tensors are those displayed in the item. Lattice addition commutes, so the alternate u_i+u_B order in the final formula agrees.

Step 6 sums the paired identity using the explicit bijections already proved and replaces p+q by the position in I. The I=empty case is checked separately: the unique tensor has two degree-zero factors, both differentials vanish, and the outer sum is empty. This also covers rank zero. No counit, contraction homotopy, chain-diagonal theorem, or stronger parent result is used, so no cycle is introduced.

Against B–E: no new nodes or hollow definitions are created; decoded TeX is single-escaped; each existing notion in the item has its actual definition dependency, whose statement I read. Every non-elementary assertion is either a cited input or absent: the proof consists entirely of the explicit finite indexing, cardinality counts, substitutions and additive cancellation just reviewed. No clause is moved to a restatement node. All uses and proof_deps agree, all quotations are verbatim, and no route theorem of another unit is needed. Both individual cited facts have exactly the hypotheses checked above. Each step is below 500 characters (total 2350), so no step exceeds the 2000-character long-step review threshold. I kept the statement unchanged and found no STATEMENT-DISPUTED case.

As a supporting edge-case check, ran the local Python integer calculation in verify_finite.py: all subsets in ranks 0 through 6 at zero and nonzero (including negative) base vertices; 254 cubical generator expansions and 2005 local triples. Checked both directions of both index bijections, the two sign formulas, and equality of full integer coefficient dictionaries. All passed. This finite verification supports, and does not replace, the general proof above.

## Validation

Server review_split requested through srvcheck.py; the full delivery dry run and push follow this report. No local check_dag, review_split or preflight_delivery execution is used.
