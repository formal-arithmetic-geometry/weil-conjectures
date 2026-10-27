# Stage-1 delivery: lem-sfb-rank-two-pinned-braid (Q56)

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rank-two-pinned-braid.json`: statement item, split into eight steps; statement and statement dependencies unchanged; no Mathlib match.
- No new nodes and no Mathlib leaves.
- `citations.json`: statement quotations for every step/dependency pair.
- `searches.jsonl`: the actual msearch records; the sandbox also retains its writing script.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, pinned/braid/Chevalley terminology, and the relevant notion. The hits for braiding are monoidal-category results, not this reductive-group assertion. No project declaration proves the item.

## Sources wanted

WANTED: Brian Conrad, *Reductive Group Schemes*, local archival copy of https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Corollary 5.1.9 and Remark 5.1.10, Proposition 5.1.16, and Isogeny Theorem Steps 1--3/Lemma 6.2.8, printed pp.132--133, 140--142, 204--209, for lem-sfb-rank-two-pinned-braid. Read online in this session; no download or repository write was made.

The inherited request for Tits, *Normalisateurs de tores I*, remains historical source information. This split does not assume that presentation or cite an SGA source. Conrad supplies the root-vector normalization and canonical representatives, not the present braid proof. The proof is marked agent-written accordingly.

## What was wrong or incomplete

The imported item was statement-only. Equality of Weyl images or of adjoint actions does not by itself prove this statement: the two words can still differ in the torus or centre. I avoided both shortcuts. The decisive elementary deduction is that a normalizer word transporting a simple pinned generator to another also transports its uniquely linked opposite generator, hence transports the actual three-factor representative. Thus vector transport can be used without assuming faithfulness of the adjoint representation.

The available `lem-sfb-low-rank-universal-root-coordinates` cites this item, so I did not use it or the classification/isogeny statements above it. A search of the actual dependency graph found no path back to this item from any of the five proof dependencies used here. The standalone rank-two seed supplies precisely the two root-vector normalizations used in A2 and G2, rather than the braid assertion itself. In B2 its definition of the vector at 2a+b suffices; its additional sign assertion is not needed.

The statement is mathematically unchanged; there is no STATEMENT-DISPUTED correction. The existing full-torus centralizer statement applies in arbitrary rank and retains the original character lattice, so reduction to two simple roots does not discard central tori.

## What remains unfinished

Nothing in this one-level split. The cited existing unsplit nodes remain separate queue items. No Lean was written, compiled or built.

## Mathlib and blueprint searches

The inherited search history was retained. I ran msearch anew for the item's canonical pinned lifts, using LeanFinder with two different formulations, LeanSearch, Loogle, and a grep of the Coxeter directory. All services answered. I read the hits and the source around `CoxeterSystem.wordProd_braidWord_eq`, `Mathlib/GroupTheory/Coxeter/Basic.lean:518`. This theorem assumes a Coxeter system of involutive generators. Here n_r squared is r-coroot evaluated at -1, so it does not prove the pinned lift assertion. The RootPairing and GeckConstruction hits concern reflections and Lie matrices. None matches this group-scheme statement.

I searched the whole DAG for rank-two, pinned braid, Tits, root commutators and the seed facts, and read the actual statements of the five dependencies. `tools/blueprint_refs.py search` for braid found only unrelated categorical braiding; rank-two, root string and root commutator gave no blueprint duplicate. I also searched the current `literature/blueprint/latest/blueprint/` directly with ignored files included for pinned braids/Tits representatives/rank-two braids; there is no corresponding imported blueprint statement. The latest pointer is `main-20261024`, commit ef6f9619fdbffa59e88528fb56483d76c70258c8. I read its stability unit and direct-image proof. The item's inherited ancestry describes a much deeper auxiliary input, while the present detailed direct-image proof assembles compactification and preservation results. This split stays below that ancestry and changes none of the unit or chapter route. The existing null ancestor returned by `blueprint_refs.py ancestor` is retained; the precise inherited `from.place` was already filled.

## Not duplicates

No new nodes. The already existing root-string seed, closed-root-set positive functional, commutator support and full-torus centralizer nodes were reused. Routine conjugation/uniqueness and the finite word calculations are steps, not new lemmas.

## Review by Q56

I read delivery-errors B--E in full and checked the proof against the actual five cited statements, not their proofs. For the item I read Conrad's discussion of canonical representatives, the reduction to the two-root full-torus centralizer, and the normalization of rank-two positive root generators. Conrad does not assert the braid relation at the cited normalizer-relator discussion, so this report and `proof_origin` explicitly identify the additional word argument as mine. There are no new node sources to audit.

Step 1 uses the first paragraph of `lem-sfb-small-centralizer-hom-amalgamation`, which really states the closed reductive subgroup with full T, original coroots, base J and inherited pinning. It does not use the homomorphism-amalgamation part. The root-calculus node states that inclusions retain the root exponentials and linked generator; this checks that the representatives do not change under reduction. The seed applies because the resulting semisimple rank is exactly two. I computed the four Cartan matrices from its root lists and checked the product orders; the common-kernel complement argument explains why those orders are also the orders on all of M, not only on the root span. In particular no central torus changes m.

Step 2 checks every hypothesis of the commutator-support theorem. The pairs are (b,+a), (b,-a) in the disconnected case, (d,+b), (d,-b) in B2, and (f,+a), (f,-a) in G2. There are no positive integral mixed sums in any pair, as one verifies directly using the listed coefficient vectors and their negatives. These pairs are closed and contain no opposite roots. The positive-functional node therefore places each pair in a full positive set Sigma. That set meets the closed-set hypothesis of the root-calculus node, giving the product-coordinate subgroup for every enumeration. Choose generators of all the free root modules and their canonical root homomorphisms: the tangent and equivariance hypotheses of commutator support are then exactly those of the root-calculus statement. Its explicit empty-index-set clause supplies the commutations, including for the negative simple root, on all algebra points. This avoids an unrecorded use of a generic Chevalley commutator formula or a field-only commutation assertion.

Step 3 uses only the canonical characterization and unique linked opposite generator in the root-calculus statement. Conjugation changes neither the torus-equivariance characterization nor the differential. Conjugating the three-factor expression still normalizes T; hence the opposite vector is the unique linked one for the transported pinning. This proves equality of group elements even with nontrivial centre. The square formula is the stated n_r squared identity followed by the stated torus equivariance; no root character is replaced by its differential.

Steps 4--7 explicitly compute the required vector transports. A1xA1 uses step 2. A2 uses exactly X_c=Ad(n_b)X_a and Ad(n_a)X_b=-X_c from the seed and the odd Cartan entry. B2 uses X_d=Ad(n_a)X_b, the no-sum commutation and the even Cartan entry -2. G2 uses exactly the seed's signed definitions X_e=-Ad(n_a)X_b and X_f=Ad(n_b)X_e. The two square signs are -1 because the pairings are -3 and -1. The resulting five-factor vector path is X_b, -X_e, -X_f, -X_f, X_e, X_b; this fixes the sign without cancelling a coefficient 2 or 3. The root paths confirm the simple-root hypothesis of step 3 in each case. Multiplication by the normalizer word gives the desired alternating equality. These are short computations from cited statements, so the steps are elementary; no separate word-calculation node is introduced.

Step 8 uses the actual subgroup inclusion and the stated arbitrary base-change compatibility of the canonical exponentials. Linked generators stay linked and are unique after base change; applying the point-group homomorphism therefore gives the required equality over each base-changed ring. A change to the zero ring is harmless because the empty-base point set is a singleton. No inference from geometric-point agreement is used.

As small-case checks, the disconnected root system gives m=2 and commuting factors; A2 gives the familiar length-three identity with the seed's minus sign; B2 and G2 give length four and six using the explicitly displayed paths. Characteristics two and three preserve all formulas, since only multiplication by -1 is used. Disconnected and nonreduced rings cause no step to change: every auxiliary input is over the whole ring. Empty or singleton simple bases have no distinct pair to check. Every non-elementary step is below 2000 characters and cites the exact statements it needs. The report records the source gap, rather than treating Conrad's normalizer passage as a proof of braid. There are no changed hypotheses, weakened conclusions, hollow definitions or unsearched new nodes.

## Validation

The required server-only `review_split` returned PASS (zero new nodes), and `check_dag` returned OK with no finding introduced by the sandbox. The full delivery dry run and push are performed after this report is written.

The first full dry run flagged an unspaced TeX row break immediately before m in the Cartan table as a doubled command. I inserted a space after the row break; the proof and statement are unchanged.
