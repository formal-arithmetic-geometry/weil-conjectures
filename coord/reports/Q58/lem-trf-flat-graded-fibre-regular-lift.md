# Q58: lem-trf-flat-graded-fibre-regular-lift

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flat-graded-fibre-regular-lift.json`: statement, split in six steps, unchanged statement; not a Mathlib leaf. No new nodes.
- `citations.json`: one entry for every node occurrence in every proof step, with quotations copied from the cited statements.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

## Attachments

None. Searches of the project source under `lean/WeilConjectures/` for the blueprint tag, initial-form regularity and associated-graded fibre terminology found no declaration stating the item. Existing sheaf-associated-graded constructions do not assert this local-ring lifting theorem. The existing generic module criterion is already attached to `flat_mod_injective` in `WeilConjectures/RingTheory/FlatModInjective.lean`; this delivery does not propose a new attachment.

## WANTED

None. The needed Stacks source is present.

## Corrections and route

The imported item had a statement and searches but no proof. Its statement is correct and is unchanged. Its three supporting results already exist: `lem-weil-pbc-finite-flat-local-free` (Mathlib), `lem-weil-pbc-flat-mod-injective` (split), and `lem-weil-pbc-krull-intersection-jacobson` (Mathlib). Creating new nodes for them would duplicate existing statements. The remainder is explicit elementary algebra rather than new nodes restating the item's clauses.

I read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` unit and `lem-trf-local-term-locality.proof.md`. The current blueprint follows contracting correspondences, while the item's existing ancestry records the historical nearby-duality/alteration branch and its ILO VIII synchronization descendants. This delivery proves the assigned lower filtered-algebra input on that recorded ancestry; it changes no unit or chapter and invokes no SGA source. The module injectivity criterion is declared as a generic off-unit tool in `split_report.tool_uses`. The other two algebra inputs are existing Mathlib leaves.

## Not duplicates

No new nodes. Searches of all `dag/nodes/` for Stacks tags 00NZ, 00ME, 00IP and 00IQ and for finite-flat freeness, residue injectivity and Krull intersection located the three reused nodes. Whole imported-blueprint searches with `tools/blueprint_refs.py search` for `finite flat`, `Krull`, `regular initial`, `flat graded` and `residue-fibre` found no blueprint statement equal to the item. The nearest blueprint ancestor was checked with `ancestor`: `lem-trf-local-term-locality`. Its existing precise ancestry and place were preserved; `same_as` is empty.

## Review by Q58

I read Stacks `algebra.tex`, Tag 00NZ (`lemma-finite-flat-local`, statement and proof beginning at line 19223), Tag 00ME (`lemma-mod-injective`, lines 23424--23477), Tag 00IP (`lemma-intersect-powers-ideal-module-zero`, line 12241), and Tag 00IQ (`lemma-intersection-powers-ideal-module`, line 12257), including their hypotheses. These are the source inputs for the agent-written filtered-algebra assembly; none by itself is represented as the complete item. There are no new-node sources to review.

For step 1 I opened `def-weil-pbc-noetherian-ring` and `def-weil-pbc-associated-graded-ring`. The first says every ideal is finitely generated; the second specifies the actual quotients, their coefficient action and multiplication. Thus the generators of the ideal I^j descend to generators over A, and the quotient ideal correspondence proves that A is Noetherian local. No theorem about arbitrary finite modules is silently taken from the definition of Noetherianity.

For step 2 I read `lem-weil-pbc-finite-flat-local-free`: its precise hypotheses are a local ring and a finitely generated flat module, and its conclusion is freeness. Step 1 supplies finiteness and locality. The flatness of the summand is proved before invoking this node: tensor a kernel element with the homogeneous inclusion, use injectivity for G, and retract by the homogeneous projection. The cited tensor-product definition explicitly supplies functoriality and the identity law used here. Finally I wrote why the obtained basis is finite, since the cited node says free rather than explicitly finite free. I also read Mathlib `RingTheory/LocalRing/Module.lean:303--309`, which states the recorded 00NZ match.

Step 3 uses only the associated-graded multiplication and the tensor-product universal property, both read in the cited definitions. The two formulas for M tensor k and M/nM are explicit inverse maps, including independence of a coefficient lift and vanishing on nM. Their compatibility with multiplication is verified on pure tensors. Importantly, the fibre summand maps are injective because they have tensor-induced retractions; the proof does not assume tensoring an arbitrary injection is exact. Multiplication by h injective on the entire fibre therefore gives exactly the quotient-map injectivity needed next. This elementary identification is part of the proof rather than an extra node.

For step 4 I opened the full statement of `lem-weil-pbc-flat-mod-injective` and checked it against Stacks 00ME. Its base and target ring are both A, the ring map is the identity and hence local, N is G_j and M is G_(j+n). A is Noetherian, N is finite, M is flat, and the residue quotient map is injective by step 3. It concludes precisely that this A-linear multiplication map is injective. I do not use an unproved assertion that an arbitrary tensor fibre reflects injectivity, or the cokernel-flatness clause. The off-unit use is a generic local algebra tool, not a replacement of the unit's geometry.

Step 5 cites the associated-graded definition for the precise equality of the product of the two classes with the class of ab. I wrote a full induction starting from I^0=R: injectivity on the jth piece forces the class of b to vanish, advancing b from I^j to I^(j+1). In particular there is no assumption that b has a finite order before separation has been applied.

For step 6 I opened `lem-weil-pbc-krull-intersection-jacobson`: it requires a Noetherian ring, an ideal in its Jacobson radical and a finitely generated module. Here those are R, I contained in the unique maximal ideal, and the cyclic module R. Its statement is exactly that the intersection is zero, which kills b from step 5. The local hypothesis identifies the Jacobson radical with m; neither reducedness nor a characteristic restriction is introduced. I checked the recorded Mathlib theorem in `RingTheory/Filtration.lean:416--423` as well as Stacks 00IQ(2).

I tested I=0: G_0=R and higher pieces vanish; positive n cannot satisfy the regular-fibre premise over a nonzero residue field, while n=0 reduces to a unit residue class. For n=0 and general I the same multiplication and induction work without increasing the degree by n, since the filtration step increases j. Nilpotent I gives vanishing high pieces, so the induction terminates as expected. A field with I=0 satisfies the conclusion for nonzero a. In the nonreduced test R=k[epsilon]/(epsilon^2), I=(epsilon), the degree-one initial form is not regular on the fibre (its square is zero); it cannot incorrectly certify epsilon. Finite-free pieces of rank zero also cause no difficulty: the corresponding injectivity assertions have zero domain. These checks find no statement dispute.

I checked delivery-errors B--E: self-contained unchanged statement; no new nodes or invented Mathlib matches; all non-elementary inputs are existing statements with sufficient hypotheses; no circular dependence on the item's parent; complete induction; and no hidden transport or unstated comparison. Every step is shorter than 2000 characters. `citations.json` uses verbatim statements, checked against the actual files, rather than quotations invented from their proofs. New Mathlib searches were run only with the required msearch command, including two semantic phrasings, Loogle, grep and LeanSearch. I read the hits: regular-sequence flat base change assumes pre-existing base regularity, and residue-field linear-independence lifting is only an input toward the present theorem, not a match for all its clauses. Queries/results are recorded exactly from `searches.jsonl`; the original imported searches are retained.

## Verification and unfinished work

The server-side `srvcheck.py ... check_dag` exited successfully: `check_dag OK: no finding introduced by the sandbox or on its nodes`. No Lean file was written, and no compiler, Lake or build command was run. No repository or launcher file was changed. No mathematical work remains beyond independent maintainer review; the required delivery dry run and push follow this report.
