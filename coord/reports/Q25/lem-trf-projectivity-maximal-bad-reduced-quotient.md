# Worker report: lem-trf-projectivity-maximal-bad-reduced-quotient

## Files written

- dag/nodes/sec-trace-formula/lem-trf-projectivity-maximal-bad-reduced-quotient.json: statement, split into five proof steps; no Mathlib match for the whole statement.
- citations.json: eleven step/node citations, quoting the current cited statements verbatim.
- report.md and searches.jsonl: review and actual search records.

New nodes: 0. New Mathlib leaves: 0. The existing maximal-element and quotient-tensor nodes are Mathlib leaves; they are reused, not counted as new.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by maximal bad, bad quotient, projectivity/radical and nilpotent/projective terminology. The Popescu maximal bad quotient theorem concerns ind-smoothness, not this statement. No project declaration found gives all clauses of this item with a finished proof. No Lean was written and no compiler or build was run.

## WANTED

None. Stacks flat.tex and algebra.tex are available locally.

## Corrections and route

The imported statement is unchanged and is a faithful extraction of the first paragraph of Stacks Tag 05FS, lemma-fibres-irreducible-flat-projective. It was statement-only. The proof now supplies the maximal bad ideal, proves its radicality using finite generators and nilpotent lifting, and checks every quotient and fibre clause. There is no STATEMENT-DISPUTED claim.

I read the chapter and unit records and the current latest blueprint files for sk-i-curve-zero and lem-trf-local-term-locality. The latest blueprint has replaced the historical semistable-alteration branch by a direct contracting-correspondence argument; its present proof does not mention the old projectivity input. This delivery retains the dispatched algebra statement and its historical ancestry; it does not change the unit or chapter route or pretend that the current proof still contains the old paragraph. The split_report records this discrepancy explicitly. No SGA source is used.

## Searches and reuse

Read the existing item searches, then ran and read five fresh logged searches through msearch.py: LeanFinder with two different phrasings, Loogle on Module.Projective and Ideal.radical, LeanSearch for the maximal radical quotient, and grep for maximal-bad/radical-projective combinations. All services answered. The finite-presentation projectivity candidates require a finitely presented module, unavailable from finite type as an algebra (e.g. R[x] has infinitely many R-basis elements). I read the pinned Mathlib declarations in Flat/EquationalCriterion.lean:287 and LocalProperties/Projective.lean:131-133,168-170. None matches the item. The grep hits concern elliptic reduction and the unipotent radical of a projective group, not this question.

DAG searches by nilpotent/projective, nilradical/nilpotent, Noetherian maximal element, and the source labels found the reusable lem-trf-local-nilpotent-projective-flat-lift and lem-weil-pbc-noetherian-ideal-set-maximal. The tensor-over-quotient-ring node was opened and reused for its actual natural isomorphism clause (2). Blueprint searches for 'maximal bad' and 'nilpotent projective' found no blueprint nodes. The ancestor command confirms lem-trf-local-term-locality. No new node was created: nilpotence of the finitely generated radical quotient, Noetherianity of a quotient, and transport of projectivity through explicit quotient isomorphisms are short arguments in the item, not separate work items.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs to distinguish.

## Review by Q25

I read Stacks flat.tex:2178-2207 (05FS, lemma-fibres-irreducible-flat-projective), including the first proof paragraph, and algebra.tex:18923-18960 (05CG, lemma-lift-projective). The latter assumes a nilpotent ideal, a flat module and projectivity of its quotient; it does not assume finite generation of the module. These are exactly the hypotheses used in step 3. The current item and source both assume a Noetherian base and a finite type flat algebra with nonzero geometrically integral fibres. No hypothesis or conclusion has been changed.

Step 1 cites the actual injectivity definition of flatness in def-weil-pbc-flat-ring-map, the natural quotient tensor isomorphism in clause (2) of lem-weil-pbc-tensor-over-quotient-ring, and the generator definition in def-weil-pbc-finite-type-algebra. I opened all three statements. Naturality identifies the two maps, so injectivity over the quotient follows directly; this is not an inference from the word 'flat' alone. The finite type assertion follows by reducing the polynomial expressions for the original generators.

Step 2 cites lem-weil-pbc-noetherian-ideal-set-maximal, whose statement allows any nonempty set of ideals, not merely prime ideals or an ideal family closed under unions. The family is nonempty because the original algebra is nonprojective. I checked the cited projective definition includes lifting along every surjection, which proves directly that the zero module is projective and excludes the unit ideal. No Zorn argument or extra finiteness is hidden here.

Step 3 cites def-weil-pbc-noetherian-ring precisely for finite generation of the ideal sqrt(I), and lem-trf-local-nilpotent-projective-flat-lift precisely for the conclusion that a flat module with projective reduction across a nilpotent ideal is projective. I opened its full statement and compared it with 05CG. The explicit exponent N=1+sum(n_i-1) proves nilpotence by expanding products in the generators; no separate nilradical theorem is invoked. The module is S/IS over R/I, the nilpotent ideal is sqrt(I)/I, flatness is step 1, and the reduced projective module is S/(sqrt(I)S), projective by strict maximality. The displayed kernel calculation verifies that this is the reduction the lifting lemma actually asks for. This avoids citing a projective-module-lifting existence theorem, which alone would not prove the needed assertion.

Step 4 uses the exact finite-generation definition of Noetherianity and the exact lifting characterization of projectivity, both opened. Generators lift from each ideal of R/I to its inverse image in R. Radicality proves reducedness directly on representatives. The maps between the two-stage and one-stage quotients are explicitly given, and the lifting property transports through these compatible ring/module isomorphisms. A nonzero ideal downstairs has strictly larger inverse image upstairs, justifying maximality. B remains nonprojective by membership of I in the bad family.

Step 5 uses def-weil-residue-field for the local-ring quotient notion and clause (2) of lem-weil-pbc-tensor-over-quotient-ring for exactly its tensor identification, now with the quotient-ring module K. I checked the prime inverse image and I contained in p, and wrote out the common residue-field fractions and both tensor-factor swaps. The latter preserve multiplication on generators, so the isomorphism is of rings, sufficient to carry nonzeroness and integrality. The original hypothesis quantifies over every extension of kappa(p), exactly including the given extension of the identified kappa(q). No assertion that every prime of R contains I is used.

For B1-B10 and C1-C8, there are no new statement-only objects to audit, no duplicate nodes, no undeclared off-unit statement tools (the off-unit proof statements used are existing Mathlib leaves), and all eleven citations are quoted verbatim in citations.json. The only non-elementary steps are maximal selection and nilpotent lifting, each with the needed statement node. Other arguments are short consequences of definitions or the cited quotient tensor identity. For D1-D5, the item itself carries the construction and contradiction; nothing is moved to a renamed copy and no dependency returns to the item. For E1-E7, I checked the ring and module bases in the lifting application, quotient prime and residue fields, and all strict/non-strict ideal inclusions. Every step has fewer than 2000 characters.

Small cases checked: R=0 is excluded by nonprojectivity (every module over it is zero); I=R cannot be bad; I=0 is permitted and gives the same ring when reduced; sqrt(I)=0 is handled by the empty generating set and N=1; square-zero radical generators give the stated pigeonhole nilpotence bound; J=A is included and its quotient is zero/projective. Finite type is never mistaken for a finite R-module: the polynomial algebra R[x] illustrates why the Mathlib finite-presentation projectivity hits are inapplicable. For the residue calculation, R=k[e]/(e^2), I=(e), q=(0) gives the common field k and the usual base-changed polynomial fibre. No new statement needs a counterexample repair.

## Unfinished work

None in this one-level split. The required server dry run and direct delivery are performed after this review; any failures will be repaired before delivery.
