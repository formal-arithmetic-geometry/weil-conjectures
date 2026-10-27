## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-ind-etale-quotient-two-base-inverse.json`: existing statement, now split into six steps; no Mathlib match for the complete item.
- `citations.json`: one verbatim statement quotation for each of the four step/node citations.
- `searches.jsonl`: actual search-command log, retained as generated.

No new nodes; no new Mathlib leaves. No Lean files written and no compiler, Lake, build, or repository git commands run.

Attachments: none. The project-source search found no declaration tagged with this item, nor a declaration proving its complete two-base quotient comparison. `Algebra.map_into_henselian_colimit`, at `lean/WeilConjectures/RingTheory/MapIntoHenselianColimit.lean:355`, is the already-attached generic tool, not an attachment of this item.

WANTED: none.

The item's statement, statement dependencies, inherited source and blueprint provenance are unchanged. Its initially empty proof is replaced by an inverse construction with three distinct applications of prescribed-residue uniqueness. In particular the proof never treats C as an S-algebra, and never needs to assert that Q is ind-etale. The given ind-etaleness of D is used twice over S, and that of C once over R.

All work is finished apart from the required delivery checks and push. There was no prior sandbox split to repair.

## Sources and searches

I read `literature/stacks-project/algebra.tex`, Tag 08HR (`lemma-map-into-henselian-colimit`, lines 42881–42900) and Tag 08HT (`lemma-uniqueness-henselian`, lines 42902–42919). The former gives the exact unique-map theorem being applied; the latter records the inverse-composite route. I also read Tag 05WS (`lemma-quotient-strict-henselization`, lines 43703 ff.) and the complete statement of `lem-weil-pbc-strictly-henselian-quotient`. That node gives the needed quotient fact for arbitrary ideals in the maximal ideal. Its direct idempotent-lifting interpretation agrees with `def-weil-pbc-henselian-terminology`: a finite Q-algebra is finite over C, and the quotient by the maximal ideal is the same, so the finite-algebra idempotent property transfers.

I read the chapter and unit records and the latest blueprint file `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`. This latest ancestor file is statement-only; the detailed historical Orgogozo/normal-cone place is recorded by the item's inherited `blueprint.from`. This split retains that auxiliary strict-local tube comparison route and makes no change to the chapter or unit.

Whole-DAG tag and concept searches located the already existing `lem-weil-pbc-map-into-henselian-colimit`, `lem-weil-pbc-strictly-henselian-quotient`, `lem-weil-pbc-quotient-local-structure` and `lem-weil-pbc-quotient-residue-field`; only the first two are needed, because the quotient theorem already includes the latter two conclusions. Blueprint searches for `henselian local target`, `ind-etale quotient`, `08HR`, and `quotient henselian`, together with the ancestor command, checked blueprint provenance. No new node was created or elementary step packaged as a lemma.

For the item I ran LeanFinder with two formulations, LeanSearch, Loogle and the logged Mathlib grep. The actual query texts and returned names are in the item and `searches.jsonl`. The Loogle query was rejected for unknown identifier `Ideal.Quotient`; it contributes no evidence of absence. The successful searches return formally-etale square-zero lifting, standard-etale presentations, residue-field constructions and Henselian definitions, not the stated quotient comparison. In particular `Algebra.FormallyEtale.comp_bijective` and `StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot` require a square-zero ideal, which J is not assumed to satisfy. The other LeanFinder formulation likewise finds no complete comparison. Earlier item searches are preserved rather than claimed as searches of this session.

## New nodes

None. The split uses existing general tool statements, with the two off-unit tool uses declared in `split_report.tool_uses` for the maintainer's judgment.

## Review by NJ

I checked the item against 08HR and the inverse argument of 08HT with the two different base rings kept explicit. I opened the statements of both cited nodes and copied them verbatim to `citations.json`; the proof does not take a construction hidden inside either proof.

Step 1 uses the strictly henselian quotient statement with A=C and I=JC. Its hypothesis is verified before invoking it: locality of R to C puts the image of J in the maximal ideal of C, which is an ideal and therefore contains JC. The cited statement supplies precisely the maximal ideal, residue field and strict henselianity of Q. Locality of q is the displayed elementary inverse-image calculation, not an additional theorem left uncited.

Step 2 has no external theorem application: quotient factorization is its universal property, S-linearity is checked by lifting an element of S to R, and the equation of reductions follows by precomposing with the surjection q. Taking the kernels of these reductions proves locality. This also checks that the residue identifications used later are the specified ones, rather than unspecified isomorphisms of fields.

Step 3 applies the cited map theorem to base S, source D and target Q. D's filtered-etale presentation is a hypothesis of the item, Q is henselian by step 1, and the source prime is the maximal ideal of D. I checked the inverse image in S is m_R/J and wrote why the two maps S to K agree: precompose with the surjection R to S and use the hypothesis. Thus the identity on K is an algebra map over the required residue field. This gives both existence and the full claimed uniqueness of local v.

Step 4 uses the same theorem with base S, source D and target D. Both candidate endomorphisms are local S-algebra maps with identity residue map, and D is henselian by hypothesis. It establishes only the first composite identity; there is no circular use of the other one.

Step 5 uses the theorem over R with source C and target Q. C is ind-etale over R by hypothesis, and Q is henselian. Both inverse images are m_R. The original compatibility of the two maps R to K is exactly what gives the required compatibility on kappa(m_R). The output is vu=q, not an equality involving a nonexistent S-algebra structure on C.

Step 6 is elementary surjection cancellation, written elementwise. It proves the second inverse identity from step 5, then surjectivity of u and equality of its kernel with JC. Thus all clauses of the original statement are established, including the unique S-factorization and the uniqueness of v.

Against delivery-errors B–E: there are no statement-only-node formatting, duplicate or relabelling issues because no nodes were added; the statement stays self-contained and unchanged. Each non-elementary application is a cited statement with a verbatim quotation. The ring-map factorization and cancellation arguments are short elementary steps, not hidden lemmas. Every proof step is under 700 characters, so none hides a long-step comparison. The two generic tools do not depend on the item. No SGA source is used.

I tested J=0 (the assertion becomes the usual residue-compatible ind-etale henselian isomorphism), J=m_R (the same proof applies over the residue field), and a non-nilpotent ideal J=(t) in R=k[[t]] with separably closed k and C=R, D=k. The last case explains why square-zero lifting hits do not suffice. J cannot make Q the zero ring since JC is contained in a proper maximal ideal. No Noetherian, finite-generation, completeness, or square-zero hypothesis entered the proof. There was no statement dispute and no weakening to make the argument work. My review corrected no mathematical assertion: it supplied the missing proof and made each base, prime and residue compatibility explicit.
