# Stage-1 worker report: lem-trf-etale-tensor-splitting

## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-tensor-splitting.json — statement, split into five steps; no exact Mathlib match, all proof dependencies already exist as Mathlib leaves.
- citations.json — six step/node entries, quoting the cited statements verbatim.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None for this item. I searched the project WeilConjectures/ tree for the blueprint id and tensor/localization, multiplication, etale, splitting and Fitting terminology. Algebra.Etale.exists_algEquiv_prod_of_algHom at WeilConjectures/Mathlib/RingTheory/Etale/Section.lean:83 is sorry-free in its displayed proof, but assumes the whole source algebra is etale over the base. Here T need not be etale over B. The existing DAG already records that project theorem for a different, stronger-hypothesis section-splitting situation. The self-tensor Mathlib theorem Algebra.FormallyUnramified.exists_algEquiv_prod also has a different hypothesis and a different tensor algebra. Neither attaches this item.

## WANTED

None. The needed sources are present in literature/stacks-project/.

## What was wrong or missing

The imported node had an empty proof. Its statement is true and remains byte-for-byte unchanged, with all finite-free and localization hypotheses retained. The finite-free hypothesis is not needed by the decomposition argument itself; it is used by the parent Fitting-ideal argument and has not been removed.

The important distinction is between etaleness of the surjection T -> B and etaleness of the structural map B -> T. The former follows by cancellation over C and is what Stacks 0812 uses. The latter is not assumed and cannot be supplied by the section-splitting theorem. For example, over a field k take C=k[x]/(x^2(x-1)) and h=x. Then C is finite free, C_h=k is etale, and T=C has a nonreduced complementary factor k[x]/(x^2), so T is not etale over B=k. The delivered proof therefore uses the existing surjective-etale kernel criterion, not the inapplicable global-etale section theorem.

The inherited blueprint ancestry runs from the contracting-correspondence specialization branch through the already split Fitting-ideal argument. I read the current main-20261015 ancestor proof, the chapter and the unit. This is a ring-theoretic tool below that branch; no chapter, unit, source route or ancestry is changed. Searches of the whole imported blueprint for tensor splitting and 0812 found no equivalent blueprint statement, so same_as remains [].

## What could not be finished

Nothing outstanding in the split. No Lean was written, no compiler or Lake tool was run, and no shared repository or launcher file was changed.

## Not duplicates

No new node was created. Existing nodes for principal localization, etale base change and cancellation, surjective-etale kernels, finitely generated idempotent ideals and tensor pushouts supply all non-elementary inputs.

## Review by N0

I read Stacks flat.tex, Tag 0812 (lemma-trick-fitting-ideal), including the multiplication-map and quotient paragraphs, and algebra.tex, Tag 00U7 (lemma-map-between-etale), Tag 00U8 (lemma-surjective-flat-finitely-presented), both proofs, and Tag 00EH (lemma-ideal-is-squared-union-connected), statement and proof. There are no new nodes with additional sources to audit. I opened each of the six cited DAG files and checked its statement, rather than using an argument buried in its proof. I inspected the project Section.lean candidate and Mathlib Unramified/Basic.lean:334-347 and Etale/Basic.lean:135,242-254 to distinguish candidate statements from the needed assertion. All new searches were executed using msearch.py, and their actual log records are appended to the imported searches without inventing a query or converting a service error to absence. Two semantic phrasings, Loogle, grep and LeanSearch were tried; the results give ingredients or stronger hypotheses, not a direct match.

Step 1 uses the tensor-pushout node's clause (2): its statement explicitly supplies the map on pure tensors and the two coprojection composites. This verifies that mu is B-linear for the second factor, not just A-linear, and that every b has preimage 1 tensor b. The step is elementary after that universal-property statement.

Step 2 uses the base-change node with its R=A, A=B and S=C. Its statement really concludes Spec(C tensor_A B) -> Spec C is etale through c -> c tensor 1, the first factor. The principal-localization node really states that Spec C_h -> Spec C is an open immersion. Cancellation node clauses (1) and (3) then give etaleness of Spec mu because the composite with Spec i is Spec lambda. I checked the contravariant order carefully. No assumption of etaleness of A -> C, B -> T or freeness is smuggled into this step.

Step 3 applies the surjective-etale kernel node to the ring map mu:T -> B. Surjectivity is Step 1 and spectrum-etaleness is Step 2, exactly its two hypotheses; its statement explicitly gives both finite generation and I^2=I. The finitely generated idempotent ideal node's clause (1) then explicitly supplies e^2=e and I=eT. This is not a definition cited in place of a theorem. The remaining equalities for q=1-e are ring identities.

Step 4 constructs the commutative corner ring D=eT with its own identity e, including the B-structure b -> e j(b); it does not give the ideal the ambient unit. I checked multiplication, identities and B-linearity of theta directly. Step 5 checks the proposed inverse on both sides. The key calculation is that t-j mu(t) is in eT and is killed by q; this proves q j mu(t)=qt and hence the inverse identity. The complementary factor and projection compatibility are thus established in the item's steps rather than moved to a new node restating its clause.

I checked delivery-errors B--E point by point. B: no new statement-only file, undefined new notion, unchecked Mathlib leaf, invented search, or new blueprint ancestor occurs; JSON has ordinary TeX escapes. C: every non-elementary assertion has an existing cited node that states it; citations.json quotes are copied from those statements. The two algebra-map/inverse computations are written out as elementary steps, all uses are in proof_deps, and the six dependencies are existing Mathlib tools, so no off-unit proof replacement or new cycle is introduced. D: the item contains the actual kernel, idempotent, product and inverse argument; it does not just invoke a new copy of its conclusion. E: I tested C=0 (rank zero), h=0 (B=T=0), A=C and arbitrary localization (mu is an isomorphism and D=0), h a unit with C etale, and the nonreduced-complement example above. The zero ring is permitted in the corner construction, with e=0 as its identity. The first projection equals the originally specified mu in all cases. Every step is shorter than 2000 characters; none hides a comparison lemma or a non-elementary standard argument.
