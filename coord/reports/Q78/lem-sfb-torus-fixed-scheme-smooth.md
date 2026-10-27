## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torus-fixed-scheme-smooth.json: item, statement unchanged, split into eight proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-fixed-local-ideal-jets.json: new statement-only lemma, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-regular-quotient-parameter-approximation.json: new statement-only lemma, unsplit, no Mathlib match.
- citations.json: one verbatim statement quotation for every node used by every item step.

Two new nodes, zero new Mathlib leaves. Existing Mathlib and project nodes are reused. No Lean was written or compiled. All writes were confined to the assigned sandbox.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by fixed subscheme, fixed scheme, torus and linearly reductive terminology. There is no declaration of this result. Also inspected the additional Sheaf hits: they concern toric realizations and group structures, not the fixed-scheme smoothness statement. The upstream declaration search is not being replaced by an assumption that a sorry declaration is finished.

## WANTED

None. Milne's actual PDF and the Stacks sources used here are available locally.

## Corrections and route

There is no statement dispute and no change to any hypothesis or conclusion. The original node had no proof. Its chosen Milne route is retained: Theorem 13.1, Lemmas 13.3, 13.4 and 13.6, and Theorem 13.7, printed pp.254--256. I read those pages and Theorem 12.12 on pp.234--235. Rather than citing Theorem 13.1 through a new name, the item carries the actual weight-lifting and finite-jet ideal argument.

The chapter and unit records were read. This is a supporting input deep below the alteration step of the constructible stability unit, not its key node; no unit realization is written. The latest blueprint is literature/blueprint/latest (main-20261024). Blueprint searches for fixed scheme, fixed ideal, finite jets, regular system, regular quotient, parameters and diagonalizable found no equivalent imported assertion. The ancestor command returns None for this inherited ancestry, and the item's existing null ancestor and via chain are retained. This is inherited metadata, not a proposed route change. Generic scheme tools outside the unit are individually declared in split_report.tool_uses.

The source's local proof works for smooth affine finite-type schemes without connectedness or irreducibility: it only examines the regular local ring at each rational fixed point. I do not add either condition. The statement is already scheme-theoretic, with fixedness after every algebra extension; checking only set-theoretic fixed points would be insufficient.

## Searches

Every new-node Mathlib search was run through the required msearch.py and its exact query and returned names/digest are recorded in the node and searches.jsonl. Both natural-language phrasings were tried for each input, together with Loogle and source grep. The fixed-ideal queries return finite abstract-group invariant extensions and coinvariant modules. Invariant/Basic.lean:405--465 was read: its residue-field endomorphism-extension statements do not identify a fixed subscheme or produce rational jet actions. For regular quotients the search returns regular sequences, quotient dimensions and the cotangent characterization of regular local rings. RegularLocalRing/Defs.lean:42--76 was read. None supplies the varying-parameter approximation criterion. The first Loogle regular-quotient pattern reported an unknown identifier; that diagnostic is retained and a valid quoted-name query was run afterward. No unavailable service is represented as an absence result. The item itself was searched again with both semantic services, Loogle and grep.

## Not duplicates

lem-sfb-torus-fixed-local-ideal-jets vs lem-sfb-torus-fixed-scheme-smooth: the new lemma identifies a local quotient and constructs rational finite jets for an arbitrary affine finite-type scheme, without any smoothness or regularity conclusion; the item's weight-lifting and regularity argument remains in its proof.

lem-sfb-regular-quotient-parameter-approximation vs lem-weil-pbc-regular-local-quotient-independent-generators: the existing statement assumes the quotient is regular and produces independent generators of its kernel; the new statement deduces quotient regularity from compatible ideal equalities at each finite order, allowing the parameters themselves to vary with the order.

lem-sfb-regular-quotient-parameter-approximation vs lem-trf-regular-local-complementary-quotients-tor: the existing statement assumes two regular quotients with complementary dimensions and proves a Tor/Koszul conclusion; it does not give the finite-order criterion for regularity of an unknown quotient.

The two new sources are Milne lemma numbers, not Stacks tags. No existing Milne 13.3/13.4/13.6 source node was found. Searches of the full DAG by statements and titles, including regular parameter and graded-ring terminology, did not find the approximation result. The already-existing G_m representation-weight-basis node is deliberately reused instead of introducing a duplicate torus representation theorem.

## Review by Q78

I checked B--E of delivery-errors.md against the actual files, not only their shape. Both new statements introduce every object, give their hypotheses, use TeX once, cite definition nodes for their scheme notions, and have no proof or proof dependencies. They are proper inputs: neither asserts smoothness of a fixed scheme. No elementary weight-selection fact is made into a node. No SGA source is used.

For the item I read Milne's proof through 13.7 and the decomposition proof of 12.12. For the local-ideal/jets input I read 13.4 and the first paragraph of 13.6. The first is stated there for automorphisms; for a split torus the affine scheme-theoretic strengthening uses coefficients of the coaction. Indeed Laurent polynomials are separated by evaluations on (k^times)^r over an algebraically closed, hence infinite, field. On every finite coefficient span, evaluation linear functionals span its dual. Consequently the ideal of coaction coefficients equals the ideal of rational-point differences. Localizing at a fixed rational point gives the difference ideal in the new statement; differences of fractions follow by the quotient formula. The ideal of that rational point is a coideal, so the finite quotients and their ideal subspaces have the asserted coactions. Localization does not change a finite quotient supported at that point. These arguments need no reducedness of X or F. I did not substitute Milne 13.5, whose hypothesis that the constant-point fixed scheme is smooth would be circular at this stage.

For the regular-approximation input I read Milne 13.2 and 13.3. The new statement uses a cotangent basis rather than naming a regular system of parameters; Nakayama identifies its lifts with such a system. For each degree choose the tuple at that order. The truncated equality identifies both cotangent spaces and that graded piece of the quotient with those of the regular parameter quotient. Its canonical symmetric-to-graded map is an isomorphism in that degree; doing this for every degree proves regularity and dimension d-s as in 13.3. I also read Stacks algebra.tex Tag 00NO (lemma-regular-graded), and the parameter quotient argument preceding Tag 00NR, to check the algebra behind the source. There is no requirement of a single compatible tuple at all orders.

Step 1 uses exactly the finite-type-over-Noetherian finite-presentation statement of lem-weil-pbc-finite-type-noetherian-finite-presentation. A field is Noetherian. The quotient and functor base-change statements are written out, rather than assuming fixed rational points automatically base change.

Step 2 uses the two actual conclusions of lem-sfb-scheme-large-algclosed-jacobson: rational closed points and density in every closed subset. It is applied over the given algebraic closure, so the enlarged field still splits the given torus. I read Stacks varieties.tex Tag 0479 (lemma-make-Jacobson). The field-flatness node and the locally-finitely-presented smooth-flat-base-change node give smoothness of the ambient base change; the smooth-scheme-over-field-regular node then gives regular local rings in every dimension. I read their statements and Stacks Morphisms Tag 02V4, case (2), and Varieties Tag 056S. The curve-only node lem-sc-smooth-regular is deliberately not used.

Step 3 takes both the quotient identification and rational finite-jet representation from the new local lemma, whose statement explicitly provides them. It uses the regularity already established in step 2, not an unproved smoothness property of F.

Step 4 cites the existing G_m representation-weight-basis statement, which is valid in every characteristic. The iteration over commuting factors and the extraction of the appropriate weight component of an arbitrary preimage are explained. This proves the splitting required here without importing semisimplicity of an abstract representation of T(k), which would be false in this generality. The representation is the rational finite-dimensional one of step 3.

Step 5 is an elementary calculation from the objects established in steps 3--4. It proves generation of the truncated algebra by increasing residual degree, then proves both inclusions for the difference ideal. A nonzero weight may have exponent divisible by the characteristic; its Laurent monomial still has a value other than one over an algebraically closed field. The comparison is only in each finite quotient; I do not assert that the u_i in the full local ring are eigenvectors. This repairs the gap that a loose paraphrase of Milne's last paragraph could leave.

Step 6 checks every hypothesis of the approximation lemma: A is regular local, J lies in its maximal ideal, the same s is used for all orders, each lifted tuple has basis images, and the ideal equalities were proved in step 5. Thus the lemma says exactly what is needed.

Step 7 uses the existing regular-separable-affine-smooth-neighbourhood statement on the whole affine F_K, with finite-type coordinate algebra and residue field K/K, which is finite separable. I read Stacks Algebra Tag 00TV (lemma-separable-smooth). The maximal smooth open node says there really is a largest smooth open; I read spaces-morphisms.tex Tag 0DZI. Its closed complement contains no closed point, so the Jacobson property previously supplied makes that complement empty. Mere density in the entire scheme would not justify this inference.

Step 8 cites the actual field-extension flatness and surjectivity nodes, stability of surjectivity under base change, the pointwise smooth base-change equivalence for a locally finitely presented morphism with flat base change, and smooth locality on the source. No finite-presentation hypothesis on K/k is needed. The lfp assumption on F/k is supplied by step 1. I read all cited statements, and also Algebra Tag 02UQ for the field-extension implication. citations.json quotes the full verbatim statement of each cited node so that all clauses being used are visible.

I tested the new local statement on the trivial action on a nonreduced affine scheme (J=0 and the lemma does not falsely claim regularity), and on the scaling action on affine space (the nonzero coordinates generate the fixed ideal). For the parameter criterion s=0 includes J=0, s=d includes the maximal-ideal quotient, d=0 forces J=0, and the n=1 condition alone is deliberately not asserted to suffice. For example in k[[u,v]], J=(u^2) cannot be treated as a regular quotient merely from an approximate tangent dimension: it fails the higher-order s=0 equalities. For the item I checked r=0, X or F empty, trivial tangent action and entirely nontrivial tangent action. All are admitted by the proof. Every step is under 1000 characters, so no non-elementary step exceeds the 2000-character review threshold. No deferred fact is hidden in a long step.

## Unfinished work

No part of this stage-1 split remains unfinished. The two new nodes are intentionally unsplit, as required for one-level delivery. The server review_split invocation passed; the full delivery dry run and push are performed after this report is written.
