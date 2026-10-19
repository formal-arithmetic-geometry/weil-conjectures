# Q09: lem-real-weil-twisted-paths

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-real-weil-twisted-paths.json: statement split into nine steps; unchanged statement; no Mathlib match.
- citations.json: one verbatim statement quotation for each cited node in each step.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Existing finite-cover transport, fundamental-group functoriality, Weil exactness, and finite-field Frobenius statements suffice. No unit record is changed: this is not the unit's key node.

## Attachments

None. I searched WeilConjectures in the read-only slopmaster2 checkout for the item tag and twisted-path/Weil-group terminology, then read the fundamental-group FrobeniusTransport and FrobeniusElement interfaces. Existing declarations cover such pieces as reparametrization, constant-cover Frobenius and arithmetic transport, but no declaration gives the whole integer-indexed twisted-path group, its isomorphism, and the closed-point return path. Generic MonoidHom.exact_weilGroupDeg belongs to the already attached lem-wf-weil-group-exact-sequence; it is not an attachment for this item.

## WANTED

None. The Stacks sources and Deligne Weil II are present.

## Problems found and repairs

The imported item had no proof. Its statement is correct, including the order g^m(p) composed with q and the positive degree of geometric Frobenius; no statement dispute or change is required. The principal risk was using the construction in the proof of lem-wf-finite-etale-weil-transport as though its statement normalized its arithmetic action. That statement asserts existence and conjugation compatibility, but does not assert normalization. Step 6 uses only existence and naturality; step 7 obtains the desired arithmetic value by an independently stated exact sequence. Another risk was assuming all arithmetic and geometric finite covers are the same category; the proof uses restriction and the explicitly injective geometric subgroup instead.

The imported proof of the existing exact-sequence node informally writes (Phi_X,Phi_X) in a fibre product without first producing an arithmetic lift. I do not reuse that argument or change that other worker's file. Its exactness statement is the true result supplied by Stacks 0BTX and the Weil inverse-image definition; its stated surjectivity and kernel clauses are all this delivery uses. The source was checked directly, including its geometric connectedness and qcqs hypotheses (separated finite type over a field is qcqs).

The current blueprint p-real-operations proof has a coefficient/sheaf-operator assertion beyond this item's remit. This delivery realizes only the coefficient-free decomposition-group and degree-e class needed there, and does not claim a stalkwise sheaf-Frobenius comparison.

## Unfinished work

None for this split. No new statement-only nodes are required.

## Blueprint and duplicate searches

Read dag/chapters/sec-purity-real-sheaves.json and dag/units/sk-p-real-operations.json, together with the main-20261015 p-real-operations statement and proof. The inherited ancestor p-real-operations is correct. Ran tools/blueprint_refs.py ancestor on the item and searched the whole blueprint for "twisted" and "fibre functor", and the DAG for the cited Stacks tags, finite-cover descent, Weil transport and fundamental-group terminology. No blueprint node already states this whole result; same_as remains []. No new node is introduced, so there are no new/existing same-tag pairs requiring a Not duplicates section.

## Mathlib searches

Preserved the item's inherited search records and added the searches actually run by Q09 through msearch.py, recorded in searches.jsonl. LeanSearch, Loogle, two distinct LeanFinder phrasings and grep were all available. Hits include finite-field Frobenius, absolute Galois groups and abstract Galois-category prorepresentability. Read Mathlib/CategoryTheory/Galois/Prorepresentability.lean:329 (autIsoFibers, an isomorphism on pointed Galois objects, not the present scheme statement), IsFundamentalgroup.lean's interface, and FieldTheory/Finite/Basic.lean:363-370 (field Frobenius). These do not identify the Frobenius-twisted path group of a scheme or its closed-point return path by a one-line specialization. The item's Mathlib verdict is no match. No search was fabricated or inferred from an unavailable service.

## Review by Q09

I read Stacks pione.tex at 0BN5 (lemma-functoriality-galois), 0BND (theorem-fundamental-group), 0BTV (lemma-limit), and 0BTX (lemma-ses-field), and Deligne Weil II (1.1.7)-(1.1.8), (1.1.10)(ii), (1.1.12)-(1.1.13), pp. 150-153. Deligne fixes the inverse-q Frobenius convention, the Weil inverse-image definition and the local Frobenius interpretation. The Stacks fibre-functor descriptions supply the finite-cover meaning of these constructions. The explicit formulas here are agent-written, so proof_origin is agent. No prohibited source route is used. For the finite-field input I also read the main-20261015 base-field Galois-group proof's first paragraph and the cited finite-field Mathlib declarations. There are no new nodes with additional sources to review.

For step 1 I opened the statements of def-weil-frobenius-detailed, lem-galois-pi1-functoriality and def-weil-pbc-finite-etale-category. They supply the actual semilinear scheme automorphism, the pullback functor and the projection formula for the fibre bijections. Pullback iteration and composition are verified on projections, so I have not assumed g to be a k-morphism. X and X_0 are connected by the given geometric connectedness, as needed for functoriality.

For step 2 the cited def-galois-fibre-functor really identifies pi_1 with Aut(F). I checked the typing, both inverse identities and both associative products explicitly; the triple product is g^(m+l)(p) composed with g^l(q) composed with r. This is elementary groupoid algebra, not a new group-construction lemma.

For step 3 the same fibre-functor definition and the functoriality statement give precisely the natural projection-of-lifts comparisons. Restriction of a natural isomorphism therefore defines a genuine natural automorphism on every arithmetic cover, not only on isomorphisms of covers. The n=0 map is the canonical one in that statement.

For step 4 I opened lem-sfb-finite-field-galois-frobenius (normality, separability, Frobenius), lem-sc-finite-etale-algebra-criterion (finite separable field algebras are etale), the finite-etale base-change definition, and def-wf-weil-group (degree is the geometric Frobenius exponent). Normality ensures that even for an arbitrary source field Omega every embedding of E factors through iota(E). Every fibre element is then the value of an actual section. Naturality with respect to that section forces the same label at the new base point, so the action is iota gamma^n sigma. This checks the sign without treating b as a k-valued point or assuming a decomposition of an arbitrary geometric cover.

For step 5 I read functoriality and the exact-sequence statement, including injectivity of the geometric inclusion and its image being the degree kernel. The equation for r composed with g^m(p) is naturality for the canonical isomorphism of descended covers, followed by projection to P_0; composing with q gives the correct multiplication order. No faithfulness theorem for restriction is silently assumed.

For step 6 I read the full finite-etale transport statement. Its lambda has source F_b((g^n)^*P), target F_b(P), and naturality for all cover morphisms, so its inverse is exactly the needed path. Its scheme hypotheses agree with the item, and integer n may be negative. Exactness supplies s of any degree. I do not extract any unasserted canonical normalization from the proof of that node.

For step 7 I checked both uses of exactness: A(p_0)^(-1)w is in the degree-zero kernel and hence equals i(h), whereas equality A(p)=A(p') implies i(p^(-1)p')=1 and then p=p'. This is the written torsor argument, not a new node restating the isomorphism clause. Equality of natural automorphisms is componentwise by the cited definition.

For step 8 the finite-field theorem applies to kappa(x)/k_0 of degree e as specified in the item; it makes gamma^e fix that field. Comparing the two fibre-product coordinates proves the point equality. Precomposition by gamma^e and its inverse gives the actual path and commutes with every cover map. No comparison with a sheaf operator is involved.

For step 9 I checked the cited functoriality and fibre-functor statements against the definition of the decomposition map by a path. Restriction to the residue-field cover and conjugation by tau_0 sends a field automorphism to the displayed reparametrization action. The finite-field theorem identifies geometric Frobenius with gamma^e. Naturality of tau gives the written equation between r and g^e(tau); substitution produces exactly tau_0 Frob tau_0^(-1), rather than its inverse. Degree is then e by the already proved degree-preserving isomorphism.

I checked the small cases n=0 and negative n, identity paths, empty finite covers, trivial constant covers, e=1, and X_0=Spec(k_0) (geometric pi_1 is trivial and the group reduces to Z). Changing tau by a geometric loop changes the arithmetic element by the same conjugation; there is no unnoticed coefficient action. All nine steps have fewer than 2000 characters, and the only non-elementary inputs are the listed existing node statements. I checked that their dependency closures do not contain the item. Every quoted citation was checked as a literal substring of its node's current statement. The off-unit finite-cover transport and finite-etale algebra criterion are declared as generic tools; they do not replace any step of the unit's route.
