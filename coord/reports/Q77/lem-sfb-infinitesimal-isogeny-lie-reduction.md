## Worker report

Q77 split lem-sfb-infinitesimal-isogeny-lie-reduction in stage 1. All writes are in this item's sandbox. No Lean was written, no compiler or build was run, and no git command was run in the shared read repository.

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-infinitesimal-isogeny-lie-reduction.json: item; seven-step split, statement unchanged.
- lem-sfb-central-semisimple-restricted-subalgebra.json: statement; unsplit, no Mathlib match.
- lem-sfb-height-one-restricted-quotient.json: statement; unsplit, no Mathlib match.
- lem-sfb-semisimple-kernel-chain-termination.json: statement; unsplit, no Mathlib match.
- lem-sfb-central-infinitesimal-torus-extension.json: statement; unsplit, no Mathlib match.

citations.json records every use in every item step, quoting the actual cited statement verbatim. Searches and their actual service output are retained in searches.jsonl and the search-results text files. The sandbox was initially empty; there was no previous split to reuse. The pre-existing searches in the item's live node have been retained and new searches have been added.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag and for infinitesimal isogenies, noncentral semisimple elements, restricted Lie subalgebras and height-one kernels found no declaration proving the item or a new supporting statement. The isogeny definition in GroupScheme/Defs.lean is a definition, not this theorem. The characteristic-zero Lie results in GeneralLinear/ClosedSubgroup/Product.lean do not state the positive-characteristic quotient construction.

## WANTED

WANTED: T. A. Springer, Linear Algebraic Groups, second edition (1998), 13.3.5, for lem-sfb-semisimple-kernel-chain-termination and the details Milne omits in Proposition 17.80. This book is not present in the supplied literature directory. The delivery does not pretend to have read it. Milne's explicit termination assertion is isolated as a statement-only node; the item's assembly proof is marked agent-written. Corollary 11.38, which is present in Milne, supplies the separate quotient-construction node.

## Source and route

I read Milne, Algebraic Groups (2017), printed pp.377--378, especially Proposition 17.80 and its proof, Corollary 17.77, and Proposition 17.74 and Example 17.75. I also read pp.222--223, Propositions 11.35--11.37 and Corollary 11.38, and pp.236--241, Definition 12.17, Corollary 12.22, Theorem 12.23 and Notation 12.29. These are algebraic-group results of the supplied Milne PDF, not Stacks statements; no numerical Stacks section is substituted for a tag.

The first new node isolates Milne's claim that failure of (a) forces positive characteristic and makes the semisimple vectors an adjoint-invariant restricted subalgebra. Its geometric scalar-extension and trivial-adjoint clauses make explicit what is needed to integrate a central toral subalgebra. The second is the height-one correspondence and quotient of Corollary 11.38, with its toral central specialization from the correspondence. The third isolates exactly the omitted termination assertion for an already specified tower. It neither constructs such a tower nor lifts any torus. In particular, the iteration does not lower group dimension, and no dimension-decrease argument is claimed. The fourth is an agent-synthesized structural extension lemma from Corollary 12.22 and exact character antiduality, rather than a restatement that every torus in the final group lifts.

For the fourth node, the intended smaller argument is concrete: centrality of N makes the commutator of E descend along E x E -> T x T to a map T x T -> N. The scheme T x T is geometrically reduced and N is infinitesimal with residue field k, so that map is its constant identity map. Thus E is commutative. Over an algebraic closure Corollary 12.22 makes E multiplicative type, which is precisely the geometric definition over k. Theorem 12.23 then gives the displayed exact character sequence; finiteness of N makes its character group finite. No reduction or neutral component over an imperfect field is asserted to be smooth. The node remains unsplit, so these are report notes for its future worker, not an additional split smuggled into its statement.

The latest blueprint file read was literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). This supporting branch is the existing alteration/PGL/Milne prerequisite chain recorded by the item's provenance, not a new route for the unit. The ancestor command reports blueprint.from.node = None for this new-target branch; I preserve that live provenance and extend its via list and exact local place in the new nodes. No unit realized fields are changed because this item is not the unit statement.

## Searches

Before creating any node I searched the whole DAG's statements and titles, its source records for Milne 17.80, 11.38 and Springer 13.3.5, and the Lean source. I ran blueprint_refs.py searches for infinitesimal isogeny, semisimple, radicial isogeny, restricted Lie, central isogeny, semisimple kernel, torus lift, multiplicative type, central extension and torus extension. The broad semisimple search returns characteristic-zero representation and Lie statements, not this construction; the specific construction queries return no blueprint match. The existing multiplicative-type statements are distinguished below and reused where their statements suffice.

Each delivered new node has real msearch.py calls of leanfinder (two phrasings), loogle, grep and leansearch, logged with unchanged query texts. The two initial broad torus-lift searches were exploratory and are not used to support an overgeneralized delivered node. The delivered central-infinitesimal-extension node has its own fresh searches for that precise statement. All services used in the recorded delivered searches returned answers. None returned an exact match or a one-line specialization. Cartan subalgebras, abstract Lie quotients, Engel nilpotence, ring infinitesimal lifting, abstract GroupExtension and the additive CharacterModule into Q/Z concern different objects. No Mathlib leaf is claimed.

## Not duplicates

lem-sfb-central-semisimple-restricted-subalgebra vs lem-sfb-infinitesimal-isogeny-lie-reduction: identifies the tangent subspace at one bad stage, with its restricted operation and scalar-extension behavior; it constructs no isogeny or final group.

lem-sfb-height-one-restricted-quotient vs lem-sfb-infinitesimal-isogeny-lie-reduction: takes a specified invariant restricted subalgebra and integrates it to a height-one kernel; does not assert termination, goodness of the target, or torus lifting.

lem-sfb-semisimple-kernel-chain-termination vs lem-sfb-infinitesimal-isogeny-lie-reduction: excludes an infinite tower satisfying stated kernel conditions; does not assert existence of a quotient or any torus-lifting conclusion. The item has to build the tower using the first two nodes and check every condition.

lem-sfb-central-infinitesimal-torus-extension vs lem-sfb-infinitesimal-isogeny-lie-reduction: classifies an already given extension of a torus, including potentially nonreduced source, by a central infinitesimal multiplicative kernel and gives an exact character sequence. It contains no torus-lifting existence conclusion; step 6 constructs that torus from the lattice quotient and proves its image assertion explicitly.

lem-sfb-central-infinitesimal-torus-extension vs lem-sfb-commutative-multiplicative-type-extension: the existing node requires E already commutative over an algebraically closed field and has no exact character conclusion. The new node must establish commutativity from a central infinitesimal kernel and torus quotient over an arbitrary field.

lem-sfb-central-infinitesimal-torus-extension vs lem-sfb-multiplicative-extension-action-rigidity: the existing statement is constancy of an external smooth connected action over an algebraically closed field. It neither makes this possibly nonreduced E commutative nor supplies its character exact sequence.

lem-sfb-central-infinitesimal-torus-extension vs lem-sfb-multiplicative-character-antiduality: antiduality assumes its groups already multiplicative type and records the closed-immersion criterion; it does not show this E is multiplicative type or state the needed short exact sequence for q. The item separately cites antiduality for construction over k.

lem-sfb-central-infinitesimal-torus-extension vs lem-sfb-multiplicative-type-largest-subtorus: that node starts with a multiplicative-type group and asserts existence and field compatibility of its largest torus. It does not classify the extension or give the character exactness from which step 6 proves surjectivity of the image.

No new node cites a Stacks tag shared by another node, so there are no unlisted same-tag pairs.

## Review by Q77

I checked delivery-errors B--E against the open node files and the Milne pages above. Every new node is statement-only with empty proof and proof_deps, its own objects, an explicit meaning for the restricted operation, height, centrality and infinitesimal kernel when used, and definition dependencies extracted from its bracketed citations. Their hypotheses retain the arbitrary ground field. Their status is unsplit, not a claim that the omitted argument has been proved. JSON uses single TeX backslashes after decoding.

Step 1 is the identity construction and directly verifies all morphism and torus clauses, including G=1. Step 2 cites the first node for positive characteristic, restricted closure, actual adjoint invariance and geometric fullness, and the second for the quotient, its height-one central multiplicative kernel, smooth connected finite-type target, and unchanged dimension. I checked those clauses in the cited statements; merely a definition of restricted Lie algebra would not suffice. Step 3 cites the third node, matching both the full geometric semisimple kernel requirement and the central height-one multiplicative requirement supplied in step 2. It never mistakes constant dimension for a descending integer.

Step 4 uses the exact composition clauses of lem-trf-finite-radicial-basechange and lem-weil-pbc-flat-ring-map-comp, whose statements I opened. The latter is a ring theorem and is used on affine coordinates. Surjectivity of a finite composite is elementary. Both citations are existing Mathlib leaves, so they are generic tools without changing the unit route.

Step 5 uses the actual fibre-product definition for the inverse image and the fourth new node for multiplicative type and the exact character sequence. Its kernel is the same N because the identity of S maps to the identity of G_{i+1}; centrality holds after every algebra extension, not just on rational points. Base change preserves finiteness because module generators tensor to module generators; the tensor identity in the step proves preservation of faithful flatness. The source P need not be smooth, and the new extension node explicitly allows that case. Step 6 uses lem-sfb-multiplicative-character-antiduality exactly for its Galois-equivariant quasi-inverse and its surjective-character-map/closed-immersion clause. It does not quote that node for the missing exact sequence: that is the fourth node's separate conclusion. The construction uses the Galois-stable torsion subgroup, so the torus is defined over k. The injection into M/Mtors and injection of monomial coordinate algebras are written out. Step 7 uses only those constructed injections, so composition gives the scheme-theoretic image assertion, not just surjectivity on geometric points. citations.json quotes all eight citations in these steps verbatim from their statement fields.

Small cases checked: rank-zero tori and G=1 use the identity case; h=0 gives the identity height-one quotient; h=Lie(G_m) gives the usual Frobenius kernel mu_p and equal source/target dimensions; h=Lie(G_a) in the general quotient lemma gives alpha_p and is not erroneously declared multiplicative because its geometric vectors are not semisimple. For the extension node, E=mu_p x T is allowed despite being nonreduced, and the torsion quotient removes the mu_p character torsion. For E=G_m -> G_m by t |-> t^p the character sequence is multiplication by p with finite cokernel, and the constructed torus still maps onto the target. A test of the bad tower is G_a semidirect G_m with weight p^a: after quotienting mu_p the weight exponent drops until the noncentral semisimple case appears; the group dimension never drops. Adding an independent central torus does not justify a dimension argument and is why termination is its own supporting node. Characteristic zero does not enter the tower since the first supporting result excludes the bad case there.

Corrections during this review: I replaced an exploratory overbroad torus-lifting approach with the precise central-infinitesimal multiplicative-extension argument needed by this quotient construction. I have not established a counterexample to arbitrary radicial-isogeny torus lifting, and do not claim one. The imported item statement was not changed and no STATEMENT-DISPUTED issue was found. I also avoided citing the largest-subtorus node for a finite-quotient clause that its statement does not contain, and instead wrote the lattice/image argument explicitly. All seven proof steps are below 2000 characters; none hides the termination assertion or the extension-classification lemma.

## Unfinished work

The four new statements intentionally remain unsplit for the next stage-1 workers. In particular Springer supplies details absent from Milne for the termination lemma. This is a one-level split, not a claim that its whole transitive dependency closure is finished. No other item work remains except the required remote checks and delivery.
