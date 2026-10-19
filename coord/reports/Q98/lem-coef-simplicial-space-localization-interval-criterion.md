# Stage-1 worker report

## Worker report

The item `lem-coef-simplicial-space-localization-interval-criterion` has its statement unchanged and a new nine-step proof, status split. One new node, `lem-coef-simplicial-local-bounded-lifting`, is unsplit with a statement only. There are no Mathlib leaves or Lean attachments. citations.json gives full verbatim statements for every step citation. Research files and repair.py stay in the sandbox; the delivery comprises the two nodes and this report.

I read the chapter, unit, three route levels of SETUP.md, GOAL.md and coord/dag-sync.md. The current ancestor source is literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md, paragraph 2. Its derived coefficient adjunction does not literally state this localization theorem: this item is auxiliary infrastructure reached through the recorded ancestry. No chapter, unit or binding was changed; this is not the unit's key statement, so no realization record is edited.

I searched slopmaster2 and the master reference checkout by the item id, blueprint tag, Reedy, Bousfield, simplicial-space and interval terminology. No slopmaster2 project declaration states this item. Master's sorry declarations are not completion evidence. No Lean was written or compiled. The generic localization candidates have a dependency path through the model/derived-mapping convention node, hammock localization, coherent nerve, Segal comparison, completion and cartesian exponent back to this item. Citing them would create a cycle. Their dependencies were left untouched.

WANTED: Rezk, A model for the homotopy theory of homotopy theory, Sections 2.3-2.5 and Propositions 9.1-9.2, printed pp. 6-7 and 21-22, for this item and the new bounded-lifting node. The Rochester PDF in the existing source is not archived under literature/. I read the online source, including the final cardinality paragraph of 9.1 and the entire proof of 9.2, without downloading it. proof_origin.by is agent, as required for missing literature, and points to the archived ancestor with the auxiliary reference and supplied arguments described. No Stacks tag states this simplicial-space cardinality theorem; no SGA source is used.

The earlier attempt invoked Rezk 9.1 with no supporting node, used a representable homotopy-colimit resolution and homotopy-limit closure under only an internal-hom citation, and asserted the localized simplicial axiom without the required lifting calculation. Its report also mentioned citations absent from its proof. I replaced it. The one new obligation is the Bousfield-Smith bound used in 9.1; all model axioms, fibrant-object and simplicial assertions and the interval argument are proved in the item's steps.

## New nodes

- lem-coef-simplicial-local-bounded-lifting: for fixed f, a set of bounded local acyclic monomorphisms detects the right lifting class against all local acyclic monomorphisms. Source: Rezk Proposition 9.1 proof, final paragraph. Status unsplit; proof and proof_deps empty and proof_origin null. It introduces the universe, all objects, local tests, total cardinal bound and arrow-isomorphism convention. It states no model-structure or cartesian-interval conclusion.

## Not duplicates

lem-coef-simplicial-local-bounded-lifting vs lem-coef-simplicial-space-localization-interval-criterion: the new statement supplies a cardinal bound for a lifting class. The item constructs the two weak factorization systems and proves the simplicial and interval assertions from that input; the new node does not restate a clause.

lem-coef-simplicial-local-bounded-lifting vs lem-coef-small-object-cell-factorization: the existing theorem assumes a small family and domain-smallness and gives a factorization. The new node finds a family detecting a proper class of local lifting problems and gives no factorization.

lem-coef-simplicial-local-bounded-lifting vs lem-coef-accessible-intersection-generators and lem-coef-smith-small-saturated-intersection: those abstract generator results assume accessibility of the weak-equivalence class. They do not prove the bounded local lifting assertion; specializing them would require substantial additional hypotheses to be proved.

lem-coef-simplicial-local-bounded-lifting vs lem-coef-simplicial-bousfield-model-structure and lem-cbc-general-bousfield-localization: these model-construction statements do not give the bounded representative-family lifting equality, and their derived-mapping convention dependencies cause the cycle described above.

Whole-DAG and blueprint searches covered localization models, local acyclic maps, Bousfield-Smith, cardinality argument, bounded lifting and simplicial spaces. The blueprint searches for the new fact found no match. Its from.node is the ancestor printed by blueprint_refs.py, via prepends this item to the inherited chain, and from.place specifies the bounded-generator input in Rezk 9.1. Both same_as lists are empty. No new Stacks tag collides with an existing node.

## Mathlib searches

I reran the item searches using msearch.py and replaced the inherited result summaries with the actual outputs of this pass. For the new node I ran LeanFinder with two descriptions of bounded lifting, LeanSearch for the Bousfield-Smith cardinality argument, Loogle for Bousfield/lifting, and grep. All services answered. The node records the verbatim outputs and exact queries; searches.jsonl is the command-generated evidence. A further logged grep located declarations for closer reading.

The hits include GrothendieckAbelian.generatingMonomorphisms_rlp, SSet model instances and generic small-object results. I read Bousfield.lean:13-26,48-58: it tests ordinary Hom-set bijections rather than weak equivalences of mapping spaces. SmallObject/IsCardinalForSmallObjectArgument.lean:70-86,480-515 assumes the given small family and its smallness; it does not produce the needed family. The abelian generating-monomorphism result assumes a Grothendieck abelian category and separator, not local equivalences of bisimplicial sets. None states the item or new node, or a one-line generalization of them. No unavailable search is recorded as absence.

## Review by Q98

I matched the unchanged item with Rezk 9.1(1)-(4), its simplicial-model assertion, 9.2 and the cartesian convention in 2.5. Its arbitrary small inclusion f, raw mapping tests into Reedy fibrant objects, monomorphism cofibrations and additional interval hypothesis are correct. There is no statement dispute. For the new node I checked the last paragraph of 9.1: bounded local acyclic inclusions detect the full lifting class. Replacing degreewise size by total bidegree size is harmless after increasing the uncountable bound. The bound depends on f and is not assumed finite, countable or uniform.

Step 1 uses the precise monomorphism and mapping-fibration clauses of lem-coef-simplicial-space-reedy-cartesian, the factorization and weak-equivalence axioms of lem-coef-reedy-model-structure, and the Kan model axioms of lem-coef-kan-quillen-right-proper. All objects are cofibrant. Factoring an old weak equivalence and taking a section of its trivial-fibration part proves directly that it passes the local test; no cyclic derived-mapping result is used. The section is a monomorphism and old weak equivalence, as required by the cited mapping axiom.

Step 2 uses that same mapping law, the Kan boundary-lifting criterion including dimension zero, and lem-coef-lifting-class-closure's arrow-retract convention and closure. It explicitly constructs fillers for pullbacks, products and transfinite inverse towers of trivial Kan fibrations. Thus the saturation needed for J-cell maps is proved rather than asserted from an uncited homotopy-limit theorem.

Step 3 uses exactly the new bounded-lifting equality and the small-object theorem's stated factorization. I verified its domain-smallness hypothesis: fewer than gamma total simplices, countably many operators, and a regular uncountable kappa greater than gamma put all representatives and equations at one stage. The J-cell factor is in T by Step 2. The retract argument supplies the left-class equality as well as factorization; it is a full weak factorization system.

Step 4 uses only the Reedy model axioms and earlier proved steps. If p is both a new fibration and local equivalence, its old factorization p=qi has i in T by two-out-of-three. A lift makes p a retract of the old trivial fibration q. This identifies new trivial fibrations with old trivial fibrations and provides the other weak factorization system.

Step 5 uses the old cartesian pushout-product and mapping laws, Reedy objectwise weak equivalences, and the Kan horn/boundary lifting tests. Horn tensor products are old trivial cofibrations and hence in T. If i is locally trivial, the boundary corner transposes to lifting a monomorphism against Map(i,Z), a trivial Kan fibration. If p is locally trivial, Step 4 reduces to the old mapping axiom. These are separate checks of both triviality cases, independent of the interval hypothesis.

Step 6 uses the mapping law and degree-zero boundary lifting. Every old fibrant local Z lifts T; every new fibrant Z is old fibrant and lifts f, which belongs to T by its definition. The simplicial axiom proved in Step 5 makes Map(f,Z) trivial, proving the reverse implication without assuming the fibrant-object identification during construction.

Step 7 uses the internal-hom formula and the model/Kan retract axioms. The written maps e(k) with its first k coordinates equal to one and r the coordinate sum are monotone, with r(e(k))=k. Their nerves give the claimed simplicial retract, not just a retract of vertices. I checked n=0,1,2 and r on every binary tuple. Induction applies the interval hypothesis only to objects already known local.

Step 8 uses the old cartesian pushout product to establish that W^Q to W^P is a Reedy fibration. Its degree-n map is exactly the test against W raised to F(n), local by Step 7, so the objectwise weak-equivalence clause makes it a Reedy trivial fibration. Mapping cofibrant X into it and currying proves W^X local. This is the direct replacement for the previous uncited density and homotopy-limit assertions.

Step 9 uses the old cartesian clause to make the pushout product a monomorphism, and the mapping law to make the two i-induced maps trivial fibrations because their exponent targets are local. It explicitly names the four mapping objects. Pulling back the lower trivial fibration gives a trivial fibration by boundary lifting, and two-out-of-three proves the map into that ordinary pullback is weak. No unjustified strict/homotopy-pullback identification remains. Symmetry gives the other factor case.

I tested the new statement with f an identity (all old fibrant objects are local, consistent with ordinary acyclic-cofibration generators) and with f empty to terminal (locality tests contractibility, with no restriction to terminal lifting targets). It allows empty endpoints and arbitrary small sizes; gamma can grow with f. Empty products, dimension-zero boundaries, empty tensor parameters and identity pushout-product factors are covered by the written constructions. No nonempty or finite-dimensional hypothesis was added. Each uses-list has been checked against the full statement quoted in citations.json; no step needs a fact found only inside another node's proof.

The new node has complete hypotheses and notion dependencies, an actual non-elementary cardinality assertion, no proof sketch and genuine searches. It is not a duplicate or relabelled item clause. No maintainer fields, live files, launchers or Lean sources were edited. The server dry run is the final check before this sandbox is handed to the second reader.

## Second reading by Q98

- Item statement: checked against Rezk, *A model for the homotopy theory of homotopy theory*, Proposition 9.1(1)--(4), Proposition 9.2, and Section 2.5(1), pp. 21--22 and 6; every clause actually present in the imported target (the inclusion hypothesis, mapping-test directions, fibrant/local identification, simplicial corner condition, lifting characterization, Reedy implication, interval hypothesis, and pushout-product conclusion) has the source's stated hypotheses and direction.
- New node `lem-coef-simplicial-local-bounded-lifting`: checked against the final paragraph of Proposition 9.1, p. 22; the class is monomorphisms detected by all local mapping spaces, the representatives are by arrow isomorphism, and the cardinal bound is an uncountable universe-small bound (the total bidegree bound follows after regular enlargement). Verdict: genuine non-elementary auxiliary fact, self-contained and not a restatement.
- Step 1: checked each use against the Reedy cartesian mapping axiom, Reedy model factorizations, and Kan trivial-fibration lifting including degree zero. The section of the old trivial fibration is a split monomorphism, so the mapping argument applies. Verdict: sound.
- Step 2: checked pushouts, coproducts, ordinal composites, and arrow retracts against enriched pullback/product formulas and Kan boundary lifting. The inverse-limit filler construction is explicit and includes limit stages. Verdict: sound.
- Step 3: checked the bounded-generator equality and the stated small-object factorization. Regular uncountable `kappa` handles the total-simplices and operator-equation bounds; the retract argument gives both lifting classes. Verdict: sound.
- Step 4: checked the old factorization, two-out-of-three, and arrow-retract square against the Reedy model axioms. Verdict: sound.
- Step 5: checked both triviality cases of the mapping corner using the old cartesian pushout product, tensor-Hom transposition, and Kan boundary lifting; no interval hypothesis is used prematurely. Verdict: sound.
- Step 6: checked both directions of the fibrant-object identification, including degree-zero lifting and the fact that the given `f` is in the local class. Verdict: sound.
- Step 7: checked the ordered maps `[n] -> [1]^n -> [n]`, their nerve maps, the contravariant exponent retract, and the cases `n=0,1,2`. Verdict: sound.
- Step 8: checked the restriction internal-hom formula degree by degree and the old trivial-fibration mapping axiom; arbitrary exponents are local by currying. Verdict: sound.
- Step 9: checked the four mapping objects, the ordinary pullback of the two trivial Kan fibrations, and two-out-of-three; symmetry covers the other factor. Verdict: sound.
- Citations: compared every verbatim quote in `citations.json` with the cited node file and checked that every non-elementary fact in the nine steps has a node citation; no citation was stale or unsupported.
- Searches and form: rechecked the recorded Mathlib searches, blueprint ancestry, source URL/place, statement-only form of the new node, and absence of SGA sources. No duplicate node or Mathlib declaration supplies either result.

No mathematical, statement, node, or citation repair was necessary after this reading; the only change in this pass is this audit section, which records the source and edge-case checks before the final delivery.
