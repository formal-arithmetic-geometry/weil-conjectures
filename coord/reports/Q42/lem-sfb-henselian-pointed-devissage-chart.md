# Q42 stage-1 delivery: lem-sfb-henselian-pointed-devissage-chart

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-henselian-pointed-devissage-chart.json — item, six-step split, original statement retained, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-pointed-affine-devissage-etale-existence.json — one new statement-only node, unsplit; general scheme-theoretic pointed complete dévissage existence, no Mathlib match.
- citations.json — one exact statement quotation for every step/node pair (34 pairs).
- report.md — this report. searches.jsonl is the search command's unmodified log; write_split.py is sandbox-only preparation code.

## Attachments

None. Searches in lean/WeilConjectures for the item id, complete algebra devissage, pointed devissage and the broader devissage spelling variants found no declaration stating this theorem. Existing derived-category and constructible-sheaf dévissage declarations concern different objects. No Lean was written or compiled.

## WANTED

None. All proof sources used here are present in literature/stacks-project/.

## Corrections and scope

The item had no proof. Its statement is true as written and is retained. The unpointed existence node lem-trf-complete-algebra-devissage-etale-existence explicitly forgets the intermediate marked primes. Neither its proof nor the source's stronger statement may be used as if those primes were its conclusion. I therefore added the general scheme-existence input, used the existing pointed base-change theorem, and read the primes from the retained chain. This is not an algebraic restatement of the item's conclusion: the new input has arbitrary scheme base, no henselian assumption, changes both source and base, and concludes with a scheme chain. The item still constructs the finite module model, eliminates the base change by henselian retraction, constructs the flat local enlargement, translates the chain and verifies the fibre-ring conclusion.

I read the current blueprint under literature/blueprint/latest/, including sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This item is a generic algebraic flattening prerequisite beneath the compactification/direct-image step (3), not a replacement six-functor route. The inherited blueprint.from.node is null, as tools/blueprint_refs.py ancestor reports; its via list is retained and the new node prepends this item. No chapter/unit record was changed. The unit's stale realization is outside this item's ownership.

Two source typos are avoided: the chain in Tag 05HR with one surjective alpha has length one, although its prose says length zero; and Tag 05HZ's connecting contraction is along the existing ring map T_i to S_(i+1), as the item's statement correctly says, not a nonexistent map in the opposite direction. Neither typo changes this item's statement.

## Mathlib and duplicate searches

The command msearch.py ran LeanFinder twice with different phrasings, Loogle, LeanSearch and grep for the item/new existence input. The original item's prior search records were preserved. Every appended query and result is taken directly from searches.jsonl. LeanFinder returned local generators, quasi-coherent data and spreading-out maps; LeanSearch returned etale base change, finite presentation under base change and rank comparison. These do not supply the complete pointed finite chain. The Loogle combined smooth/finite-module query and AlgebraicGeometry grep for the devissage spellings returned no hits. No service failure was represented as absence. No new Mathlib leaf is claimed.

I searched all dag/nodes by Tags 05HR, 05HI, 05HM and 05I1 and by pointed/complete devissage, and ran blueprint_refs.py search for devissage, pointed, 05HR, 05I1 and complete d. The blueprint has no matching general pointed algebra/scheme existence statement. I opened all six same-tag candidates listed below. Related nodes for flat finite-type modules add flatness hypotheses and have a finite-presentation/projectivity conclusion, so are not this existence input. The new id was absent from the DAG and project Lean source.

## Not duplicates

lem-sfb-pointed-affine-devissage-etale-existence vs lem-trf-complete-algebra-devissage-etale-existence: the existing statement concludes only an unpointed algebra devissage and explicitly forgets pointing; the new theorem produces a scheme chain retaining every marked intermediate point, necessary to recover the singleton prime fibres.
lem-sfb-pointed-affine-devissage-etale-existence vs lem-trf-devissage-pointed-etale-refinement: refinement requires a supplied one-step datum and an etale refinement of its smooth target; the new theorem constructs a whole chain from an arbitrary finite-type quasi-coherent module.
lem-sfb-pointed-affine-devissage-etale-existence vs lem-trf-devissage-generic-basis-drop: the existing theorem constructs one generic basis map on an already supplied smooth target and bounds its cokernel support; it does not construct the source/base neighborhoods or the complete chain.
lem-sfb-pointed-affine-devissage-etale-existence vs lem-trf-devissage-pointed-restriction: restriction assumes an existing pointed datum/chain and preserves it under base change or shrinking; the new theorem asserts initial existence.
lem-sfb-pointed-affine-devissage-etale-existence vs def-trf-pointed-scheme-devissage-data: this is a definition of chains and their operations, with no existence assertion; the new theorem states existence for arbitrary input modules.
lem-sfb-pointed-affine-devissage-etale-existence vs lem-trf-pointed-devissage-affine-translation: translation requires a chain already supplied and extracts algebra data, forgetting the point conditions in its conclusion; the new theorem constructs that chain after elementary etale changes.

## Review by Q42

I checked this split against delivery-errors B–E with the node statements and Stacks source open. For the item I read flat.tex Tag 05PG's first proof paragraph, the complete algebra definition 05HX, pointed algebra definition 05HZ, existence lemma 05I1, scheme existence proof 05HR, and complete pointed scheme definition 05HI. For the one new node I read 05HR's statement and full induction/refinement/shrinking proof and 05HM's role there; the statement deliberately uses the existing auxiliary pointed-chain definition, dropping support-dimension equalities only. The source proof constructs affine neighborhoods and retains exactly these points and maps. Its input needs a finite-type quasi-coherent module, which the new statement explicitly supplies even though the displayed proposition in the source omits reintroducing that module. No proof is concealed inside the new statement and its proof/proof_deps fields are empty.

Step 1 is an elementary fraction construction, not a new spreading-out lemma. I checked the localization definition against the actual universal-property argument B = (C_0)_(q_0), using that B is local. Taking the C_0-span of finitely many B-generators inside P gives a finite module without assuming finite presentation. Fractions give the displayed bijection onto P, so there is no unlicensed descent of infinitely many relations. Locality of A to B supplies contraction to the maximal ideal of A.

Step 2 uses exactly the affine finite-type criterion, tilde/quasi-coherence theorem, tilde/global-sections unit isomorphism and affine finite-type module criterion from the cited statements. They supply every hypothesis of the new scheme-existence theorem, which returns the elementary etale marked neighborhoods and a chain, rather than borrowing these data from the proof of the unpointed algebra node.

Step 3 uses the henselian-local root-lifting equivalence because the terminology definition uses idempotents, while the retraction theorem uses simple roots. I read algebra.tex Tag 04GG (including the retraction clause and proof) to check this change of formulation. The retraction contracts m to m-prime, and the marked residue map is an isomorphism, exactly the hypothesis of clause (1) of lem-trf-devissage-pointed-restriction. That clause really preserves the points, singleton fibres, generic bases and cokernels. The affine fibre-product and tilde-pullback theorems identify the new objects, not just their stalks. Cancellation shows that the section of the etale base map is itself etale; base change then composition makes C_0 to C etale. The cited affine finite-presentation theorem, applied to affine schemes, supplies finite presentation, whence finite type by concatenating finite generator lists. Finite generation of N follows from its displayed tensors.

Step 4 uses etale's flatness clause, the local-ring definition of flat morphism and the affine stalk/localization statement. Consequently the map at the marked prime is both flat and local, precisely the hypotheses of the cited flat-local faithful-flatness theorem. This proves faithful flatness of B to D, rather than mistakenly requiring A to B flat. The tensor/localization comparison is written on pure tensors with an inverse; the necessary denominators map to units because q contracts to q_0.

Step 5 uses the affine translation node for all the algebra chain conditions that its statement actually gives. It separately uses the pointed-chain definition for the retained points: the singleton fibre says exactly uniqueness of the prime of S_i above q_i. The first closed immersion and each next closed immersion give the two contraction clauses. These facts are read directly from the data, not obtained by citing the unpointed translation for a stronger conclusion. The length-zero case has zero initial module and no primes to supply.

Step 6 uses the cited smooth-flat theorem and affine flatness equivalence to pass from scheme flatness to ring flatness. Local finite presentation is in the smooth definition, and the affine criterion gives actual finite presentation of T_i over A. I checked morphisms.tex Tags 01VE and 01VF and varieties.tex Tag 056T (smooth over a field is geometrically reduced). The existing geometrically-reduced-fibres statement provides precisely that fibre conclusion. Geometric irreducibility and reducedness then give integral affine schemes over every field extension, by the cited definitions; irreducible explicitly includes nonempty, which is needed for a nonzero domain, not merely absence of zero divisors. The affine fibre-product statement identifies their coordinate rings with T_i tensor_A K.

I tested P = 0, an empty chain, a field base, zero rank maps and non-finitely-presented finite modules. Step 1 also handles P=0 by choosing the empty generating family; the existence theorem may return a zero chain after shrinking when only the marked stalk is zero. The proof assumes no Noetherian condition, no flatness of P or B over A, and no finite presentation of P. Every non-elementary assertion is either the stated conclusion of a cited node or an explicitly written construction; no step exceeds 2000 characters (the maximum is 1051). Statement dependencies are retained because each notion still occurs in the unchanged item. Proof dependencies are exactly the union of the step uses. The 34 entries of citations.json quote the full cited statements verbatim. Cross-unit citations are declared as generic tool uses in split_report, without setting the maintainer's top-level tool_uses field.

## Unfinished work

The single new existence theorem is intentionally statement-only for the next DAG stage-1 item. No other mathematical gap is deferred in this item's assembly proof. Server dry run and delivery are run after this report is written.
