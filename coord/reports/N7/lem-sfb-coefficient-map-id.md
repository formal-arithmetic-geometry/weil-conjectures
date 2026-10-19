# lem-sfb-coefficient-map-id

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-coefficient-map-id.json: existing statement, now a Mathlib leaf at CategoryTheory.Functor.map_id, Mathlib/CategoryTheory/Functor/Basic.lean:47.
- citations.json: empty list, since a Mathlib leaf carries no proof steps.
- No new nodes or unit files. The item itself is the one Mathlib leaf.

## Attachments

None. Searches of WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the blueprint id, coefficientMap_id, coefficientMap and the coefficient-change notion found no matching declaration. The upstream-master declaration AlgebraicGeometry.ProEtale.coefficientMap_id, WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean:100, is reference material only, not an attachment. Its proof is the same Functor.map_id specialization.

## WANTED

None.

## Corrections and observations

The imported proof had elementary:null and did not cite the coefficient-map definition. Rather than introducing a node for a functor axiom, the existing item is a Mathlib leaf; proof and proof_deps are empty. The original blueprint proof origin is retained, as required by delivery preflight even for a Mathlib leaf. Its statement is unchanged. Added sk-def-sfb-pullback-from-point to stmt_deps because it supplies the functor on all condensed abelian groups. The coefficient-map definition is written for ring morphisms, but its formula a_X=p_X^*a is meaningful for all morphisms of condensed abelian groups, exactly as the item's source and upstream master's omitted ring instances intend. Ring structure is not used or assumed by this law.

The new-snapshot item has no chapter/unit metadata, and dag/chapters/sec-six-functors-basics.json and dag/units/sk-def-sfb-coefficient-change.json do not exist. I read the corresponding current blueprint _section.md files directly and did not invent or change maintainer metadata. The chapter sets up condensed coefficients by inverse image; the unit explicitly gives the identity law. No route change is needed.

Blueprint/DAG searches included coefficientMap, coefficient map identity, coefficient change of the identity, preserves identities, identity morphisms, and coefficient. The broad coefficient search was filtered against the identity-law concept: sk-def-sfb-coefficient-change contains this law only as one clause of its larger ring/derived construction, and is not an exact duplicate of the abelian-group identity statement. No other blueprint node states the same full assertion; same_as is [].

## Unfinished work

None for this item. Its coefficient definitions remain existing DAG dependencies for subsequent work; they are not claimed attached or closed here.

## Review by N7

I read the current main-20261015 item statement and its entire one-paragraph proof, the chapter introduction and the coefficient-change unit. I also opened the statements of def-sfb-coefficient-map, sk-def-sfb-pullback-from-point and sk-def-sfb-pulled-back-coefficients, as well as the definition source in sec-proetale-coefficients. The first supplies a_X=p_X^*a for ring morphisms; part 4 of the second supplies p_X^* as a functor from all condensed abelian groups to abelian sheaves on X. The third explains the additional ring structure, which this statement does not need. Thus the item's broader abelian-group quantifier is retained, and the inverse-image definition is explicitly a statement dependency.

For the original sole proof step, expand the coefficient-map notation and apply F.map_id with F=p_X^* and object Λ. The target object is exactly p_X^*Λ, so the resulting identity is id_{Λ_X}; no comparison isomorphism, exactness, monoidal theorem, or base change is being smuggled into the argument. I read Mathlib/CategoryTheory/Functor/Basic.lean:30–58, including the field map_id at line 47, and Stacks categories.tex, Definition definition-functor, Tag 001B (lines 162–177), which states precisely F(id_x)=id_{F(x)}. This confirms the Mathlib generalization and its source, with no extra hypotheses. The leaf has no remaining proof steps, hence there are no step citations requiring quotations; citations.json is [].

The requested search command actually ran all four kinds; searches.jsonl records the exact queries. LeanSearch and Loogle returned Functor.map_id with the general signature, grep located its actual declaration line, and the LeanFinder hits about underlying condensed identities and identity scheme pullback were read and rejected as different laws. No unavailable service or invented search is recorded. Since an exact generalization was found, a second negative-search phrasing was unnecessary.

I checked delivery-errors B–E against this leaf: it introduces no unsplit claims, new definitions, duplicate nodes, clause-restatement children, proof gaps or cycles through new dependencies. The only added dependency is an existing definition already used by def-sfb-coefficient-map. The equality holds also for the zero condensed group, the zero ring, the empty scheme, and noncommutative condensed rings: the functor identity axiom has no nonzero, commutative, nonempty or finiteness condition. The item is true as written; no statement dispute or hypothesis correction is needed. No SGA source is used. The dry run is the last action; delivery is left to the second reader.

## Dry-run repair

The first captured dry run required proof_origin even for a Mathlib leaf; restored the original agent-blueprint origin with a precise place. It also reported malformed JSON in unrelated def-cbc-enhanced-diagrams-cones (Extra data at line 187). That file is outside this delivery and was not changed. Retrying through the required delivery tool against the refreshed baseline.


## Second reading by N7

- Item statement: compared every quantifier and the equality with main-20261015 `lem-sfb-coefficient-map-id.md` and its `.proof.md`, then read `def-sfb-coefficient-map`, `sk-def-sfb-pullback-from-point` part 4 and the coefficient-change unit; the abelian-group generality and arbitrary scheme agree with the source. The notation-domain issue below is repaired explicitly.
- Original step 1 / current Mathlib leaf: checked the exact field `CategoryTheory.Functor.map_id`, Mathlib/CategoryTheory/Functor/Basic.lean:40–49 (field at 47), against Stacks `categories.tex`, Tag 001B, `definition-functor`, lines 162–177. Substitute F=p_X^* and its object Λ: F(id_Λ)=id_{F(Λ)} becomes precisely the asserted equality after the two displayed definitions. Only the functor property is used; no monoidal or ring-morphism property, comparison isomorphism or hidden transport occurs. Verdict: exact one-line specialization, no proof steps or proof dependencies required.
- New nodes: none. B1–B7 and the deletion/duplicate audit introduce no obligations; there are no clause-restatement children or elementary helper nodes. The sole delivered node is the existing item, now one Mathlib leaf; its file, declaration and line are verified.
- Independent searches: ran the logged Loogle query `Functor.map, CategoryTheory.CategoryStruct.id` (OK, zero hits), grep `map_id.*:|map_id \(` under CategoryTheory/Functor (9 hits, including the field at line 47), and LeanFinder `Every functor preserves identity arrows as part of its defining axioms` (8 hits, first the exact general law with its full signature). These are different phrasings from the first reader’s searches and are recorded as returned in searches.jsonl and the node.
- Source implementation: read upstream-master ChangeOfCoefficients.lean:88–107, where `coefficientMap` is the inverse-image map and the identity lemma explicitly omits the ring instances; this confirms the generality but is not a finished-proof attachment. An independent source search found no `coefficientMap_id` declaration on slopmaster2. No Lean file was written and no compiler or build was run.
- Edge cases: for Λ=0 the same functor axiom gives the equality (including the coincident zero/identity endomorphism); for a field’s underlying condensed group and for X empty or arbitrary the exact same substitution applies, with no nonzero, nonempty or characteristic assumption. No integer parameter occurs. Verdict: no exceptional case or missing hypothesis.
- Citations: citations.json remains [] because the final leaf has no proof steps; all notation dependencies are existing definitions. No SGA source is used.

STATEMENT-DISPUTED (notation domain only): `def-sfb-coefficient-map` introduces a_X only when a is a morphism of condensed rings, whereas the imported item quantifies over all condensed abelian groups. For example the constant condensed abelian group Z/2Z ⊕ Z/4Z is an allowed object without any ring-object structure supplied; the cited definition alone therefore cannot be instantiated. The mathematical equality is true, and the source proof and archived implementation show the intended interpretation. Added the explicit definitions Λ_X=p_X^*Λ and (id_Λ)_X=p_X^*(id_Λ) to the item, citing the existing functor on all condensed abelian groups. This is a notation clarification faithful to the source, not an added hypothesis or a weakened conclusion. The first worker’s earlier statement-unchanged assessment above is superseded by this correction.

Changes and reasons: made the notation well-defined at the stated generality, recorded three independent searches and their actual results, and appended this second reading. Retained the correct Mathlib leaf, dependencies and empty citations. The required command with a trailing dot prints usage because this installed deliver.py accepts exactly group/item positional arguments; the supported equivalent omits the dot. Dry-run and delivery results follow.

Additional independent DAG check: tools/blueprint_refs.py search coefficient-map searched all imported chapters (17 hits); the identity item is the exact assertion, the composition/square nodes concern different laws, and sk-def-sfb-coefficient-change bundles the ring/derived construction and cites this identity item in its proof. It cannot be used to prove its own identity child without circularity. A whole-DAG search for 001B, preserves identities and coefficientMap_id gives no alternative exact coefficient-identity node. The new direct inverse-image dependency was already reachable through def-sfb-coefficient-map, so it adds no reach and cannot introduce a cycle. Read the chapter introduction and unit proof directly, since their DAG metadata records are absent.

Second-reader dry run: the supported command `python3 /home/ubuntu/weil-launcher-nt/deliver.py N7 lem-sfb-coefficient-map-id --no-push` printed `OK (not pushed) deliver/N7/lem-sfb-coefficient-map-id at 7118dbd1e3: preflight passed`. No preflight repair was required after this second reading. Delivery uses the same supported invocation without `--no-push`.
