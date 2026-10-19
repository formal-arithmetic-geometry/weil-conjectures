# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-normal-geometric-specialization-conjugacy.json`: statement item, split into six steps; not a Mathlib match. No new nodes or Mathlib leaves.
- `citations.json`: a verbatim statement quote for every step/node citation. The whole statement is retained where a step uses several clauses.
- `searches.jsonl`: searches actually executed through msearch.py. The inherited searches in the item were retained.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` for the item tag and geometric-specialization/conjugacy terminology. No project declaration states this item. References to normal schemes or specialization alone do not cover its conjugacy clauses.

## WANTED

None. The ILO volume and all supporting Stacks source files are present locally.

## Findings and corrections

The imported statement is retained verbatim. No hypothesis was added, no conclusion weakened, and no source or unit route was replaced. The item was statement-only, without a proof. Its parent needs the geometric isomorphisms used in ILO XVII Lemma 3.5.8 and Proposition 3.6.1. These passages assert the conjugacy without the field argument; this delivery supplies that argument and marks proof_origin as agent.

The actual strict localization of a generic point is the spectrum of the separable algebraic closure inside the chosen algebraic closure, not in general the entire algebraic closure. The proof therefore distinguishes these fields throughout. No perfection hypothesis is used. The intermediate fraction field need not be normal over the original fraction field: the argument uses uniqueness of algebraic closures over the intermediate field, and does not use the existing normal-subextension automorphism-extension lemma, whose hypotheses would not justify that application.

Searched the whole DAG by strict-localization, henselization/normal-domain, algebraic-closure and embedding keywords, and the whole blueprint with blueprint_refs.py for specialization, conjugacy and algebraic closure. Read the returned candidate statements. Existing generic commutative-algebra nodes supply all the auxiliary results; no duplicate or clause-restatement node was created. The ancestor command identifies lem-per-artin-gabber-affine-curve, agreeing with the inherited blueprint.from record. Read its current DAG first proof step, the main-20261015 ancestor proof file, the chapter record and the unit record. This child serves the finite-coefficient potential-dualizing argument under the current ancestor Step 1. The off-unit statements are generic tools, individually declared with their purposes in split_report.tool_uses; they replace no perverse-unit proof step.

## Not duplicates

No new nodes. All supporting statements are reused, including the Mathlib leaf lem-pc-algebraic-closure-exists-unique and the finite-etale-over-field product leaf.

## Unfinished

None in the requested one-level split. Supporting unsplit statements are existing DAG items, not proofs claimed by this delivery.

## Review by Q66

I read ILO, Expose XVII, printed pp. 277–278: the two geometric-isomorphism diagrams in the proof of 3.5.8, and the specialization-independence and closed-point Galois-invariance statement of 3.6.1. I checked the six proof steps against the existing cited node statements, and read the supporting Stacks passages in algebra.tex (04GW, strict henselization by triples; 08HR, map into a henselian ring from an etale colimit), more-algebra.tex (06DI, normality of strict henselization; 092Q, weakly etale algebras over a field), and fields.tex (09GT/09GV, existence and uniqueness of algebraic closures). There are no new nodes needing a source comparison.

Step 1 uses the triples theorem for filteredness, locality, strict henselianity, the maximal ideal and residue identification. Its zero-prime instance gives the generic strict localization: the maximal ideal is zero, so the surjective residue map is an isomorphism. I checked functoriality clause (1), which explicitly identifies the residue field with the separable algebraic closure inside the chosen geometric field. The normal-colimit theorem states both the normal-domain assertion and injectivity of A into B; no flatness or faithful-flatness conclusion is borrowed from its proof. Normality of the local domain A is among the item's hypotheses.

Step 2 uses ind-etale stability for base change to K and weak etaleness, then the weak-etale-field statement for finite etale finitely generated subalgebras and separable algebraic residue fields. The finite-product leaf supplies precisely the finite separable field factors. A finite product embedded in a nonzero domain has one factor by idempotents; applying this to K[c] gives inverses in C. This is the short elementary argument, not a new lemma. It proves C is the fraction field before the zero-prime residue-field clause is applied. The correspondence of maps with field embeddings follows from localization and injectivity of field homomorphisms; all A-nonzero elements already map to units in the target field.

Step 3 uses both clauses of algebraic-closure existence/uniqueness. I wrote the finite-coefficient dimension argument proving that an algebraic closure of F is algebraic over K, instead of silently assuming the required base change. The relative-separable-closure definition says exactly why the embedded F lands in K^s. This proves existence, rather than assuming a specialization in order to construct one.

Step 4 applies uniqueness over F with its two different specified embeddings into Omega; both are algebraic-closure structures since polynomials over K remain polynomials over F. The resulting field automorphism fixes K and preserves the separable algebraic subfield. I checked the contravariance explicitly: (t composed with sigma)^# equals a composed with t^#. No normality of F/K is needed.

Step 5 uses the full statement of the map-into-henselian-colimit theorem. Its base is A, source and target are B, the source prime is the maximal ideal, and the residue map is the restriction of tau^#. B is henselian by Step 1, and the residue automorphism fixes k, exactly as required. Applying uniqueness to the inverse map and then to the composites proves the lift is an automorphism. The same uniqueness identifies the lift with the action on pointed etale neighbourhoods. Thus the composition is a specialization and Step 4 applies. This avoids assuming that an arbitrary closed residue action already extends to the fraction field.

Step 6 uses algebraic-closure uniqueness over F for two different ambient algebraic closures, with the direction of the field isomorphism reversed on spectra. It proves the generic-point-change clause and, after composing with the already constructed closed action, the corresponding equivariance clause. The relative-separable-closure citation justifies restricting that isomorphism to the strict-local generic fields.

I checked E1–E7 on these applications. In dimension zero, A is a field and B is its separable closure, so the construction reduces to the usual automorphisms of that closure. For a strictly henselian normal local base, B=A and F=K, and the same argument applies with no nontrivial intermediate extension. For an imperfect field, K^s can be smaller than Omega; the proof uses the former for strict localization and the latter only for algebraic-closure uniqueness, so it does not identify them. Integrality is essential to the field reduction and is used explicitly; no connectedness-only or reducible case is smuggled into the statement. Excellence, Noetherianity and henselianity of the original A are stronger than this particular argument needs, but are retained as imported. No step exceeds 2000 characters or conceals an additional comparison theorem. B1–B10 and D1–D5 hold with no new nodes; every non-elementary supporting fact is a cited statement, not a source tag standing in for a citation. C3/C4 were checked against the statements quoted in citations.json. No Lean source was written and no compiler or build tool was run.
