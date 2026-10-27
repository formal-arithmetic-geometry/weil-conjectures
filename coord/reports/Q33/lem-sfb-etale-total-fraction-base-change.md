## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-total-fraction-base-change.json`: statement item, now split into six steps. No exact Mathlib match; five freshly logged searches supplement the retained inherited records.
- `citations.json`: 14 step/node entries quoting the existing statements verbatim.
- `report.md`: this report. Sandbox-only `write_split.py` reconstructs the node and citation manifest; it is not project content.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the item id and for total quotient/fraction terminology alongside etale/étale. The general fraction-ring search found `IsFractionRing.tensorProduct_of_comap_eq_bot`, `WeilConjectures/Mathlib/RingTheory/Localization/BaseChange.lean:32`; reading it shows domain hypotheses on BOTH rings and an injective map, so it does not state this item for reduced rings or disconnected étale algebras. No attachment is claimed.

## WANTED

None. The needed Stacks sources are present locally.

## Audit findings and changes

The imported item is mathematically correct, including the map to the zero ring. Its statement and statement dependencies are retained verbatim. Its proof was empty. There was no earlier sandbox node, report or search log to repair. No repair note exists for the item.

The inherited blueprint ancestor is null (confirmed by `tools/blueprint_refs.py ancestor`); its long `from.place` and `via` provenance is retained, not replaced with an invented blueprint id. The current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3), still provides the proper-direct-image context for this supporting branch. It does not itself state this commutative-algebra comparison. Searching the entire imported blueprint for “total ring of fractions” returned no match; broader etale searches and a DAG-wide source-tag/concept search supplied the existing nodes instead.

Read `literature/stacks-project/spaces-divisors.tex`, Tag 0EN6, label `lemma-meromorphic-quasi-coherent`, including the proof's flatness parenthesis, displayed tensor comparison, generic-factor decomposition, and final paragraph identifying the factors. Read Algebra Tag 02LX, `lemma-total-ring-fractions-no-embedded-points`, and Tag 05C3, `lemma-weakly-ass-zero-divisors`, which it cites. The reduced Noetherian case can use fields at the minimal primes; the existing node `lem-weil-pbc-reduced-noetherian-total-ring-fractions` states exactly this stronger specialization, so no associated-prime or henselian-local-ring nodes are needed. Read Algebra Tag 00U3, `lemma-etale-over-field`, and Morphisms Tag 02GO, `lemma-base-change-etale`.

The proof follows the generic-field route of 0EN6, with an agent-written final localization argument rather than silently importing the source's “clearly implies” identification of every minimal prime of B. Accordingly `proof_origin.by` is `agent`. There is no statement dispute and no change to the unit route.

## Not duplicates

No new nodes. Existing statements were reused for reduced Noetherian total fractions, affine flatness, localization base change, tensor products with finite products, affine fibre products, étale base change and étale algebras over fields. In particular `lem-sc-affine-totalquotient-minimal-product` has the more general weak-associated-prime hypothesis; the reused reduced-Noetherian node already provides the field factors required here.

## Tool use

`lem-weil-pbc-reduced-noetherian-total-ring-fractions` is a generic commutative-algebra tool from `sk-thm-p1`, declared in `split_report.tool_uses`. The six-functor unit has no ring-theoretic replacement; this is precisely the 02LX input named in the item's source. All other theorem citations are existing Mathlib leaves, and definition citations introduce their actual notions.

## Review by Q33

I opened the source paragraphs named above and every existing node cited in the six steps. There are no new node statements or new source claims to review.

Step 1 uses `def-weil-etale-morphism` for its explicit flatness clause, `lem-weil-pbc-flat-morphism-affine-criterion` for module flatness of this global affine ring map, and `def-weil-pbc-flat-ring-map` for preservation of injections under tensor. These statements say the exact implications used. I wrote the map A tensor B → B explicitly, so “flatness” does not hide an extra exactness assertion or assume faithful flatness. A→0 is allowed.

Step 2 uses `lem-weil-pbc-localization-base-change`, whose statement gives both the tensor localization and the denominator description, plus `def-weil-pbc-module-localization`, whose statement includes the zero criterion. Tensor-factor interchange is the elementary bilinear interchange map and its inverse. Step 1 proves all denominators are regular, which justifies injectivity of B→C without assuming B is a domain. This step establishes C as a localization at f(T_A), not prematurely at T_B.

Step 3 uses both clauses of `lem-weil-pbc-reduced-noetherian-total-ring-fractions`: the factors are fields and the canonical compatible product map is an isomorphism. Its reduced and Noetherian hypotheses are exactly the item's. It also cites `lem-weil-pbc-tensor-finite-product`, whose statement really is a module isomorphism. I added the pure-tensor check that upgrades this specific isomorphism to one of rings; this avoids taking a ring assertion from a module-only statement. `def-weil-pbc-module-tensor-product` supplies generation by pure tensors. No finiteness of the map A→B is assumed.

Step 4 cites `lem-weil-pbc-fibre-product-affine-spectra` for the actual fibre-product identification with its projection, `lem-weil-pbc-etale-scheme-base-change` for etaleness of that projection, and `lem-weil-pbc-etale-algebra-over-field-product` for a finite product of extension fields. All three statements were opened and match those uses. Each K_i is a field by Step 3. No claim that an arbitrary étale B/A is finite is made: only its base changes to these fields are finite products, exactly as 00U3 asserts. Zero factors n_i=0 are explicitly allowed in that node.

Step 5 is elementary relative to Step 2 and the fraction relation in `def-weil-pbc-module-localization`: if (t b)/f(s)=0, there is u with f(u)t b=0. Both factors are regular by Step 1 and t∈T_B, so b=0. This proves regularity after localization rather than invoking it without a cited lemma. The finite-product argument is coordinatewise: if a coordinate vanished it would kill that coordinate's nonzero idempotent; inverse coordinates give a unit. This is a few-line argument, not a new lemma node.

Step 6 also uses only the explicit fraction relation and tensor formulas of the two cited definition nodes. I checked well-definedness for arbitrary equivalent fractions using the unit j(v), wrote the two inverse maps, and checked the precise requested formula on (a/s) tensor b. Thus this proves the canonical B-algebra map, not an unspecified abstract ring isomorphism. It does not assume any map Q(B)→C before establishing all T_B denominators are units.

I checked the delivery-errors B–E requirements: the node is self-contained already; no proof sketch was exported as a new statement, no clause was renamed into a child node, no uncited non-elementary comparison occurs, and no cited node's internal proof is being used. The only ring comparison proved inline is the elementary multiplication check on an already-cited module isomorphism. All six steps are shorter than 2000 characters (maximum 793), and each gives the actual argument. `proof_deps` is the exact union of uses. The original statement, sources, created record and blueprint fields are preserved. No SGA source is used.

Small cases checked: A=0 forces B=0 for a unital homomorphism; B=0 gives empty field factors and the unique unit in the zero ring; A a field reduces directly to the finite étale field-product statement; A a product of two fields with B one factor tests a noninjective étale map; A=k[x,y]/(xy), B=A[1/x] tests a reduced ring with intersecting components and deletion of a generic factor. The proof uses no injectivity of f and allows factors to disappear. The finite-product argument handles empty products without excluding any case.

The first proposed argument might have quoted the final “clearly implies” line of 0EN6 without giving the minimal-prime comparison. I replaced that potential gap before writing the split by the explicit unit-denominator and inverse-fraction argument of Steps 5–6. No correction to a statement was necessary.

Mathlib searches were performed exclusively through the mandated msearch.py command. I read its actual hits; the algebraic base-change candidate in `Mathlib/RingTheory/Algebraic/Integral.lean:502–531` requires `FaithfulSMul` and `NoZeroDivisors` for the target and is not a one-line specialization for this item. `Algebra.Etale.baseChange` (`Etale/Basic.lean:242`) is stability only; the Away tensor equivalences (`Localization/BaseChange.lean:459–475`) localize at powers of one element. These do not state the entire comparison. All five fresh logs are recorded exactly; no unavailable service is recorded as a negative match.

## Unfinished work

None in the stage-1 mathematical split. Delivery is subject to the required server checks and independent maintainer review.
