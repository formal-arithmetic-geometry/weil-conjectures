# Stage-1 report: lem-trf-etale-coordinate-divisor-parameters

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-coordinate-divisor-parameters.json`: item, split into six steps, no Mathlib match.
- `citations.json`: nine entries, one exact statement excerpt for every cited node in every step.
- `report.md`: this report.
- `searches.jsonl`: unmodified output log written by the required search command.

There are 0 new nodes and 0 new Mathlib leaves. The sandbox initially contained only dispatcher markers, so there was no previous split or report to recover. The item was copied from the current shared read clone; its inherited searches and ancestry were retained. No Lean, repository, launcher, unit or chapter file was written, and no compiler or git command was run by the worker.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for etale/parameter and normal-crossings terminology found no declaration giving this item. The related `RegularCodimensionTwoFiniteEtaleModel.lean` theorem concerns finite etale extension across a codimension-two boundary, not the marked coordinate divisor or its geometric branches.

## WANTED

None: the Stacks sources and ILO volume used here are present.

## Audit and changes

The imported item was statement-only. Its statement is valid; no hypothesis or conclusion was changed. I added an explicit reference to the existing algebraic strict-henselization definition at the already-present geometric branch sentence, and the corresponding statement dependency. This is a citation clarification, not a changed definition of branch.

The split uses existing `lem-trf-etale-coordinate-intersection-geometry` for its stronger assertion about arbitrary regular coordinate intersections, and existing `lem-trf-parameter-product-strict-local-branches` for the local algebra of geometric branches. Neither is a newly created restatement of an item clause. The coordinate-intersection result assumes a nonempty list, whereas this item allows r=0: Step 1 appends the unit 1, which changes no vanishing index set, to satisfy its hypothesis uniformly. I did not silently apply its s>=1 statement to an empty list.

For nonzerodivisors I use the full permutation clause of the already reviewed Stacks 00NQ node, not an unproved assertion that every member of a regular sequence acts injectively on the original ring. Each marked parameter is put FIRST in a permutation before taking the injectivity conclusion. Injectivity of the product is then composition, and the global assertion follows by the explicit annihilator/localization argument in Step 4.

The geometric-branch count is taken from the branch lemma's quotient and minimal-prime assertions, not from the normal-crossings definition or the numerical branch-count definition. The unit factor does not change either quotient ideal. This also avoids assuming that the branch number is invariant without proof: the calculation at every w gives the same index set computed at y.

## Search evidence

All new Mathlib searches were made with the prescribed `msearch.py Q79 lem-trf-etale-coordinate-divisor-parameters` command and copied verbatim from its JSONL log into `mathlib_searches`. Both natural-language formulations, Loogle `Algebra.Etale, IsRegularLocalRing`, and grep `IsRegularSystemOfParameters|[Ee]tale.*[Rr]egular|[Rr]egular.*[Ee]tale` on `RingTheory` were read. The second LeanFinder query asks specifically about regular local parameter products, their strict henselian branches, and transport under etale localization. All current services answered successfully; the inherited unavailable LeanSearch entry remains recorded as unavailable.

Hits concern standard etale presentations, formal-etale base change, `isRegular_mul_iff`, Henselian predicates, and localization of an already regular sequence. I read the source definitions in `Mathlib/RingTheory/Etale/StandardEtale.lean`, `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean`, and `isRegular_mul_iff` at `Mathlib/Algebra/Regular/Basic.lean:154`. None states the full item or gives its parameter transport and geometric branch count in one line. Multiplication of injective maps is an elementary step and does not need a new Mathlib leaf.

Before settling the dependencies I searched the whole DAG for 07QP, 0AH0, 00U4, 00NP, regular parameter systems, strict henselizations and branch terminology. `tools/blueprint_refs.py search` returned no blueprint match for `regular system of parameters`, `normal crossings`, or `07QP`. The `geometric branches` search returned only `sk-lem-curve-normalization`; I read its statement, which is about the constant-sheaf normalization exact sequence on curves and does not state this item. `ancestor` confirmed `lem-trf-local-term-locality`; the existing via chain and specific place were retained, and `same_as` remains [].

## Not duplicates

No new node was created. Existing coordinate-intersection and strict-local-branch nodes were reused instead of duplicated.

## Tool use

`lem-weil-pbc-regular-local-generators-regular-sequence` is declared in `split_report.tool_uses` as a generic Stacks 00NQ commutative-algebra tool. Its arbitrary-permutation assertion supplies the nonzerodivisor input not asserted by the same-unit coordinate-intersection node. This preserves the ILO coordinate-chart route, not an alternative proof of a unit-level step.

## Review by Q79

I read ILO Expose VIII 4.1.2 (printed p.117), 4.1.6 and 4.1.8 (printed p.118), and the surrounding 4.2.2/4.2.4 discussion on printed pp.118-119. These give the parameter-product presentation, the geometric multiplicity interpretation, and the etale-local chart use in the branch-depth argument. I checked the algebra in the actual Stacks source: 07QP is `lemma-dimension-etale-extension`, 0AH0 is `lemma-regular-etale-extension`, 00U4 is `lemma-etale-at-prime`, 00KU is `definition-regular-local`, and 00NQ is `lemma-regular-ring-CM`. No new node has a source to review because none was needed.

For Step 1 I opened the statements of `def-weil-regular-scheme`, `pqf-def-locnoeth` and `lem-trf-etale-coordinate-intersection-geometry`. The first two make Spec C a regular locally Noetherian scheme from the actual hypotheses, and the third explicitly asserts regularity, local Noetherianity, transport of EVERY full parameter system and equivalence of zero residues. Its s>=1 hypothesis is met by adding 1, including when the original list is empty. The distinct-position hypothesis is precisely the item's hypothesis. Units versus zero residue is the definition of the maximal ideal of a local ring.

Step 2 uses only the local-ring unit criterion already established in Step 1 and finite products. I checked that the product over the complement is invertible even if the marked sublist is empty, and that factorization is in the actual stalk at w.

For Step 3 I opened `lem-weil-pbc-regular-local-generators-regular-sequence` and `def-weil-pbc-regular-sequence`. The former explicitly allows every permutation, and the latter explicitly defines the first regular-sequence condition as injective multiplication on the module with no earlier parameters killed. Thus putting each marked germ first gives precisely injectivity on R, not on a different quotient. R is regular local by Step 1. The empty product gives the identity. I checked the composite order does not affect the result in this commutative ring.

Step 4 is an elementary argument, written out in full: an element whose every localization vanishes must vanish, since a maximal ideal containing its proper annihilator would give a contradiction to the localization-zero criterion. This proves the assertion on C as well as on every affine open of W; W need not be globally Noetherian or quasi-compact. The zero ring is explicitly harmless.

For Step 5 I opened `def-nagata-effective-cartier-ideal` and `def-trf-normal-crossings-divisor`. The former asks for affine-local nonzerodivisor generators, which Step 4 supplies. The latter asks for a product of a sublist of a full regular system in an etale neighborhood; the identity neighborhood, Step 1's full transported system, and Step 2's equality of principal ideals supply exactly this data. Removing a unit factor changes no closed subscheme. The empty ideal presentation is the unit ideal, as required.

For Step 6 I opened `def-sc-ring-strict-henselization` and the entire statement of `lem-trf-parameter-product-strict-local-branches`. Its hypotheses are a regular local ring, a sublist at distinct positions, and a strict henselization relative to a separable residue-field closure: these are exactly R, the marked parameters and the geometric-point choice. Its statement explicitly gives the quotient strict henselization and the count of minimal primes of its reduction, including invariance under its chosen strict-henselization representative. The ideals (h*P) and (F) coincide because their ratio is the unit v; this proves the conclusion for the actual divisor quotient, not only a formal coordinate model. For zero marked parameters the point is off the divisor and the branch count is zero.

I compared every citation excerpt with the cited statement; all nine quotes are literal substrings. Each step's non-elementary input is in its uses list, and proof_deps is exactly their union. No proof uses material only available in another node's proof. All steps have fewer than 2000 characters (maximum 1006); there is no long concealed comparison lemma. I checked r=0, fields and zero-dimensional stalks (all marked germs then units), repeated units, nonempty marked sublists with different labels, empty schemes including Spec of the zero ring, identity h, arbitrary nonaffine etale W, and points off the divisor. Repeated nonunit labels cannot satisfy the distinct-position assumption, so that does not furnish a counterexample. No statement dispute or route change was needed.

## Unfinished work

None in this one-level split. The two existing unsplit lemmas are existing downstream DAG tasks, not new work hidden in the item.

## Validation

The prescribed server `review_split` check passed before this report was written. The full `deliver.py Q79 lem-trf-etale-coordinate-divisor-parameters --no-push` invocation then exited 0 with `OK (not pushed)` and `preflight passed` at da8c2c43016. The report was updated with that observed result; the final report contents are checked again before the authorized push. The push result is supplied in the worker's final delivery response.
