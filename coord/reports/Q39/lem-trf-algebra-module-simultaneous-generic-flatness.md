# Q39 stage-1 delivery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-algebra-module-simultaneous-generic-flatness.json`: split statement, not a Mathlib leaf; four proof steps using existing nodes only.
- `citations.json`: ten verbatim statement quotations, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the unchanged search-command log.

New DAG nodes: 0. New Mathlib leaves: 0. The existing leaf `lem-weil-pbc-flat-module-retract` is reused.

## Attachments

None for this item. Searching `lean/WeilConjectures/` for the exact blueprint tag and for generic flatness found no declaration stating the simultaneous module/algebra conclusion. `RingHom.exists_nonzero_flat_localizationAway`, in `lean/WeilConjectures/RingTheory/GenericFlatness.lean:160`, belongs to the already attached node `lem-sbc-finite-type-algebra-generic-flatness`: it covers the algebra only. I read its statement and complete proof, including the three private helpers. This is evidence for using that existing node, not for attaching the present item.

## WANTED

None. The relevant Stacks sources and current blueprint are available locally.

## What changed and why

The imported item had a complete statement but no proof. Its source explicitly suggests the square-zero reduction. I preserve the statement, its hypotheses, and its statement dependencies. I apply the existing algebra-only generic-flatness theorem to the finite type algebra C = B direct-sum M with square-zero multiplication. Finite generation is proved by explicit generators. After localizing C, the two desired localizations are its module retracts by four explicit fraction formulas. The existing flat-retract Mathlib leaf finishes the proof.

I corrected the source's location of the application of Tag 0573: that lemma is in `literature/stacks-project/more-morphisms.tex`, not `algebra.tex`. Tag 051T itself is in `algebra.tex`. This is a bibliographic correction; there is no statement dispute.

Whole-DAG title/concept searches found the existing square-zero definition, algebra generic-flatness theorem, and flat-module-retract leaf. I read their statements rather than borrowing their proofs. Blueprint searches for `generic flatness`, `051T`, `square-zero`, `TrivSqZeroExt`, and `flat direct summand` found no blueprint node stating this simultaneous algebra/module claim. The lone `square-zero` blueprint hit is a Nagata setup, not a duplicate. The current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md` retains the contracting-correspondence argument. The inherited Tag 0573 algebraic subargument is below that unit, and this delivery does not replace its route.

I retained the item's historical Q93 searches and added the exact six commands in this sandbox's search log. LeanFinder was tried with both the direct statement and the square-zero formulation; Loogle, LeanSearch and two grep patterns also ran. Their results concern flat localization, local flatness criteria, smooth algebras, or the unrelated `genericPolyMap`. None supplies simultaneous generic flatness under the item's hypotheses. In particular, flatness of a localization ring does not prove an arbitrary localized module flat. There are no newly created nodes needing search provenance.

## Tool uses

`lem-sbc-finite-type-algebra-generic-flatness` is an off-unit commutative-algebra tool, giving the nonzero localization of C. `def-sc-trivial-square-zero-extension` is an existing off-unit notion. Both are declared in `split_report.tool_uses`. The flat-retract node is already Mathlib. The trace unit gives none of these algebraic facts; using them below its route does not change the route.

## Not duplicates

No new nodes. In particular, finite generation of C and localization of the coordinate inclusions/projections are elementary steps proved explicitly, not newly named nodes or copies of clauses of the item.

## Review by Q39

For the item I read Stacks Tag 051T, `algebra.tex`, label `lemma-generic-flatness`, including its polynomial-module reduction and general finite-type case. Its conclusion gives even freeness over A localized at a; our weaker flatness over A is faithfully the clause used in the third paragraph of Tag 0573, `more-morphisms.tex`, label `lemma-scheme-theoretically-dense-generic-fibre`. I read that paragraph and the surrounding reduction: it requires the chart algebra and the finite cokernel flat over the same base. Our square-zero argument proves precisely that simultaneous flatness. It is an agent-written reduction to an existing theorem, so `proof_origin.by` is `agent`, not a claim that Stacks gives this particular proof. There are no new-node sources to audit. I also read the square-zero model in Tag 0B2B (`varieties.tex`, `lemma-tangent-space`) and checked `Module.Flat.of_retract` at Mathlib/RingTheory/Flat/Basic.lean:172–179 as read-only source.

Step 1 uses exactly the statements of `def-weil-pbc-finite-type-algebra`, `def-weil-finitely-generated-module`, and `def-sc-trivial-square-zero-extension`. The first two give the finite sets of generators and their polynomial/linear expressions. The third gives the multiplication used in the displayed generator identity. Consequently this step is an elementary evaluation and finite-generation argument, with no Noetherian assumption, no presentation theorem, and no hidden module-flatness claim.

Step 2 uses `lem-sbc-finite-type-algebra-generic-flatness`, whose statement permits any commutative finite type algebra over any domain and any model of its principal localization. Here A is exactly the given domain and step 1 establishes the required finite type property for C. Its statement does not require C to be a domain, the structure map to be injective, or any finite presentation hypothesis. `def-weil-ring-localization-away` supplies F as the particular localization model. `def-weil-pbc-flat-ring-map` explicitly equates flatness of the composite ring map with flatness of its underlying A-module. Thus the cited statements give everything used in this non-elementary step, including a nonzero element in the base rather than an arbitrary element of B.

Step 3 uses the full fraction definitions in `def-weil-ring-localization-away` and `def-weil-pbc-module-localization-away`, together with the multiplication in `def-sc-trivial-square-zero-extension`. I checked the equality relation coordinate by coordinate: t to the j is (s to the j,0), so a witnessing exponent for a pair of C-fractions witnesses equality of each projected fraction. Conversely a witnessing exponent in one coordinate works after inclusion with zero other coordinate. This proves well-definedness of all four displayed maps directly; addition and A-linearity are the stated fraction formulas. Both retraction equations hold on every fraction. No general assertion about localization commuting with products, exactness, or tensor comparison is being used without a cited node.

Step 4 uses the full statement of `lem-weil-pbc-flat-module-retract`, twice with R = A and ambient module F. Step 2 proves its flatness hypothesis, and step 3 gives linear maps and the two identity composites. Its conclusion is flatness as A-modules, exactly as requested, not merely flatness as B-localized modules. The same a is retained in both applications. I placed a verbatim statement quotation for every citation of every step in `citations.json` and checked every cited node's statement in the read repository.

For small cases, M = 0 gives the ordinary algebra theorem and a zero module retract; B = 0 forces M = 0 and the construction and maps still work. If A is a field, no nonzero denominator can create a difficulty and all modules are already flat over A. For a noninjective structure map, take A = Z, B = Z/2, M = B: inverting the nonzero base element 2 can annihilate the whole square-zero algebra and both desired localizations; the formulas remain valid and do not assume s is nonzero in B. Non-Noetherian A causes no missing hypothesis because the existing algebra theorem expressly allows it. Empty generator lists, nonfaithful M, and torsion in M likewise do not change any equation.

I checked delivery-errors B–E against the written split: no new-node format, duplicate, or unsplit-proof problem arises; all non-elementary uses are cited statements; the proof does not apply a renamed copy of either clause; there is no induction or circular construction; the scalar actions and denominators are fixed explicitly. No step exceeds 2000 characters (lengths 558, 463, 912, 439), and the elementary steps contain only the written generator and fraction calculations. The bibliographic location above is the only correction discovered.

## Unfinished work

None in this one-level split. Existing dependency nodes are reused as required; this delivery does not claim that it has independently completed all stages below them.
