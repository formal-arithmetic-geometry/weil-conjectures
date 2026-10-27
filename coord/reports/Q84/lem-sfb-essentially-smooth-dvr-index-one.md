## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-essentially-smooth-dvr-index-one.json`: item, statement unchanged, five proof steps, Mathlib searches find no exact match. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each step/node pair (24 entries).
- `searches.jsonl`: five actual searches for this item, including a second semantic phrasing; all services answered. The inherited Q36 searches in the item are preserved.

## Attachments

None. Searched the live project's WeilConjectures tree for the blueprint id and for smoothness, DVR, uniformizer, and ramification terminology. No declaration found states all the clauses. The candidate unramified criteria in Mathlib require formally unramifiedness and algebraic residue separability, which do not follow here when the residue field is transcendental.

## Wanted literature

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, §3.6 Definition 1 and the following essentially-smooth characterization, printed p.78 (PDF p.84), for lem-sfb-essentially-smooth-dvr-index-one. The repository has no local BLR PDF. I did not download it; the proof is explicitly marked agent-written and assembled from local Stacks sources.

## Problems found

The item has no mathematical statement error. In particular separably generated here allows transcendental residue extensions and is stronger than merely recording ramification index one; it must not be confused with formally unramifiedness. The existing blueprint provenance has `from.node: null`; the required ancestor command returns null too, so I preserved it and the inherited via list, and retained the precise source-place description. Searches of the full blueprint for essentially smooth, smooth domain, geometrically reduced field, separability, and local ring fibre found no alternative exact statement. The latest blueprint's direct-image proof (3) is still the compactification/direct-image route; the present proof is only its inherited lower trait-extension prerequisite and changes no unit or chapter route.

## Unfinished work

None in the one-level split. All inputs already have DAG nodes. No Lean was written or compiled. The missing primary BLR PDF prevents claiming a verbatim source-following proof, not the agent proof given here.

## Review by Q84

I read the local Stacks statements and their proofs at Schemes 0HA1 (fibre local ring quotient), Algebra 00PD (DVR characterization and power factorization), Algebra 04KN (geometric reducedness under localization and its tensor/localization hint), Algebra 030W (geometrically reduced field implies separable in positive characteristic), the characteristic-zero passage at 00TX, and Fields 030F and 09GH (transcendence bases and finiteness from algebraic generators). I also read the smooth geometric reducedness proof in Varieties 056T and the finite-presentation base-change statement at Algebra 05G5. No new node needs its own source review. This is an agent assembly because the BLR source requested in the imported item is unavailable locally.

Step 1 uses `lem-sbc-scheme-fibre-stalk-quotient`, whose statement supplies the quotient by the extended maximal ideal with its actual stalk map, and `lem-weil-pbc-affine-open-stalk-localization` to identify the base stalk with D. Since D is local at its maximal ideal, all localization denominators are already units. `sbc-lem-smooth-geometrically-reduced` supplies precisely geometric reducedness of the scheme fibre; `def-pc-reduced-scheme` explicitly includes both section and stalk characterizations. Thus this is the fibre stalk, not the whole fibre ring.

Step 2 uses `def-sc-discrete-valuation-ring`, `lem-weil-pbc-dvr-unit-times-uniformizer-power`, and `def-weil-residue-field`. The first supplies a nonzero principal maximal ideal and the domain property; its stated 00PD equivalence also gives the Noetherian hypothesis of the power-factorization theorem. The map's injectivity is used for nonvanishing of pi and locality for its being a nonunit. The proof writes out the cancellation that shows the putative nilpotent class is nonzero. The residue identification is canonical over k because the quotient isomorphism of Step 1 is induced by the stalk map. No theorem asserting the desired common uniformizer is hidden as a new node.

Step 3 uses the smooth-morphism and locally-finite-presentation definitions, which say exactly that affine finite-presentation models exist. An affine base neighbourhood containing the closed point of Spec D is the whole local scheme; this observation is explicitly written out. `lem-weil-pbc-fibre-product-affine-spectra` identifies the fibre chart as Spec(B tensor_D k), including its projections. `lem-weil-pbc-open-immersion-base-change` says this chart is open in the actual fibre. `lem-weil-pbc-finite-presentation-base-change-composition` gives the finite presentation, and `lem-weil-pbc-affine-open-stalk-localization` gives the ring C_q. Every hypothesis is satisfied without requiring X to be globally finite type or quasi-compact.

Step 4 cites the same affine-fibre-product and open-base-change statements, the section characterization of `def-pc-reduced-scheme`, and `lem-weil-pbc-localization-tensor-over-base`. The last states the localization comparison as a module isomorphism. The written fraction formulas verify its multiplicativity too, so it is the ring comparison needed here; there is no unquoted extra ring theorem. I expanded the omitted reduced-localization argument directly: va^N=0 implies (va)^N=0, hence va=0. This works for every scalar extension, including tensor rings with zero divisors and arbitrary transcendental extensions. The image denominators need not be units until localized, which the argument respects.

Step 5 uses `lem-weil-pbc-geometrically-reduced-extension-separable` only in positive characteristic, and `lem-weil-pbc-char-zero-field-extension-separable` only in characteristic zero. Both state nonalgebraic separability, not just separability of algebraic elements. The fraction formulas in `def-weil-pbc-localization-at-prime` identify the residue field of C_q with Frac(C/q); the finite chart generators therefore generate F as a field. `def-weil-pbc-separable-field-extension` then applies to F itself. `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis` gives one finite basis, while `def-kun-transcendence-degree` says its cardinality equals that of any transcendence basis, making the separating basis finite too. Finally `lem-weil-pbc-algebraic-generators-finite-extension` states the exact finiteness result for the algebraic remainder. This avoids silently replacing separably generated by finite separable over k.

For small cases I checked X=Spec D (trivial residue extension, empty basis), D[t] at (pi) (residue k(t), a one-element basis, common uniformizer), and an etale DVR extension with nontrivial finite separable residue field (empty basis, finite algebraic remainder). Over an imperfect field the argument uses geometric reducedness, not perfection. The nonsmooth ramified example pi=t^e for e>1 produces exactly the nonzero nilpotent exhibited in Step 2, confirming why smoothness is needed. X empty has no x and is vacuous. No excellence or completeness was used.

Against delivery-errors B–E: there are no new statement-only nodes to duplicate or disguise a clause as; definitions and non-elementary tools are all explicit cited statements, with copied quotations. Every external-unit statement is a generic tool, declared with its purpose in `split_report.tool_uses`; none replaces the ambient direct-image route. I checked hypotheses, actual quotient objects, the tensor localization formulas, both characteristic cases, and finite generation. All five steps are shorter than 2000 characters. I corrected the draft's source-tag descriptions to 01JQ (affine fibre products) and 05G5 (finite-presentation base change), rather than citing section 01JO or the unrelated description of 00F4. The server-only review_split check passed before this report.

## Not duplicates

No new nodes. Existing fibre-stalk, DVR-factorization, tensor-localization, and field-separability nodes are reused directly.
