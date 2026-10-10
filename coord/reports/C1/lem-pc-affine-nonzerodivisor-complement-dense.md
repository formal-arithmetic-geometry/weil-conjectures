Files written:

- `dag/nodes/sec-picard-framework/lem-pc-affine-nonzerodivisor-complement-dense.json` — statement, split proof, and citations to the affine localization calculation.
- `dag/nodes/sec-picard-framework/lem-pc-affine-localization-injective.json` — statement, Mathlib verdict: match (`IsLocalization.injective`).
- `dag/nodes/sec-picard-framework/lem-pc-principal-open-dense-of-nonzerodivisor.json` — statement-only node, Mathlib verdict: no match.
- `citations.json` — verbatim statement quotes for every proof citation.

Attachments:

- None. A grep of the slopmaster2 source found no declaration tagged `lem-pc-affine-nonzerodivisor-complement-dense` and no declaration stating the item exactly.

WANTED:

- None. The cited Stacks source is represented by the existing project citation path `literature/stacks-project/divisors.tex`, Tag 07ZU.

What was checked or corrected:

- The imported item was already stated with the correct hypotheses and conclusion, so its statement and statement dependency were retained. Its blueprint ancestor is `lem-pc-degree-base-change`, proof part (2), affine calculation for the complement of an effective Cartier divisor.
- The Stacks Tag 07ZU affine argument was read. Its localization-injectivity assertion was separated into `lem-pc-affine-localization-injective`; its density assertion was separated into `lem-pc-principal-open-dense-of-nonzerodivisor`. Searches of the whole DAG and blueprint found no duplicates.
- Step 1 checks the sheaf map on principal affine opens: localization at `g` preserves regularity of `a`, then the cited localization-injectivity statement applies. Both cited statements say exactly those facts, and both are recorded in `citations.json`.
- Step 2 cites the exact statement-only density node. The proof dependency union matches the step uses, and all new nodes have blueprint provenance and three Mathlib search records.
- Small cases checked: `A = k[t], a = t` gives `D(t)` dense and `k[t] -> k[t,t^{-1}]` injective; `A = k, a = 1` gives the identity open; a ring with zero divisors was excluded because the nonzerodivisor hypothesis is essential.

## Review by C1

I checked the item against the Tag 07ZU affine-local calculation and against the existing `lem-pc-cartier-divisor-nowhere-dense` use site. The item’s map is checked on the affine principal-open basis, where it is a localization map. I opened `lem-pc-localization-preserves-nonzerodivisor` and verified that it states regularity survives localization, and I added the separate injectivity node because the former does not itself state injectivity. I verified the injectivity node against `IsLocalization.injective` in Mathlib and recorded the specialization through powers of a nonzerodivisor. I also checked that no existing DAG or blueprint node states the principal-open density assertion; that assertion is therefore a statement-only node with a complete source citation and explicit no-match searches. Every proof citation is quoted verbatim in `citations.json`, and the step uses and `proof_deps` agree.

What I could not finish:

- Nothing remains unfinished in the split. The maintainer review script run from the read-only repository cannot see the sandbox files; the delivery preflight is the authoritative dry run for these files.
