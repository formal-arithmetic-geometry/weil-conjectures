# Q43 stage-1 report: lem-sfb-locally-free-derived-scalars

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-locally-free-derived-scalars.json`: existing statement node, now split in four steps; no full Mathlib match.
- `citations.json`: a verbatim statement quote for each of the eight step citations.
- `report.md` and the command-maintained `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. The sandbox initially contained only dispatcher marker files, so there was no earlier split or search log to recover. The existing item's seven historical search records and its provenance are retained; the six searches run for this delivery are appended.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, locally free/finite locally free, and flatness/scalar-extension combinations found no declaration stating all clauses on an arbitrary small ringed site. The finite locally free project APIs, étale/adic lisse results, scheme-module flatness results, and derived scalar-extension constructions each have narrower scopes or provide only part of this item. They do not support an ATTACH claim.

## WANTED

None. The literature used is present locally. The inherited historical brief references `coord/dag-sync.md`, which is absent from this shared clone; the current direct-delivery brief gives the applicable workflow.

## Findings and changes

The statement is correct and is unchanged, as are its nine statement dependencies. The missing proof is replaced by: (1) the local-basis factorization of every finite relation and the existing equational criterion; (2) bounded-above flat K-flatness for the degree-zero complex; (3) the existing K-flat change-of-rings computation with the identity resolution and an explicit naturality check; (4) the slice tensor comparison and inverse finite-basis formulas proving local freeness after scalar extension.

This supplies the flatness and ordinary-reduction assertion in paragraph (3) of `sk-lem-integral-models-generators.proof.md`, within the route of `sk-lem-integral-models`. It introduces no new coefficient category and does not substitute another route for any unit step. Four generic auxiliary statements used outside the unit are declared in `split_report.tool_uses` with their purposes.

The existing node `lem-pc-bounded-above-flat-kflat-site` has the right statement but its source place says Tag 06YS. In the local Stacks tag index, the bounded-above flat K-flatness lemma `lemma-bounded-flat-K-flat` is Tag **06YQ**; 06YS is `lemma-K-flat-resolution`. The present item's step cites the actual source label and Tag 06YQ. I did not edit that other node. This is a bibliographical issue, not an extra hypothesis or a change of statement.

## Searches and reuse

The full DAG was searched for tags 0GN1 and 06YQ, local/sheaf flatness criteria, tensor restriction, and derived change of rings. In particular, I opened the statements of `lem-weil-pbc-site-flat-equational-criterion`, `lem-pc-bounded-above-flat-kflat-site`, `lem-pur-derived-change-of-rings`, and `lem-sfb-localized-site-tensor-restriction` and reuse them. I also read the sheafification-flatness and tensor/sheafification nodes; their statements do not give the locally sectionwise hypothesis of 0GN1 directly, so I did not miscite them. The equational criterion instead makes the local-basis argument immediate, avoiding a new flatness lemma.

Whole-blueprint searches with `tools/blueprint_refs.py` used `locally free derived`, `flatness`, `locally free`, `scalar extension`, `locally finite free`, and `K-flat`, and the ancestor query confirmed `det-lem-integral-models-generators`. No other blueprint node states the whole item; `same_as` remains empty. Since no new nodes are created, there are no new/existing same-tag pairs to distinguish.

All new Mathlib queries were run through the required `msearch.py`: LeanFinder with two phrasings, Loogle `SheafOfModules.IsLocallyFree`, LeanSearch for the derived/ordinary tensor comparison, and two greps. The log records each query and its result; all services answered. The semantic hits provide free sheaves, finite presentation, and a map from a free sheaf, rather than this theorem. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean` at lines 178–207: `mapFreeIso` assumes a coproduct-preserving functor and an identified unit; it does not prove flatness or a derived comparison. `Sheaf/LocallyFree.lean` defines local generators and local freeness. `RingTheory/Flat/LocallyFree.lean` is about ordinary modules and localization on a prime spectrum, not arbitrary ringed sites. The focused sheaf-module grep found no IsFlat/KFlat/derived scalar-extension API. The complete item is consequently not a Mathlib leaf.

## Review by Q43

I read the chapter and integral-model unit, and the current blueprint generator statement and proof, especially paragraph (3)'s sentence that the lattice is flat and its derived reduction is its quotient. For the item I read Stacks `sites-modules.tex` Tag 0GN1 (`lemma-flatness-sheafification-refined`), then Tag 08FC (`lemma-flat-eq`) to verify the alternate direct local-basis proof. For the later steps I read `sites-cohomology.tex` Tags 06YQ (`lemma-bounded-flat-K-flat`) and 06YY (`lemma-derived-base-change`), and `sites-modules.tex` Tag 03EL (`lemma-tensor-product-pullback`). There are no new nodes requiring separate source checks.

In step 1, the cited slice definition really identifies sections over the terminal object of the slice with sections on the original object. The equational criterion really asks for local finite factorizations of relations with the coefficients displayed in the step. The local basis supplies the sections and coefficients, and each coordinate of the given zero relation supplies the required zero coefficient relation. Smallness and commutativity are already hypotheses of the item. This uses neither global freeness nor flatness of global sections on every site object.

In step 2, the cited statement applies to every bounded-above complex of flat module sheaves, not merely a bounded acyclic tensor input. The upper bound is zero; the zero terms are flat directly from the cited definition. I checked the tag discrepancy described above against the actual source and used the correct source place in the step.

In step 3, clause (2) of the cited change-of-rings statement explicitly computes in the derived category of the target ring and accepts a K-flat resolution for an arbitrary ring-sheaf morphism. The identity is such a resolution by step 2. The tensor definition provides the balancing relations and the target-ring action, so swapping the tensor order preserves that action. For naturality, a morphism between two inputs is a morphism between their identity resolutions; both ordinary maps act by the displayed formula, and the left-derived comparison is its natural comparison transformation. No condition that B be flat enters this reasoning.

In step 4, the cited tensor restriction node explicitly states the isomorphism on any slice and its pure-tensor formula. That formula also checks B-linearity. The two maps between the local scalar extension and B to the r-th power are written out; their composites are identities by balancing and the coordinate basis equations, and both commute with restriction. This is a few-line finite-basis computation from the cited tensor definition, so it is elementary rather than a new lemma. The ranks are those of the given trivializations, with no claim of rank uniqueness over the zero ring.

I checked delivery-errors B–E: all objects are introduced, the statement is unchanged, no new unsplit statements or duplicate lemmas were made, every non-elementary input has a cited node whose statement says it, and no proof of another node is used as an interface. The finite coordinate calculations remain steps. All steps are shorter than 2000 characters. Edge cases checked: rank zero, rank varying between cover members, the zero ring, an empty covering allowed by the site, the identity scalar map, and R=Z with B=Z/2 and M=Z to check that B-flatness is unnecessary. A site without enough points also works because the proof uses relations and coverings, not stalks.

## Unfinished work

None in the authorized one-level split. No Lean was written or compiled. The prescribed server dry run passed: `OK (not pushed)` at `caa0765c3ac`, including the server preflight. The report then received this validation note and a correction of the count of newly logged searches from seven to six; a final dry run is performed on this report before pushing.
