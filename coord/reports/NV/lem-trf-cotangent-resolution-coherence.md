# Worker report: lem-trf-cotangent-resolution-coherence

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-cotangent-resolution-coherence.json`: replaced the returned proof with nine explicit steps; statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-adjunction-standard-simplicial-homotopy.json`: new statement-only generic adjunction lemma, unsplit; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-simplicial-derived-colimit-computation.json`: new statement-only generic derived-colimit computation and naturality lemma, unsplit; no exact Mathlib match.
- `citations.json`: one verbatim statement quotation for each of the seventeen proof uses.

The four children proposed by the superseded local repair were removed from the delivery set. Their files, the old report, and the old citations are retained under `repair-history/`. Existing search logs are retained, including unsuccessful searches for those superseded proposals. New searches are recorded by msearch.py under this item's sandbox, with their full results in `repair-search-*.txt`.

## Attachments

None. Searching WeilConjectures for the blueprint tag, cotangent/resolution combinations, comonad, derived colimit and cosimplicial resolution found no project declaration stating this item or either new lemma. The upstream master is reference material, not a finished-proof certificate. Mathlib's low-degree algebra-presentation cotangent complex is not the full simplicial derived object in the item.

## WANTED

None. All mathematical sources used are present in literature/stacks-project.

## Repair of the return

The returned head was f50e88263f, recorded in coord/returns/NV.md. I compared the retained work with the current shared item and rebuilt the split rather than re-pushing it unchanged.

A.4: both genuinely new nodes have `created.item = lem-trf-cotangent-resolution-coherence`, group NV. The existing item's `created` record is restored verbatim from the current repository: Q86 created it while splitting lem-trf-lci-cotangent-presentation. That parent name is historical provenance, not an erroneous new-node stamp. The item's split_report.item names this delivery. Existing maintainer-owned metadata is not rewritten.

C.1/C.3/C.4: the former comparison assertion about algebra maps with homotopy inverse composites is removed. Degreewise polynomial does not assert the cofibrancy needed for that argument, and 08QI does not state it. The old free-module assertion also conflated the free B-module on the underlying set of B with B itself. The replacement uses the polynomial-presentation category and derived colimit from 08PS and 08Q9. No part of another node's proof is imported as an unstated theorem. The new generic derived-colimit lemma explicitly states its comparison map, bar model, reindexing square, and coefficient restriction. The item then supplies the generator-fibre argument, category/coefficients transformation, comparison formula and cancellation calculation.

C.4/E.7 and unit realization: sk-i-curve-zero currently has two contraction/Frobenius steps, both realized by lem-trf-local-term-locality. This auxiliary cotangent node is not its key node and does not realize either step directly. I removed the old report's claim that it did. The current inherited blueprint.from retains the historical semistable/lci support chain; I preserve this historical ancestry exactly, as coord/dag-sync.md requires. No unit file is included and no realized field is overwritten. If maintenance wishes to retire or rebind this historical branch after the unit-route correction, that is an existing-node metadata decision, not a new realization claimed by this delivery.

## Sources and searches

For the item I read cotangent.tex, standard-resolution construction 08PM/08PN; polynomial-presentation category and 08PS (lemma-identify-pi-shriek), including its generator-fibre proof and size footnote; 08QI (remark-resolution); and 08QL (section-functoriality), including the final omitted-verification sentence. I read the cited sources of those arguments: simplicial.tex 08NC, 08ND, 08P1, 08P2, and sites-cohomology.tex 08Q9, 08PG (example-left-derived-colimits), 08PH (example-morphism-categories), and 08PD. The naturality omitted in the cotangent section is an explicit clause of the new generic computation lemma, with its bar-chain formula; it is not called elementary in the item.

For the new adjunction lemma I read the formulas in Situation 08N9 and both proofs 08NC/08ND. Its F is Stacks' left adjoint U; its U is Stacks' right adjoint V. Thus FU is a comonad, with counit evaluation and comultiplication FηU. The new lemma is about arbitrary adjunctions, not just the polynomial-resolution clause of this item. Its statement introduces the adjunction and the meaning of its simplicial homotopy assertion.

For the new derived-colimit lemma I read 08Q9's double-complex comparison roof and 08PG/08PH's explicit bar complex and reindexing chain map. Taking C=D^op translates their presheaf convention to the covariant diagram convention used here. Both Q and Q' must have contractible representable evaluations; uQ need not. Restriction of scalars is exact and commutes with direct sums, so on these bar models the coefficient restriction is degreewise restriction. The displayed formula for each summand is unchanged. This coefficient statement is part of the new lemma, not an appeal to an unstated base-change theorem.

Before creating these two nodes I searched the whole DAG's statements/sources for 08NC, 08ND, 08Q9, 08PD, standard simplicial resolutions, adjunctions/comonads and derived colimits, and ran blueprint_refs.py searches for standard simplicial, comonad, derived colimit and cosimplicial resolution. No existing blueprint node states either lemma. The current item's ancestor command returns lem-trf-local-term-locality; new ancestry adds this item to the existing via chain. The generic module model, normalized/alternating equivalence, Kan criterion and trivial-Kan homotopy result already exist and are cited instead of being recreated.

Each new node has actual LeanFinder, LeanSearch, Loogle and source-grep searches, plus a second natural-language phrasing; queries and digests are copied from searches.jsonl. ExtraDegeneracy.lean supplies homotopies *given* extra degeneracies, but not the arbitrary adjunction bar construction. I read its structures and homotopy definitions. The presheaf-colimit hits are ordinary colimits and Yoneda generators, and the group bar resolution is specific to representations; I read the returned types and ModuleCat/Presheaf/Generator.lean. None specializes in one line to either new statement. The old item searches remain applicable because its statement has not changed.

## Not duplicates

lem-trf-adjunction-standard-simplicial-homotopy vs def-coef-free-category-comonad: the latter only defines the free-category comonad; it neither constructs the simplicial object of an arbitrary adjunction nor states the two augmentation homotopy equivalences.

lem-trf-adjunction-standard-simplicial-homotopy vs lem-coef-free-resolution-coproduct-augmentation: the latter concerns a free-category resolution after adjoining a fixed category, not arbitrary adjunctions or polynomial algebras.

lem-trf-adjunction-standard-simplicial-homotopy vs lem-coef-dk-cofibrant-localization-comparison: the latter compares free-category and hammock localizations and does not give the asserted arbitrary-adjunction construction.

lem-trf-simplicial-derived-colimit-computation vs sk-prop-sf-comparison: the latter is the bounded-below étale/pro-étale cohomology comparison, not homology of arbitrary small ordinary categories or its bar computation.

lem-trf-simplicial-derived-colimit-computation vs det-sf-comparison-affine-continuity: the latter concerns a cofiltered pro-étale affine limit and its cohomology, not derived colimits of a module diagram evaluated on a representably contractible simplicial object.

## Review by NV

I opened every cited node's statement and copied the part used (in citations.json, the full statement) rather than substituting a theorem from its proof. My substantive checks, step by step, were:

1. The new adjunction lemma explicitly provides the bar object and underlying homotopy equivalence. The free-polynomial adjunction and degreewise surjectivity are checked on variables. The section is only a set map, avoiding the returned erroneous module contraction.
2. lem-cbc-realization-weak-equivalence states precisely the mapping-components test; the inverse on those components is written out using the supplied simplicial homotopies. lem-cbc-simplicial-module-model states both creation of weak equivalences and their normalized-quasi-isomorphism characterization. lem-cbc-normalized-alternating-homotopy-equivalence explicitly gives a natural chain homotopy equivalence. Those are exactly the statements needed to obtain the alternating augmentation; the constant complex calculation is included.
3. The same normalization equivalence and model lemma apply to Z-modules. The normalized lift is not inferred just from degreewise surjectivity: the descending correction x-s_(k-1)d_k(x) is written explicitly and preserves the image. The model lemma states the positive normalized degree criterion for fibrations, and lem-coef-kan-quillen-right-proper identifies underlying trivial fibrations with all boundary lifts, including n=0. This agrees with the quoted definition of trivial Kan fibration.
4. def-weil-size-convention permits nested universes. All polynomial presentations, including arbitrary sets of variables for the given resolutions, form a set only in the containing universe. I do not apply a small-colimit theorem to an unbounded large category. The generator description is the universal property of A[E], not Yoneda full faithfulness.
5. def-weil-pbc-trivial-kan-fibration states boundary lifts, and I construct those lifts generator by generator, including degree zero. The quoted lem-weil-pbc-trivial-kan-homotopy-equivalence states an actual section and homotopy, so its conclusion supplies exactly the contractibility required in Step 6.
6. def-weil-pbc-kahler-differentials includes the universal derivation and its explicit relations, so it gives the functor on presentation maps. The new computation lemma states an isomorphism for these *covariant* diagrams, not just an equality of homology groups. Its hypotheses were established in Steps 4–5. The derived-category definition justifies the ambient localization; the comparison is c_Q=a_std^-1 a_Q and the naturality equation is given.
7. This is an elementary generator calculation: evaluation and insertion commute because their values on each generator agree. Polynomial-map uniqueness proves strict identities and composition, and the differential rule respects the universal derivation relations. The only cited fact is exactly the universal differential statement. There is no monad/comonad conflation and no uncited coherence theorem.
8. This is the tensor-product universal property and the same differential relations, with the functor u and theta written down. Both directions of the polynomial-base-change isomorphism fix coefficients and variables. A supplied cross-resolution map produces k by q⊗a'↦h(q)a'. No claim that base change preserves a resolution, no flatness assumption and no Tor-independent base-change theorem are used.
9. The new lemma explicitly states the naturality square for precisely (u,theta,k), including coefficient restriction. The displayed equations imply c_Q' K(h)=K(t)c_Q by multiplying by inverse isomorphisms; arbitrary-resolution transport is the written conjugation formula, with identity, composition and change-of-resolution checked by cancellation. No algebra map between arbitrary choices is asserted to exist.

I checked the new adjunction statement on the identity adjunction (the object is constant), and on the free-polynomial/underlying-set adjunction including A=B=0. The derived-colimit statement for a one-object identity-only category with constant Q reduces to the alternating constant complex quasi-isomorphic to F(*). For the empty category there is no Q:Delta^op→D, so the hypothesis is not accidentally satisfied. I checked empty generator sets, infinitely many generators, n=0, identity squares, composite squares, and nonflat A→A'; none requires a missing finiteness, nonzero-ring, flatness or cofibrancy hypothesis. I also checked the normalized correction in degrees 1 and 2 and its preservation of already vanishing higher faces.

B1–B9: the two new nodes are statement-only, introduce their objects, define or cite their technical notions, use single TeX escaping, carry exact source labels/tags, preserve ancestry and record real searches. C1–C8: every substantive external inference is a cited statement; the only off-unit lemmas are generic simplicial/module tools declared under split_report.tool_uses, not replacements for a geometric route. D1–D5: neither new lemma mentions the cotangent complex; the item retains the presentation-category argument and the actual square/transport calculation. E1–E7: I corrected the earlier wrong-object and unsupported-comparison steps and checked hypotheses and edge cases as above. All nine proof steps are below 2000 characters; none conceals a long lemma. The current item statement is consistent with its source and is unchanged, so no statement dispute is opened.

## Unfinished work

The two new generic lemmas are intentionally unsplit stage-1 inputs. No Lean was written or compiled. The current unit realization remains the maintainer's existing two-step binding; historical ancestry is preserved rather than misrepresented as a new realization.
