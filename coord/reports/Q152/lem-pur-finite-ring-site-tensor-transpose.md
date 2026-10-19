# Q152: lem-pur-finite-ring-site-tensor-transpose

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-ring-site-tensor-transpose.json`: statement split into eleven steps; no Mathlib match for the item.
- `citations.json`: one verbatim statement quotation for each of the 23 step/node citations.
- `report.md`: this report. No new nodes and no Mathlib leaves were created.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` by the exact blueprint tag/id and by projection, compact support, comparison and transpose terminology. `ProEtale/Derived/LowerStarProjectionComparison.lean` proves a related proper-projection transport only for bounded-below input and tensor output; it does not state this item. Its generic `CategoryTheory/Adjunction/ProjectionMapMate.lean` supplies the same categorical calculation, but is not an attachment for this multi-clause unbounded item. The master checkout is not used as evidence of a finished proof.

## WANTED

None. All documents used are available in the repository. The new proof is marked agent-written: the blueprint asks for the arbitrary-finite-ring tensor formula but does not supply the complete unbounded site-comparison calculation.

## What needed correction

The item had no proof. Its proper comparison cited `lem-weil-pbc-comparison-direct-image-canonical-mate`, whose statement is only on the bounded-below derived category. I replaced this reference and statement dependency with `lem-sfb-unbounded-direct-image-comparison`, whose statement supplies the specific canonical mate on the whole unbounded category. The mathematical hypotheses, map, and three conclusions are unchanged. The old comparison is still the bounded-below specialization, not a second normalization.

The localizing comparison alone is not enough for assertion 1: it equates two localizing closures, not the entire etale derived category with one. Steps 2–3 explicitly supply the missing generation argument from the existing finite-ring etale compact generators and the existing telescope theorem. Similarly, the old restricted exceptional-adjoint-transfer node is not sufficient: it assumes a right adjoint on finite-Tor constructibles. Step 4 instead transports the ambient etale adjunction across the equivalences just proved and uses the existing uniqueness theorem.

No STATEMENT-DISPUTED is necessary: the item is mathematically valid as stated. The bounded-below citation was a reference mismatch, not a hypothesis to impose on the conclusion. The source's phrase defining the compact-support projection map is read as the usual factorization displayed explicitly in Step 9: first the proper projection map, then direct image of the open tensor identity.

## Searches and reuse

Read and retained `searches.jsonl` from the interrupted attempt. Its initial LeanFinder, LeanSearch, Loogle and grep queries concern this item, so they were not repeated. Ran a second phrasing and inspected its returned signatures: derived single-functor full faithfulness and scheme-etale forgetful full faithfulness do not state an etale/proetale derived equivalence; monoidal adjunction structure does not give the compact-support comparison. Grep finds the Mathlib proetale site definitions and elladic coefficient definitions, but no exceptional-adjoint/projection-comparison theorem. All recorded queries are the exact logged queries, with their actual results; no unavailable service was called a negative result.

Searched the whole DAG and blueprint for projection, projection maps, transposes, compact generators, the relevant declaration names, open tensor and unbounded comparison. Reused existing nodes throughout. In particular `lem-trf-open-tensor` supplies the proetale open identity, `lem-pur-etale-open-derived-tensor` its unbounded etale counterpart, and `lem-pur-etale-finite-ring-compact-generators` allows every finite ring here, not only a quotient of a valuation ring. No new-node duplicate pairs exist.

## Not duplicates

No new nodes.

## Review by Q152

I read the current `det-sp-finite-general-ring` proof in the 2026-10-15 blueprint, especially (2) for vector-bundle integration and (3) for the tensor formula. This item only makes the transport used there explicit; it does not replace the diagonal, deformation-to-the-normal-cone or vector-bundle route. I also read the current localizing-comparison proof, the current unbounded derived-unit and direct-image proofs, Stacks `derived.tex` Tag 09SN (`lemma-write-as-colimit`), `sites-cohomology.tex` Tag 07A4 (`lemma-pullback-tensor-product`) and Tag 0GL1 (`lemma-j-shriek-and-tensor`), and `sites-modules.tex` Tag 0E8I (`lemma-j-shriek-and-tensor`). I read Bhatt–Scholze Section 6.4 (Example 6.4.1, Lemmas 6.4.2, 6.4.5 and Proposition 6.4.8) in the local PDF. No SGA source is cited or used.

I opened and read the statement of every cited node. Here is the mathematical check of their uses, by step.

1. `lem-weil-pbc-finite-type-over-noetherian` gives Noetherianity of a finite-type scheme over a Noetherian scheme. A field has precisely the zero and unit ideals, so the base qualifies. The compactification is in the finite-type standing setting; the proper morphism and its schemes meet the hypotheses of the projection-formula and ambient-adjoint nodes.
2. `lem-pur-etale-finite-ring-compact-generators` gives both compactness and isomorphism detection for a set of finite-Tor constructible objects, for the arbitrary finite ring in the item. I checked that its scheme hypothesis does not require any extra separatedness. `def-pc-generators` defines the weak-generator notion used by `lem-pc-compact-generators-build-objects`; the step explicitly converts isomorphism detection to that notion before applying the latter theorem. The telescope triangle is built from sums and cones, hence is inside every localizing subcategory containing those generators. No generation assertion was taken just from a definition.
3. `lem-sfb-unbounded-site-comparison` states exactness, full faithfulness and preservation of sums for the full unbounded category. `det-ctf-finite-comparison-localizing` states the equivalence of closures and compact-support comparison, including the ordinary finite-discrete coefficient identification. `lem-sfb-unbounded-direct-image-comparison` explicitly defines its isomorphism as the counit mate for every unbounded complex. `lem-cbc-proetale-extension-zero-comparison` supplies the finite-ring sheaf comparison; the etale and proetale exact-extension nodes justify applying it degreewise without boundedness. These statements provide exactly what the step uses.
4. `thm-amb-etale-exceptional-adjoint` is on the whole ordinary etale derived category and applies to this Noetherian compactification. I wrote the four Hom bijections, so transport of the adjunction is explicit. `sk-prop-sf-existence` gives the adjunction on the same closures, not an ambient proetale adjunction. `det-sp-unique-right-adjoint` supplies the unique counit-compatible isomorphism. Applying it only after Step 3 avoids comparing functors on different domains. The counit has the required inverse beta direction.
5. `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` states the K-flat preservation and canonical bifunctorial comparison. Its Stacks construction computes the maps on total complexes. The step verifies composition, unit and symmetry directly on each pure-tensor summand, including the Koszul sign. No extra abstract coherence theorem is assumed.
6. The unbounded direct-image node supplies the actual counit normalization for both P and H, with no finite-window restriction. `def-weil-pbc-adjunction-mate` supplies the injective transpose bijection; `def-kun-projection-formula-map` defines the projection map as the counit-tensored adjunct. The displayed equations cancel the same b_P and b_P inverse. This is a routine calculation from these statements, not use of the bounded-below Lean result as if it were unbounded.
7. `lem-amb-proper-coproducts-projection` explicitly asserts invertibility for arbitrary unbounded etale inputs and arbitrary finite commutative rings, and explicitly identifies its tensor-order convention with the projection morphism and two symmetries. The step cancels those isomorphisms and uses the equality already proved in Step 6 to deduce the proetale result. No finite Tor amplitude, cyclic-ring flatness or cardinality-invertibility hypothesis is smuggled in.
8. The two open tensor nodes state natural isomorphisms on the unbounded categories in use. The canonical sheaf site comparison and `lem-weil-extension-by-zero-adjunction` let us compare the named maps by restricting their adjuncts. Both are the same tensor identity on the open; the total-complex argument then gives equality after derivation. I checked this does not rely on proetale geometric stalks detecting all maps. This uses the statements' canonical maps and exactness, not an unnamed construction buried in a cited proof.
9. I displayed the two-arrow compactification formula and pasted the proper and open squares. Naturality identifies their outside direct-image/open composite with the specific beta. All invertibility assertions here have already been supplied in Steps 7–8, so no new non-elementary fact is needed.
10. The exceptional-adjunction statement in `sk-prop-sf-existence` is exactly the Hom bijection used for injectivity. I calculated the adjunct using the counit equation of Step 4 and naturality of beta, then used the inverse projection square. The e factor has type from Rf_! of M to the unit sheaf, and the final unit constraint has target K, so the equation has exactly the target of assertion 3.
11. Symmetry is the explicit same signed swap on both sides, checked in Step 5. For the empty source all objects on X are zero, and for the zero coefficient ring every module is zero; the adjunction calculations remain defined and give unique maps. For f the identity all formulas reduce to the tensor/unit identities, another check on the directions of beta and rho. Finite non-principal rings such as F_l[x,y]/(x,y)^2 and non-flat maps from Z/l^n require no change: every cited finite-ring statement permits them and no step uses coefficient flatness.

I checked B–E of `coord/delivery-errors.md` against the files: there are no new unsplit nodes, no disguised clause nodes, no invented searches, no missing non-elementary lemmas, no cited proofs substituted for statements, and no dependency cycle back to the item through the reused generation/uniqueness/open-tensor lemmas. `citations.json` copies full node statements verbatim so the exact hypotheses and formulas remain visible. Every step is under 2,000 characters; the longest is the explicit open-tensor comparison calculation. The steps marked elementary are direct map/adjunction calculations or pasting of earlier steps, with their formulas written out. All off-unit statement tools are declared in `split_report.tool_uses` for independent maintainer review.

## What remains unfinished

No mathematical clause remains unproved at this split level. Required server preflight/dry-run and push are performed with the delivery tools; their final result is reported in the delivery response.
