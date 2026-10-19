# Q72: lem-trf-reduced-curve-normalization-genus

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-reduced-curve-normalization-genus.json`: statement, split into eleven proof steps; Mathlib searches found no match. Statement and statement dependencies retained verbatim. Existing Q29 searches and provenance retained, with the five actual Q72 searches appended.
- `citations.json`: thirty step/node entries, with quotations copied verbatim from the cited node statements.
- New DAG nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item is not its unit's key statement.

## Attachments

None. Searches by the exact blueprint id and by normalization/genus, arithmetic genus, reduced proper curve, and normalization quotient in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration proving every clause of this item. The normalization smoothness theorem in `AlgebraicGeometry/Regular.lean` covers a supporting fact only. `AlgebraicGeometry/Cohomology/EulerChar.lean` defines `Scheme.arithmeticGenus` as the dimension of first cohomology. This does not state this formula and is not the definition of p_a used here on a disconnected scheme. Upstream master is reference material, not attachment evidence.

## Literature wanted

WANTED: Michael Temkin, *Stable Modification of Relative Curves*, arXiv:0707.3953v3, Appendix B, Lemma B.1, printed p. 57, archival copy for lem-trf-reduced-curve-normalization-genus. I read the primary PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf (PDF page 57); I did not download or write literature into the shared repository. The proof's supporting sources are already present locally in the Stacks source tree.

## Problems found and changes made

The imported node had a correct statement but no proof. Its formula does not require connectedness or ordinary/nodal singularities. Temkin states his lemma with connectedness and geometrically reducedness over a separably closed field; over the algebraically closed field of this item, the same normalization-sequence calculation gives the stated Euler-characteristic formula without connectedness. I retained p_a=1-chi throughout, never replacing it by h^1 for a disconnected scheme.

The inherited `blueprint.from` records the historical semistable-exceptional-fibre argument below `lem-trf-local-term-locality`. The current main-20261015 sk-i-curve-zero unit instead uses the contracting-correspondence theorem; I read its unit and node proof and do not claim this genus calculation replaces or proves that theorem. I retained the maintainer-owned unit, chapter, and historical ancestry. This is a split of the already assigned supporting item along its specified normalization route, not a change of unit route. `tools/blueprint_refs.py ancestor` returned `lem-trf-local-term-locality`.

A possible C4 mistake was avoided: `lem-pc-chi-zero-dim-support` gives vanishing and chi=dim global sections, but does not assert that global sections are a sum of stalks. Step 6 proves that identification explicitly by extending representatives of germs by zero using sheaf gluing. Likewise, etale constant-coefficient finite-pushforward theorems are not used for the structure sheaf. The affine cohomology edge node explicitly concerns quasi-coherent structure modules and gives the requisite scalar-linear comparison.

## Searches and reuse

The sandbox initially contained only dispatcher brief markers, with no earlier split, report, or searches to resume. I copied the shared item and retained its statement, citations, provenance, and Q29 Mathlib-search records. The only changes are its proof, proof dependencies, proof origin, split status/report, and actual additional searches.

DAG and blueprint searches covered normalization, normalization exact sequence, genus, finite support, coherent pushforward, support closedness, and the Stacks tags 0C1R, 0AYT, 0BXR and 089W. Existing nodal nodes impose connectedness and nodality and cannot be used for this item. The reduced-algebraic-normalization node, normalization-properties node, coherent pushforward/quotient/support nodes, affine cohomology edge, and Euler nodes already state the required more general tools. There is therefore no new statement to create or search separately. Whole-blueprint searches found no equivalent full reduced disconnected normalization/genus statement; `same_as` is empty.

The five Q72 Mathlib searches are exactly those in `searches.jsonl`: LeanFinder in two formulations, LeanSearch, Loogle, and source grep. All services returned successfully. The first semantic search returned normalization instances and Weierstrass discriminant/reduction results; the second returned relative-normalization maps. LeanSearch also returned incidence-algebra Euler characteristics. Loogle returned relative normalization and integrality/reducedness. The source grep for normalization/genus, arithmeticGenus and deltaInvariant had no hits. I read the relevant Mathlib normalization definitions and instances; they provide none of the coherent-cohomology/genus formula. No match or one-line specialization was found. No service failure is mislabeled as absence.

## Not duplicates

No new nodes are created. Existing `lem-trf-nodal-curve-normalization-euler` and `lem-trf-nodal-normalization-quotient` are restricted to connected nodal curves; they are not the general item and are not used to infer it. The supporting results are all reused under their existing ids.

## Review by Q72

I read the item, its chapter and unit, the current blueprint locality proof, and Temkin's Appendix B Lemma B.1 online. I also read the local Stacks statements/proofs for varieties Tags 0BXR (normalization of algebraic schemes), 0C1R (normalization exact sequence and delta quotient), 0AYT (zero-dimensional coherent support), and 08AA (Euler additivity); coherent Tags 089W, 01Y6, 01Y0; morphisms Tags 01T6, 035L, 01W5 and 056J; and cohomology Tag 02UZ. For each dependency I opened its JSON statement, rather than borrowing a conclusion from its proof. There are no new-node sources to certify.

1. Step 1 uses `lem-weil-pbc-finite-type-over-noetherian` for Noetherianity and `lem-weil-pbc-reduced-algebraic-normalization-field-change` for the finite family, finite surjective normalization, and dense normal isomorphism locus. X is reduced and finite type because it is proper. No field-change assertion is used.
2. Step 2 uses the integral-scheme equivalence for the reduced irreducible components, the closed-immersion properness node for their properness, and normalization-properties (a),(c) for properness, dimension and smoothness. All components have dimension exactly one, not zero, by the pure-dimension hypothesis. Algebraic closedness supplies perfectness. For integrality of each normalized component, the normalization-in-residue-field-extension node applies with the generic point and the trivial finite extension of its residue field; its construction is the same integral closure as def-sc-normalization. This gives nonemptiness and connectedness, not merely smoothness.
3. Step 3 is an explicit elementary argument for injectivity using the integral-closure construction, reduced-induced closed-subscheme ideal and reducedness. A section vanishing on every normalized component vanishes in every residue field; its membership in the radical-zero ideal then forces it to be zero. Exactness at the quotient is its definition. I did not assume injectivity from finiteness or topological surjectivity alone.
4. Step 4 uses coherent finite pushforward and coherent cokernels under the locally Noetherian hypothesis established in step 1; its closed-support citation explicitly states closedness for a finite-type quasi-coherent module. These statements give exactly the properties used.
5. Step 5 uses the normal isomorphism locus from the same reduced-normalization statement, and `lem-sc-dim0-finite` for a closed zero-dimensional subset of a finite-type scheme. The argument excluding a positive-dimensional closed support is written out. No nonsmooth-point finiteness is assumed without this argument.
6. Step 6 has no external dependency: the sheaf axiom extends a representative of a single germ across the open complement of that closed point, since the overlap has zero sheaf. Injectivity is checked on germs, and the finite sum handles all support points. This proves precisely the missing stalk/global-sections identification of Stacks 0AYT(2) in a few lines, so it is a proof step rather than a new node.
7. Step 7 uses the zero-support cohomology statement for vanishing and chi=dim Gamma, and the proper coherent cohomology finiteness statement to justify finite dimensions. Step 6 then gives the sum of stalk dimensions. The stalk F_y itself is used, not its residue-field fibre; the two dimensions need not agree.
8. Step 8 checks Noetherianity and dimension one for each proper normalized component before applying the general dimension vanishing theorem. The global-functions statement applies because these curves are nonempty, connected, proper and reduced; it gives dimension one in degree zero. The genus and Euler definitions supply the remaining numerical terms.
9. Step 9 uses the finite-morphism definition to show a closed immersion is finite (the quotient algebra is cyclic), the finite-composition statement to obtain each h_i finite, and coherent finite pushforward for G_i. The direct-sum description of B is sectionwise sheaf gluing on the finite disjoint union; it does not invoke an unproved cohomology decomposition.
10. Step 10 uses the affine cohomology edge statement for the affine finite h_i. Its isomorphism is linear over the base's global functions and hence over k, so dimensions agree. Euler additivity and coherent finite sums give chi of B. This is why no new disjoint-union cohomology comparison lemma is needed.
11. Step 11 applies Euler additivity only to the coherent exact sequence already proved. The final substitution and subtraction from one give the complete statement.

I checked delivery-errors B through E: statements retain their introduced objects and all hypotheses; there are no new unsplit nodes with hidden proofs, fabricated search records, new duplicate tags, moved clauses, cycles, or uncited non-elementary geometric/cohomological inputs. Generic off-unit statements are declared as tools in `split_report.tool_uses`, with why the present unit supplies none. All citations have verbatim quotations; their proof-dependency union is exact. No step is over 2000 characters (maximum 964). No nontrivial comparison or lemma is hidden in a long step.

Small cases: a smooth connected curve has F=0, v=1 and p_a=g; two disjoint projective lines have F=0, v=2 and p_a=-1, confirming why h^1 cannot replace 1-chi; a cuspidal rational cubic has v=1, g=0 and local quotient k[[t]]/k[[t^2,t^3]] of dimension one, giving p_a=1; the normalization quotient at a rational node is one-dimensional, giving the same value for a rational nodal cubic. For empty support the germs identification and sum are both zero. The empty X is excluded by the item, while all arguments would still make the Euler convention consistent.

## Unfinished work

None within this one-level stage-1 split. Existing supporting nodes retain their own statuses and are not split or edited here. No Lean code or build/compiler command was run.
