# Stage-1 report: lem-sfb-almost-homogeneous-potential-smooth-cover

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-almost-homogeneous-potential-smooth-cover.json` — statement, split proof, and 10 steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-semitrait-potential-reduced-normalization.json` — new statement-only normalization node; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-equivariant-open-orbits.json` — new statement-only field orbit node; no Mathlib match.
- `citations.json` — verbatim statement quotations for every citation in every step.

## Attachments

None. A search of `lean/WeilConjectures/` found no declaration carrying the item tag or stating this result.

## WANTED

- WANTED: `literature/anantharaman-groupes-dimension-un.pdf`, Proposition 4.2.3 (OCR 4,2,5), printed pp.58–59 and Appendix II Corollaries 2–3, printed p.73, for `lem-sfb-almost-homogeneous-potential-smooth-cover` and `lem-sfb-semitrait-potential-reduced-normalization` (the local file is absent; the primary Numdam scan was read).
- WANTED: the same Anantharaman local archive, Proposition 4.2.3 geometric-orbit paragraph, for `lem-sfb-finite-equivariant-open-orbits` (the field argument was reconstructed from that paragraph and Milne Lemma 1.64, Propositions 1.65–1.66 in the local Milne PDF).

## What was checked and changed

The imported item has the hypotheses and conclusion of Anantharaman Proposition 4.2.3, including the fact that the normalized base is not asserted finite over the original base. Its proof was empty, so I retained its statement and supplied the proof route from the primary scan. The current blueprint has no node stating the item or either intermediate fact; `blueprint_refs.py search` for “normalization geometrically reduced” and “finite equivariant orbit” returned no match. The imported blueprint ancestry has a null nearest node and a long inherited `via` chain; I preserved it and recorded the exact paragraph used in each new node.

The first new node packages Appendix II Corollary 2 for a finite family of schemes, so one finite fraction-field extension works for both the group and scheme. It states only the generic geometric-normality hypothesis, finite normalization, flatness, separated finite type, geometrically reduced fibres, and generic isomorphism. It does not state the group law, action, smoothness, or orbit conclusion. The second packages the field-level comparison used after normalization: a finite surjective homomorphism of finite-type groups and a finite equivariant cover of an almost homogeneous target yield a smooth geometrically reduced source whose connected components are open neutral-component orbits. It does not assert any trait normalization or potential-extension result.

## Review by Q02

I read the item source in the Numdam scan, printed pages 58–59, and Appendix II printed page 73. The source first makes a finite purely inseparable generic extension and reduces the flat models, then applies Appendix II Corollaries 2 and 3, lifts the action to the normalizations, and identifies geometric orbits with connected components. I also read the local `milne-algebraic-groups_iAG2017.pdf` at Lemma 1.64 and Propositions 1.65–1.66. The local Anantharaman PDF named by the node is unavailable, so the proof origin is marked agent-written and the scan is recorded as WANTED.

Step 1 checks the finite purely inseparable reduction and the semilocal Dedekind normalization using the cited finite-component, integral-closure, and DVR statements. Step 2 checks flatness of reductions over DVRs, reducedness of the products, and factorization of all group and action maps through reductions; the cited flatness and reduction statements say exactly these things. Step 3 checks that reduction preserves field-valued points, obtains fppf transitivity by the cited Zariski lemma, and applies the new field-orbit node to the identity cover; it then uses the cited theorem that geometrically reduced finite-type groups are smooth and the cited smooth schemes are geometrically normal. Step 4 applies the new normalization node simultaneously and verifies that the new base is the integral closure of the original base, with the cited Dedekind closure and finite-presentation statements supplying the listed base properties.

Step 5 applies the existing trait normalization group-structure node on every localization at a maximal ideal, checks all of its hypotheses from Steps 2 and 4, and glues the unique laws with the cited morphism-gluing node. It uses the existing geometrically-reduced-group smoothness and smoothness-criterion nodes to obtain a smooth group. Step 6 uses the existing normalization-under-smooth-base-change node to lift the action canonically, then checks the action diagrams on the generic fibre and extends them using the cited separated-target density lemma. Step 7 applies the new field-orbit node fibrewise and invokes the cited smoothness criterion; its hypotheses are explicitly matched to Steps 4–6. Step 8 constructs the neutral open subgroup by gluing the existing trait-neutral-component subgroups, checks quasi-compactness and finite type with the cited Noetherian-open and composition nodes, and restricts the action.

The final two steps check the morphism clause separately. Step 9 uses reduction, finite normalization, integral base change, and integral composition exactly as stated by the cited nodes. Step 10 uses the existing finite-fibre statement for the normalized base, finite residue extensions, and the existing finite-map fibre statement; the remaining finite-dimensional tensor-algebra argument is written out as an elementary Artinian argument. Empty schemes and fibres are retained throughout. No excellence, commutativity, original smoothness, or module-finiteness was introduced.

## Not duplicates

- `lem-sfb-semitrait-potential-reduced-normalization` vs `lem-sfb-complete-trait-normalized-reduced-fibres`: the existing node gives a finite fraction-field extension and geometrically reduced normalized fibres over a complete DVR, without a generic-normality hypothesis; the new node assumes geometrically normal generic fibres but treats a semilocal Dedekind base without completeness and a finite family after one finite extension. Neither statement specializes to the other in the required application.
- `lem-sfb-semitrait-potential-reduced-normalization` vs `lem-sfb-raynaud-faltings-normalized-reduction`: the existing node is an affine complete-trait reduction result, whereas the new node is the finite-type semilocal normalization corollary with simultaneous extension and separated schemes.
- `lem-sfb-finite-equivariant-open-orbits` vs `lem-sfb-almost-homogeneous-potential-smooth-cover`: the new node is a field-level finite-equivariant-cover lemma and has no trait, normalization, or potential-extension conclusion; the item has all of those conclusions.
- `lem-sfb-finite-equivariant-open-orbits` vs `lem-sfb-smooth-group-relative-neutral-open`: the existing node constructs the relative neutral open subgroup over a DVR; the new node is a field-level assertion about a finite equivariant cover and its open orbits.

## What remains

The required server dry run passed at 7d8e9bab147. I corrected the duplicate comparison above after rereading the complete-trait node: it does provide finite extension and reduced fibres, but its completeness hypothesis prevents its application here. The final dry run will cover that correction. No Lean source or compiler was modified or run.

## Edge cases and field-lemma check

For the new normalization node I checked the empty family, empty schemes, the identity normalization of an already normal smooth generic-only model, and the need for a common extension: apply the source corollary once to a finite disjoint union, not by choosing unrelated extensions for the two models. The normalized base remains Noetherian by the cited Dedekind closure node, not by an assumed module-finite base change. No completion or henselization is inserted.

For the field node I checked a point with a finite geometrically reduced cover (the source becomes finite etale), a trivial connected group, disconnected finite groups, empty schemes, and nonaffine smooth groups. The geometric argument is as follows. After passing to an algebraically closed field, restrict to one open target orbit. For a point upstairs, its stabilizer maps into the stabilizer downstairs. The inverse image of the latter stabilizer has the same identity component as the upstairs stabilizer because its action on the finite fibre has a point stabilizer of finite index. Thus the upstairs orbit has the same dimension as the downstairs orbit. Every component upstairs dominates a target orbit, since the group acts equivariantly and the target orbit is transitive, and the finite map bounds its dimension by that orbit dimension. The locally closed orbit theorem and the strictly smaller dimensions in an orbit boundary then force every orbit to be closed and open, hence finitely many. The smooth locus on each reduced irreducible component over the algebraically closed field is nonempty; translations give smoothness on every orbit. Smoothness descends to the original field. The neutral connected group has connected orbits, so these are exactly the geometric connected components, and the same argument after every algebraically closed extension gives the required pointwise transitivity. This is the genuine orbit lemma isolated as the second new node; it is not silently used as an elementary step of the item.

I reviewed delivery-errors B–E against the written files: the two new statements are self-contained, the generic field extension is finite, all schemes used in the normalization and smooth-pullback nodes are locally Noetherian, and all group/action identities are identities of morphisms. Each citation's entire quoted statement was read and copied verbatim in citations.json; no definition-only node is asked to supply a theorem. Every non-elementary assembly ingredient is cited. No proof step exceeds 2000 characters, and no step simply restates the item's conclusion via a new node. All search records are copied from actual msearch output; the saved hits were read, and no successful search was repeated with the same question.
