## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-regular-separable-affine-smooth-neighbourhood.json`: split into four steps, unchanged statement; no exact Mathlib match. No new nodes, no Mathlib leaves.
- `citations.json`: nine verbatim statement quotations covering all step/node pairs.

## Attachments

None for the item. The related source declaration `Algebra.regularLocal_iff_smoothAtPrime`, `lean/WeilConjectures/RingTheory/RegularLocalSeparableResidueSmooth.lean:56`, only supplies the algebraic criterion already represented by `lem-weil-pbc-regular-local-separable-residue-smooth`; it does not state the full ambient affine-open conclusion. The item blueprint tag has no source-library hit. No Lean was written or compiled.

## WANTED

None for this split. All the sources used here are locally available Stacks sources. The inherited blueprint provenance mentions a wanted de Jong PDF, but this item is the isolated commutative algebra and affine geometry prerequisite; its argument needs no de Jong claim or SGA source.

## Audit findings and changes

The imported item was statement-only. Its statement is correct and stays unchanged. The existing 00TV node already supplies the substantial algebraic criterion; creating another regular/separable smoothness node would duplicate it. The existing principal-open section-localization result and affine smoothness comparison supply the geometry. I also found the more specialized `lem-trf-affine-smooth-prime-scheme-neighbourhood`, but used the basic existing statements so that the identification over the specified base is checked explicitly rather than inferred from a neighbourhood's existence.

I read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`. The current blueprint's (3) is the compactification/direct-image paragraph, whereas the inherited provenance records a prior alteration refinement and the parent's local regular-curve argument. The present split proves exactly that inherited local prerequisite and does not alter the unit's route. The ancestor command returns None: the item's inherited `blueprint.from.node` is already null. I preserved that protected provenance and its detailed place, and filled `same_as` with the empty search result. No new nodes need ancestry records.

Whole-DAG keyword and tag searches (00TV, 00TB, 01I3, 01V6, regular/separable, smooth/principal) located the reused statements. Whole-blueprint searches `regular separable`, `smooth affine`, `separable residue`, and `principal open` gave no equivalent imported statement. The hit on scheme conventions does not state this result. No duplicate node was created.

Mathlib searches were actually run with msearch.py: LeanFinder in two phrasings, Loogle, grep, and LeanSearch. All services answered for this run; Loogle had no matches. I read both semantic result lists, the grep hits, and Mathlib/RingTheory/Smooth/Locus.lean:150–157. `Algebra.IsSmoothAt.exists_notMem_smooth` assumes smoothness at the prime (and finite presentation), so does not by itself prove the item from regularity. The other hits already assume a smooth morphism, standard smoothness, or concern localization over its own original ring. They do not justify making this whole item a Mathlib leaf. Existing search records were retained; the new queries and their actual results were appended. No invented or unrun searches are recorded.

## Review by Q115

I checked B–E against the statement, proof, and open source files. There are no new nodes, so no unsplit proof, missing definition interface, duplicate, or clause-relabelling node is introduced. The proof has 2167 characters in total and no step near 2000 characters. Each genuine theorem used is an existing cited statement; sources in the step metadata identify where I read the argument, not substitutes for DAG citations.

Step 1 is a direct unfolding of the three cited definitions: separable algebraic extension, transcendence basis, and general separable extension. I read Fields `definition-separable` (09H1) and Algebra `definition-separable-field-extension` (030O). An intermediate field's elements have the same minimal polynomials over k because the base remains k, not the intermediate field. The empty family is algebraically independent because k injects into a field extension, and is a transcendence basis because every element is algebraic. Thus each finitely generated intermediate extension is separably generated. This is a small definitional argument, not an uncited permanence theorem about changing base fields.

For step 2 I read Algebra `lemma-separable-smooth` (00TV), including its hypotheses and the beginning of its cotangent-sequence proof, and `definition-smooth-at-prime` (00TB). I opened the full statement of `lem-weil-pbc-regular-local-separable-residue-smooth`: it allows any field and finite-type algebra, and only asks separability of the residue extension. Step 1 supplies precisely its general separability notion. Regularity is assumed at exactly S_q. I also opened `def-weil-pbc-singular-ideal`: its statement, not just its proof, defines smoothness at q by existence of the required g and smooth S_g. Thus this step uses no theorem about openness of the smooth locus, and does not assume finite presentation without justification.

For step 3 I read Schemes `lemma-standard-open-affine` (01I3), including the construction Spec(S_g) -> Spec(S) from the localization map, and the section-ring localization interface (01HV). The cited `lem-weil-pbc-affine-open-section-vanishing-prime` explicitly says both that the principal open corresponds to g not in the prime and that its section restriction is the localization S -> S_g. These give affineness of V and the canonical section-ring isomorphism. The cited `def-weil-affine-spectrum` states functoriality and uniqueness for morphisms of affine schemes, so the composite isomorphism to U corresponds to that localization map. Applying the same statement to the maps into Spec(k) verifies the base compatibility by composition of k -> S -> S_g. This does not identify arbitrary morphisms merely from their underlying point maps. The same g gives q in D(g) and hence x in V.

For step 4 I read Morphisms `lemma-smooth-characterize` (01V6) and More on Morphisms `lemma-smooth-formally-smooth` (02H6). I opened `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`: it specifically compares the ring notion with the project's locally finitely presented and formally smooth morphism notion, so no convention identification is silently assumed. I opened `lem-weil-pbc-smooth-restrict-open-subschemes`: clause (c) expressly transports smoothness across source and target isomorphisms. Apply it with e from step 3 and the identity on Spec(k). The commuting equality needed by (c) was established in step 3. The argument works for any g with S_g smooth, as the item's wording requires.

I checked small cases: S=k and q=(0) allow g=1 and V=U; a zero-dimensional finite separable field algebra is included; disconnected or nonreduced ambient schemes require no global regularity assumption, since only the chosen localization is used. The zero ring has no prime q, so that case is vacuous. Over an imperfect field a purely inseparable residue field is excluded by the explicit separability hypothesis, as required by 00TV. Neither normality, dimension one, integrality, perfection, separation of X, nor quasi-compactness of X is used. The result therefore retains the full strength of the statement.

The generic 00TV, principal-open localization, and affine smoothness comparison are reported in split_report.tool_uses as tools from other units; they do not replace the unit's geometric route. Every quoted citation was checked literally against the corresponding node statement. I corrected an initially mistyped 030O tag in the step metadata before validation.

## Unfinished work

None in the mathematical split. Delivery validation and push are performed with the mandated delivery command.
