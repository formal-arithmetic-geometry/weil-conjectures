# Stage-1 worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-noetherian-fibre-ample-neighbourhood.json`: item, statement, split into nine proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-ample-fibre-section-lifting.json`: new statement-only node, unsplit; no Mathlib match. This is the degree-zero local-lifting consequence of Stacks 0D2M, not an ampleness-neighbourhood theorem.
- `citations.json`: every proof-step citation, with the cited statement copied verbatim.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source for the blueprint tag, fibre/fiber ampleness, neighbourhood spellings, and the relevant module/cohomology/projective-space files. There is no declaration stating the item's proper-family neighbourhood result. The upstream master was searched for the item and wording as reference only. The available field-based ampleness declarations are not this theorem. No Lean was written or compiled.

## WANTED

None. The sources used are in the repository.

## Findings and changes

The imported item had no proof and was correctly stated. Its Noetherian hypothesis and its absolute conclusion over an affine neighbourhood are retained verbatim. I expanded Stacks 0D2N (`coherent.tex`, `lemma-ample-in-neighbourhood`, lines 6090–6158). The substantive cohomological input is the final assertion of 0D2M (`lemma-ample-on-fibre`, lines 5977–6087). I isolated precisely its locally liftable section consequence, leaving the formal-functions proof to that new statement-only node's own future split.

The source asks for a sufficiently large very ample exponent, while the existing immersion node promises some exponent. Step 2 first applies that node to the ample N-th power, with N at least d_0, so the resulting exponent Na is large enough. It does not pretend that the existing node promises all large exponents. The two proper-image shrinkings are explicit. At the end I use the definition of ampleness directly: a finite map has affine preimages of the affine standard charts, and these preimages are the nonvanishing opens of sections of L^d. Thus positive-power descent and a separate finite-pullback ampleness theorem are not hidden inputs.

I read the chapter and unit records, all three blueprint levels in SETUP, the current `main-20261015` ancestor text, the imported item's ancestry, and the general parent split. This is the Noetherian input beneath the already established arbitrary-base approximation argument. No chapter or unit step changes. Generic off-unit tools are declared in `split_report.tool_uses`; the delivery does not set the maintainer-owned `tool_uses` field.

## Search record

Before writing the new node I searched the whole DAG by `0D2M`, `lemma-ample-on-fibre`, lifting/fibre-section wording, and the proposed id, and ran `tools/blueprint_refs.py search` for `0D2M`, `fibre section`, and `lifting sections`. None states this local lifting theorem. The broader blueprint search for `ample` was also read: the curve, degree, tensor, and field-extension lemmas have different conclusions. The ancestor command returns `lem-trf-local-term-locality`; the child's via list prepends this item to its existing ancestry.

All Mathlib searches for the delivery used msearch.py and are preserved in searches.jsonl. I read the hits: the first semantic phrasing returned structure-sheaf localization and denominator-clearing results, not fibre-section lifting for line bundles; the second returned SurjectiveOnStalks, sheafification and stalkToFiber surjectivity, not the cohomological base-change map in 0D2M. Loogle found no IsProper/IsAmple combination. The unanchored grep hit only `example`/`examples`; the word-boundary grep for IsAmple/ample/ampleness in Mathlib/AlgebraicGeometry found no hits. The item's own semantic queries likewise returned morphism-locality, affine-neighbourhood and Noetherianity declarations. The record distinguishes these actual outputs from a theorem match and retains the item's earlier searches.

## Not duplicates

- lem-trf-ample-fibre-section-lifting vs lem-trf-noetherian-fibre-ample-neighbourhood: the new statement supplies lifts of individual high-degree fibre sections; it asserts no ampleness or projectivity on a neighbourhood. Steps 2–9 still construct and analyze the projective-space morphism and both shrinkings.
- lem-trf-ample-fibre-section-lifting vs lem-trf-ample-neighbourhood: the latter is the arbitrary-base relative-ampleness conclusion, proved by approximation using this item; it cannot supply the cohomological lifting input without a cycle.
- lem-trf-ample-fibre-section-lifting vs lem-weil-pbc-ample-finite-common-power-cover: that existing node finds sections and affine opens on a scheme already carrying an ample line bundle; it does not extend sections from a fibre to the total space.

The new node's source tag 0D2M is not a source tag of an existing node. I reused `lem-trf-proper-finite-fibre-finite-near` (02UP, no Noetherian restriction) instead of adding a second 02OH node; the other existing 02OH node is weaker than this already available theorem. I reused the projective-space quotient geometry and section/chart interfaces rather than adding any construction, comparison or elementary shrinking node.

## Unfinished work

None in this one-level split. The new cohomological lifting node is intentionally statement-only and unsplit, as required.

## Review by Q22

I reviewed delivery-errors B–E with the statements and the local Stacks files open. I read all of 0D2N and the statement and proof of 0D2M, including the formal-functions and Nakayama ending and the degree-zero surjectivity. In 0D2M I specialize F to O_Z, which is coherent because a proper scheme over a Noetherian scheme is Noetherian; the source imposes no flatness of f or of L over the base. A preimage of a fibre section in the direct-image stalk is represented on some base neighbourhood, exactly the existence statement of the child. The child introduces every object and uses the existing definitions of Noetherian schemes, invertible modules, tensor powers, fibre and pullback. It carries no proof, proof dependencies, proof sketch, or hollow data.

For step 1 I checked the homeomorphism clause of `def-pc-scheme-fibre`, the closed-map clause of `def-weil-proper-morphism`, the two explicit conditions of the ampleness definition, and the arbitrary-base-change statement of `lem-weil-pbc-proper-base-change`. The empty fibre really yields an empty inverse image over an affine neighbourhood; it is not silently discarded.

For step 2 the new node supplies a uniform d_0 for all sections at each d. The positive-power node applies with N positive. The affine-base immersion node is applicable because the fibre is proper and hence locally finite type over a field, and its conclusion supplies both the immersion and the twisting isomorphism. The projective-bundle quotient-geometry statement explicitly identifies its free-sheaf case and twist with polynomial Proj over an affine base. This provides the projective-space model used here. Step 3 uses that same node's separatedness and quotient correspondence, the actual proper-to-separated theorem (a Mathlib leaf), and the proper-immersion-closed theorem (also a Mathlib leaf). None of these is merely a definition substituted for the claimed result. The coordinate sections are the images of the basis under its stated universal quotient.

For step 4 each t_j is lifted separately using the child's quantifiers and d >= d_0; there are only r+1 neighbourhoods to intersect. The invertible-pullback-tensor node states the tensor isomorphism, its compatibility with sections, and the residue-field formula, which justify the fibre restriction used here. Step 5 uses the actual openness/trivialization statement of the nonvanishing node and the equivalence between generation and covering by nonvanishing loci. The field extension in the residue-value formula is faithful, so the lifts have no common zero at any point of the fibre. The closed bad locus is removed using properness; no flatness, geometric-fibre hypothesis, or assumption that s is closed is introduced.

In step 6 I checked the quotient-geometry node's arbitrary-base-change naturality, not merely a definition of projective bundles. Equality of the fibre map with i_s follows because their quotient sections are the same t_j. The proper-to-separated statement applies to the triangle over U_1, with the source proper by open base change and the projective-space target separated. Step 7 applies the finite-neighbourhood theorem to phi at every point of the projective-space fibre, not to f at s. The homeomorphism in the scheme-fibre statement and injectivity in the closed-immersion definition give finite topological fibres of phi at these points, including the empty ones outside the image. I opened and checked 02UP in `more-morphisms.tex`, lines 12594–12622, as the more general version of 02OH cited by 0D2N. The finite-locality node says exactly that finiteness can be checked on an arbitrary target open cover; it allows the union of the W_p.

In step 8 the proper projective-space statement supplies the closed image of the complement of W. The complement's image misses s because W contains the whole fibre, and the chosen V is affine inside its open complement. Restriction to smaller opens preserves the finite condition on affine inverse images; the target-cover criterion gives finiteness over P_V. In step 9 I read the statements of the section-defined morphism, its standard-chart preimage theorem, and the standard-chart geometry theorem. They concern the same base-change projective-space convention, and the quotient theorem identifies the morphism and the pulled-back twist. The chart theorem explicitly makes standard charts affine when the base open is affine. A finite morphism is affine by its definition. Proper base change and the proper-basic node supply quasi-compactness over the affine V. Hence the positive-degree sections themselves satisfy the absolute ampleness definition; no unquoted reverse implication about tensor powers is needed.

I tested the child on the identity morphism (a fibre scalar lifts to the local ring and hence some neighbourhood), the empty total space (only the zero section), and a family with an empty fibre. I checked that non-flat or nilpotent bases are not excluded: the source's formal-functions argument has precisely these hypotheses. I tested the item's shrinking argument on an empty fibre, a zero-dimensional fibre, a nonclosed base point, and projective dimension r=0. In each case the proper-image argument and the finite-neighbourhood theorem apply. The high-exponent choice includes d_0=0 and always gives d>0. I found no false imported statement and made no statement correction.

The split has no new elementary or duplicate node: finite intersections, affine-neighbourhood choices, set complements, multiplication of positive exponents and the final definition check stay in the proof. All steps are below 2000 characters. citations.json contains verbatim cited statements for all nine steps. The only new theorem is the substantive 0D2M consequence; none is a renamed clause of 0D2N. No SGA source is used.
