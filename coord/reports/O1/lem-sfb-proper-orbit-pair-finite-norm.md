# O1 stage-1 report: lem-sfb-proper-orbit-pair-finite-norm

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-orbit-pair-finite-norm.json — statement, now split into seven proof steps; no exact Mathlib match.
- citations.json — one verbatim statement quotation for every step/node citation, numbered from 1.
- report.md — this report. searches.jsonl contains the actual search-command records; write_split.py is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. The existing DAG contains all needed general inputs; none was relabelled as a new clause of the item.

## Attachments

None. Searched lean/WeilConjectures for the exact item id and for norm-section, orbit-pair, pencil and related notions. No declaration there states the whole assertion. Existing projective-space and coordinate-cover descent declarations cover other constructions, and are not an attachment of this item.

## WANTED

None for this split. Its argument is written from the available Stacks sources. The inherited de Jong reference identifies the ancestor's intended geometric use; this proof does not require an unavailable PDF or invoke a quotient theorem.

## Audit of the inherited item and blueprint

The statement and all ten statement dependencies are unchanged. There is no STATEMENT-DISPUTED issue. The imported node had no proof; this delivery supplies the argument rather than applying a renamed copy of its conclusion. The nearest-blueprint-ancestor command returns None, so its existing null from.node and twelve-element via chain are retained, with the already precise original-steps-7--10 place. Whole-blueprint searches for “norm pencil”, “finite invariant norm”, “orbit separated pair”, “orbit-separated”, and “affine nonvanishing” found no equivalent imported blueprint statement; same_as is []. No new definition, chapter, unit or route was introduced.

Read the chapter and unit JSON, then the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability.proof.md. The latest unit treats preservation by the six functors, with direct-image preservation on the existing route. This node remains a generic local geometric input under that route, in the inherited quotient-free norm-pencil construction. The difference between the current unit prose and the archived unit record requires no change to this geometric lemma. Off-unit geometric tools that are neither Mathlib nor recorded closed are declared individually in split_report.tool_uses; no maintainer-owned tool_uses field is set.

## Mathlib searches

Retained the five inherited 2026-10-22 searches, and appended only actual 2026-10-23 msearch.py queries from this sandbox's log. Ran LeanFinder twice with distinct phrasings, LeanSearch, Loogle with IsFinite and Proj, and grep twice. Read the returned hits. The first LeanFinder returned structure-sheaf denominator and limit lemmas, not norm pencils. The second returned affine-space coordinate evaluation, Proj.mul_apply, Hilbert90.aux, Proj localization and global-section morphism lemmas, and finite-group representation statements. LeanSearch returned finite/proper and tensor-invertible ingredients, not the combined result. Loogle returned no hits. The targeted grep found Proj.fromOfGlobalSections at Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:443; read its signature and construction at lines 410--465. Its input is a graded-ring map to global functions with irrelevant ideal mapped to the unit ideal; it does not construct the present invertible-bundle orbit norm or assert the required invariance or finiteness. Thus it is no one-line specialization proving this item. No search failure was recorded as absence.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Reused the existing tensor/pullback, nonvanishing, generating-sections, projective-chart, affine-locality and proper/affine-finite nodes. The stronger-looking effective-action norm-pencil lemma assumes an integral generic setting and includes additional assertions; applying it here would introduce hypotheses the present item does not have. Instead the proof carries the explicit finite permutation calculation using general tensor statements.

## Review by O1

I read Stacks constructions.tex Tag 01NE (lemma-projective-space), the relative construction after Definition 01NF, Tag 01NG (lemma-standard-covering-projective-space) and Tag 01NH (lemma-projective-space-separated). For the sheaf operations I read modules.tex Tag 01CA (section-tensor-product), Tag 01CB (lemma-stalk-tensor-product), Tag 01CD (lemma-tensor-product-pullback), Tag 0B8L (lemma-pullback-invertible), Tag 01CT (lemma-constructions-invertible), and Tag 01CY (lemma-s-open). For the geometric criteria I read properties.tex Tag 01PV (lemma-affine-cap-s-open), morphisms.tex Tag 01S8 (lemma-characterize-affine), Tag 01W6 (lemma-image-proper-scheme-closed, clause 2) and Tag 01WN (lemma-finite-proper). I opened every cited node and read its statement, rather than using an argument hidden in a cited proof.

Step 1 uses precisely clauses (1) of lem-weil-pbc-invertible-pullback-tensor, the equivalence in lem-sc-nonvanishing-tensor-pullback, and BOTH clauses of lem-sc-tensor-section-affine-open. The latter explicitly gives tensor nonvanishing as the intersection and affineness when one factor's nonvanishing open is affine. The identity index supplies exactly that factor. I checked that this avoids the false general claim that intersections of affine opens are affine on arbitrary schemes; no separatedness lemma is silently substituted. Each pullback is along an automorphism of Y, and all modules in this step are invertible as required. Complementing the proved equalities gives exactly the two stated zero unions.

Step 2 uses lem-weil-pbc-invertible-generating-sections-fibre, whose statement includes the residue-value formulation and the equivalence with generating the sheaf, not just a definition of generation. The disjoint unions give disjoint norm zero sets; inclusion of the identity translate gives disjoint original zero sets. The two line bundles M and C meet the invertibility hypothesis. Applying the criterion twice gives every generation clause without an unstated Nakayama invocation.

Step 3 uses def-weil-pbc-morphism-to-projective-space-by-sections only for the relative morphism it actually defines and its structure-map property. It uses lem-weil-pbc-projective-morphism-chart-preimage clause (i) for the exact open preimages. This is a theorem citation rather than an attempted derivation of chart identities from a definition. Restricting the same structure sheaf to equal opens explains the equality as open subschemes.

Step 4 uses lem-weil-pbc-projective-space-standard-charts clauses (a) and (c), which explicitly say the standard charts cover and are affine over an affine base. Spec F is the needed affine base. It then applies the existing Mathlib leaf pqf-lem-affine-local-target: the inverse images of this target affine cover, already shown affine in steps 1 and 3, imply each map is affine. There is no assumption that either coordinate map is surjective.

Step 5 uses lemma-nagata-projective-space-base-change-proper with the finite coordinate set of size two; its statement is about the same relative projective space used here. I read its current blueprint statement under literature/blueprint/latest as well as the DAG node. Properness implies separatedness by def-weil-proper-morphism. The two structure triangles commute because step 3 constructs F-morphisms. Therefore lem-weil-pbc-proper-over-separated applies with base Spec F, source Y and target projective line. It says the two maps are proper. The same-unit Mathlib leaf lem-sfb-affine-proper-finite then applies to their affine and proper morphism properties, proving finiteness. No missing dimension or finite-type hypothesis is imported: the cited proper-to-separated theorem has exactly the hypotheses in force, and properness itself includes finite type.

Step 6 uses clause (2) of lem-weil-pbc-invertible-pullback-tensor for section-compatible tensor pullback and composition, and the explicit permutation formula in lem-weil-pbc-module-tensor-symmetric-monoidal for the actual canonical isomorphism and its value on tensor sections. With the left action convention g∘h=gh, h* g* identifies with (gh)*, and the position g is sent to gh. The inverse permutation is multiplication by h inverse. Substituting c=a and c=b into these actual formulas gives the two exact section equalities. This is a short finite-index calculation from cited isomorphisms, not a new norm-linearization theorem disguised in the step; the item does not require a cocycle assertion, and none is used. No action faithfulness or characteristic restriction enters.

Step 7 uses BOTH the pullback compatibility and the equivalent-pairs assertions that are explicitly present in lem-weil-pbc-projective-space-functor-of-points. These prove equality of the projective-space-over-Z components. Since h is an F-automorphism, the components in Spec F also agree; the uniqueness clause explicitly written in def-weil-pbc-morphism-to-projective-space-by-sections gives equality of the full maps over F. Thus the last conclusion is equality of scheme morphisms, not merely equality on residue points, which would fail as a criterion on nonreduced schemes.

For B--E I checked the unchanged statement is self-contained with every notion defined inline or among its statement dependencies, every cited id exists and is unmerged, proof_deps equals the union of uses, every citation quotation is literally the cited statement, and each source label is the one read. There are no statement-only new nodes, no new Mathlib leaf with an unchecked signature, and no possible new-node cycle. No step exceeds 2000 characters (the longest is under 900), and no non-elementary helper is hidden in long prose. The proof is marked agent-origin because it assembles the norm argument from the cited source lemmas rather than attributing this exact combined statement to Stacks.

Edge cases checked: if Y is empty, generation and the equalities are vacuous and the same affine/proper criterion gives finite maps. For the trivial group the construction reduces to the ordinary pencil. A nonfaithful action merely repeats factors, so the right permutation still works. Characteristic dividing |G| causes no problem because no averaging or division is used. Nonreduced schemes cause no problem: nonvanishing and generation are the cited residue-fibre criteria, and invariance is obtained from representability, not pointwise equality. A zero section is allowed; disjointness then forces the other to be everywhere nonvanishing, and the hypotheses give the affine chart needed for the argument. A general high-dimensional proper scheme is not silently assumed to admit such a pair; the given affine pair is precisely what makes the affine chart argument work. I found no statement correction necessary.

## Unfinished work

None in the requested stage-1 split. No Lean was written, compiled or built; the shared repository and launcher files were only read. This delivery supplies no new claims that need a separate worker split.
