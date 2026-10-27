# Q31 stage-1 report: lem-sfb-fundamental-flag-boundary-sections

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fundamental-flag-boundary-sections.json: statement, split; preserved its statement, source, statement dependencies, and inherited metadata; added a four-step proof and actual new searches alongside the inherited searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-opposite-schubert-picard-basis.json: statement, unsplit; opposite Schubert prime Cartier divisors, translated boundary components, and classification of every line bundle by degrees on simple Schubert curves; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-line-schubert-curve-degree.json: statement, unsplit; the rank-one orbit isomorphism and restriction of arbitrary character line bundles to projective-line twists; no Mathlib match.
- citations.json: one verbatim statement quotation for every proof-step citation.
- searches.jsonl: actual msearch.py log, with raw search outputs retained in the corresponding .search-results.json files. report.md: this report.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by Schubert, Bruhat, homogeneous line, and fundamental weight. No project declaration states this item; no attachment is claimed from a sorry declaration or from Mathlib. The corresponding search of lean/Sheaf likewise gives no relevant declaration.

## WANTED

WANTED: Brion--Kumar, Frobenius Splitting Methods in Geometry and Representation Theory (2005), local PDF, section 2.1 pp.62--63 and Exercises 2.2.E(2)--(3) pp.70--71, for lem-sfb-fundamental-flag-boundary-sections and both new nodes. The author-hosted primary PDF at https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf was read online, including the definitions of roots and associated bundles and the exercise heading allowing characteristic zero. The new nodes' source.document records a wanted local path, not an existing file. Nothing was downloaded into the repository.

WANTED: Iversen (1976), Theorem 5.3, for the original source chain recalled in Milne Remark 22.49. This delivery uses Milne's printed formula as corroboration, and explicitly separates the geometric Picard and rank-one inputs rather than assuming that the remark alone identifies supports.

## Corrections and limitations

The live item has empty proof and status unsplit; no earlier split, report, or searches.jsonl was present in this sandbox. The inherited Mathlib searches dated 2026-10-23 were read and retained; the newly added searches address the refined input statements. There is no statement dispute and no change in the item statement or its quotient sign convention. No index matching with a preassigned boundary ordering is required.

The inherited blueprint ancestry has from.node = null. tools/blueprint_refs.py ancestor confirms None; all new from.via chains prepend the item to the inherited chain. Its exact inherited place is retained and extended. Whole-blueprint searches for Bruhat, Schubert, coroot, Picard and homogeneous line-bundle notions found no node stating either new input. The newest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images proof (3) were read: they give the compactification context, and this remains a lower auxiliary for the inherited strict-dominant ampleness route. The item is not the unit's key node; no unit file is changed. The historical coord/dag-sync.md mentioned by the standing brief is absent; the current direct-delivery brief and newest blueprint were used.

The proof_origin is agent: the assembly, local Cartier computation and translation are written here; the detailed Brion--Kumar inputs are available online but their local document is wanted. The two new nodes are intentionally statement-only, not purportedly proved in this delivery. Nothing else remains unfinished for this one-level split.

## Not duplicates

lem-sfb-opposite-schubert-picard-basis vs lem-sfb-bruhat-longest-cell-charts: the existing node gives the strata and affine charts, but no closure relations, codimension-one boundary description, Cartier boundary divisors, Schubert curves or degree-dual Picard classification.

lem-sfb-opposite-schubert-picard-basis vs lem-sfb-fundamental-flag-boundary-sections: the new node is a geometric/Picard assertion for every invertible sheaf, with no characters or global sections identified. It cannot produce the item's sections without the independent rank-one restriction calculation, comparison of classes, local section construction and homogeneous translation carried out in the item.

lem-sfb-opposite-schubert-picard-basis vs lem-sfb-double-flag-invariant-boundary: the existing node constructs an invariant rho section on Q x Q and its opposite orbit; it does not classify line bundles by Schubert-curve degrees or describe individual opposite prime divisors on Q.

lem-sfb-opposite-schubert-picard-basis vs lem-sfb-strict-dominant-flag-line-ample: the existing node proves ampleness and uses this item as input. It gives no independent Picard classification; citing its proof would be circular.

lem-sfb-homogeneous-line-schubert-curve-degree vs lem-sfb-reductive-rank-one-reflections: that node constructs the root homomorphism and reflection/coroot identities, but does not identify its orbit map with a Schubert curve or restrict homogeneous line bundles to twists.

lem-sfb-homogeneous-line-schubert-curve-degree vs lem-sfb-homogeneous-line-bundle-sections: the existing node constructs the bundle and identifies sections with semi-invariant functions. It does not give the restriction isomorphism on the projective-line orbit or compute degrees.

lem-sfb-homogeneous-line-schubert-curve-degree vs lem-sfb-simply-connected-character-lattice: integrality and duality of the fundamental characters do not identify flag curves or calculate associated line-bundle degrees.

Both new ids were absent from the whole DAG before writing. Searches of all DAG statements for Schubert, coroot degree, flag Picard classification, Milne 22.49 and associated-line restriction found no duplicate. No Stacks tag is assigned to these group-theoretic inputs: their source is Brion--Kumar and Milne. The existing divisor definition and canonical-zero-scheme lemma were opened and reused at the definition/local-calculation level; no new node was created for the elementary canonical-section calculation.

## Review by Q31

I read the item, its inherited parent strict-dominant ampleness proof, the chapter and unit records, the newest blueprint unit and direct-image proof, and delivery-errors B--E. I read Milne iAG2017 Theorem 22.48 and Remark 22.49 at printed pp.479--480, and the rank-one homomorphism construction in Theorem 21.11(b),(e) and paragraph 21.24, pp.429--430,432. I corrected the new rank-one node's initially broad section reference to these exact places before the final dry run. The remark computes line-bundle classes, not individual section supports on its own. I therefore opened Brion--Kumar section 2.1 pp.62--63 and Exercises 2.2.E(2)--(3) pp.70--71 in the primary online PDF. Its positive roots are those of Lie(B), exactly as here; its L(lambda) is G x^B k_(-lambda), matching the item's action with +lambda on the quotient coordinate. The exercise heading states that the characteristic may be zero. No Frobenius splitting theorem or SGA result enters this argument.

For step 1 I read the entire statement of the new opposite-Schubert node: it expressly supplies E_i, the curves R_j, the degree isomorphism, its values on O(E_i), and the boundary components n_0 E_i. This is precisely the input used, rather than an appeal to the affine-chart node for closure or Picard information that it does not state. Hypotheses are the same algebraically closed field, semisimple simply connected group and Borel pair. The Cartier assertion is essential for step 3 and is explicit in the new statement. The standard justification to be split below that node is smoothness of Q, closure/purity of Schubert strata, and the opposite-divisor intersections dual to the simple curves; the Picard classification is the general assertion in Exercise (2), not a disguised existence-of-sections assertion.

For step 2 I opened lem-sfb-simply-connected-character-lattice: it states that the fundamental weights are actual torus characters in every characteristic and have the exact delta pairings. I opened the full rank-one degree statement: it gives the orbit isomorphism and degree with the same quotient sign, for every character, including negative ones. I compared the two degree vectors and used the injectivity explicitly stated by the opposite-Schubert node. The conclusion at this step is only an isomorphism of invertible sheaves; the existence and supports of sections are still proved in the next step. To split the rank-one node later, restrict the character along diag(t,t^-1), identify the SL2 quotient by first columns, and compare the associated fibre of character -m with the m-th power of the dual tautological line. The orbit-identification assertion is genuine additional algebraic-group geometry, so it is not being treated as a one-line elementary node.

For step 3 I opened def-pc-divisor-line-bundle and read its definition as the dual ideal, then read Stacks divisors.tex Definition 01WX and Lemma 01X0 (their labels are given in the step). I do not take the canonical section from a definition that does not state it: the inclusion of the ideal is written as a section of its dual, and the calculation t = f e proves its residue-field zero locus directly. I also opened lem-sfb-homogeneous-line-bundle-sections: it expressly gives a G-homogeneous line bundle and its natural left action. The formula s_i(x) = n_0 phi_i(t_i(n_0^-1 x)) is a global section because these are line-bundle isomorphisms covering translations. The zero-locus equality follows from fibre isomorphisms and the written local computation. No theorem about flatness, codimension or descent is hidden in this elementary step.

Step 4 only assembles the preceding equalities, distinctness and irreducibility, and observes that a section with nonzero fibre on the nonempty cell cannot be zero. It does not infer that a nonzero section vanishes nowhere. In the trivial-group case the first input already states that the boundary is empty, so no assertion about a nonexistent fundamental character is made. Every proof citation has a verbatim quotation in citations.json; step 1 quotes the whole relevant new statement so both its Picard and boundary clauses are covered. No step exceeds 2000 characters.

I tested SL2 with upper triangular B: Q is the projective line, R_1 is all of Q, E_1 is the opposite fixed point, M_(omega_1) is O(1), and translating its canonical section by n_0 gives a section vanishing at the B-fixed point, the complement of U n_0 B/B. The check works in characteristic 2 as a character calculation, without differentiating characters. For SL2 x SL2 the two opposite divisors and curve degrees give the two coordinate basis vectors, and their translates are the two boundary components. For SL3, the longest element exchanges the two fundamental weights, so the decision to state no prescribed index matching is harmless; translation of the already-identified homogeneous bundles handles it. The zero character restricts to O(0) and a negative fundamental character to O(-1) on the corresponding rank-one curve, confirming the degree sign and that no dominance assumption has slipped into the second new node. The trivial-group case has Pic(point) = 0 and empty families.

I ran leanfinder, leansearch, loogle and Mathlib grep for each proposed node and the item, and a second semantic phrasing for each. I read the resulting types: abstract root-system bases and coroot evaluations, Coxeter generators, Lie weight spaces, module flags, the ring Picard group, general section functors and topological fibre frames do not supply the geometric assertions. Every added search record reproduces an actual command and raw output; no unavailable service is described as no match. Both new nodes have no proof or proof dependencies. Statement references and proof dependency unions were checked, and no new theorem is used through the proof of a cited node. The local construction and translation remain in the item, avoiding D1/D2 relabelling. This is my author review; the maintainer's independent review remains required.

## Validation

The first required deliver.py --no-push completed successfully at 1e8430055f2. After correcting only the rank-one source-place precision and this report, the final required dry run is rerun before pushing. No Lean file, compiler, Lake, local DAG gate, repository write, launcher edit, git command in the repository or sub-agent was used.
