# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-interval-localization.json`: statement, split in seven steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-enriched-marked-realization.json`: one new statement-only auxiliary theorem, unsplit; no Mathlib match.
- `citations.json`: exact TeX substrings copied from the statements, one for every step/node citation.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item identifier, its blueprint docstring tag, simplicial localizations and coherent nerves found no declaration stating either the item or its new realization input. The upstream master source is reference only.

## WANTED

WANTED: Lurie, Higher Algebra, Notation 1.3.4.11, Proposition 1.3.4.14 and Proposition 1.3.4.7 with its proof, printed pp. 110–114, for both nodes. Read online at https://www.math.harvard.edu/~lurie/papers/HA.pdf; the document is not archived in literature/. No source was downloaded or repository file changed. The proof origin is agent, naming the current blueprint ancestor, as required for external material not archived locally. No Stacks tag states this enriched result. No SGA source is used.

## What was wrong and what changed

The imported statement agrees with HA 1.3.4.7: it retains both closure conditions on W, the full simplicial tensor isomorphism natural in the target, the cylinder projection condition, and the derived coherent nerve. The full-functor localization formulation is the interpretation of the source's marked equivalence. An arbitrary object-preserving locally Kan replacement is permitted by the existing coherent-nerve comparison. The statement is unchanged.

My first working draft hid the argument behind an extension induction and described an inadequately typed cylinder homotopy. I discarded that draft after opening the actual HA proof. The final split gives the explicit endofunctor on each degreewise category, its identity/composition equations, two endpoint natural transformations, and their W-valued components. The independent realization input is now an unsplit node rather than an uncited assertion.

I read the current blueprint ancestor prop-coef-integral-exceptional-adjoint, proof paragraph 2, the chapter record, and the unit sk-prop-sf-biduality-general. This supplies its existing enhancement ancestry for the derived coefficient adjunction; no chapter, unit route, statement or realization changes.

## New nodes

lem-coef-enriched-marked-realization is the marked geometric-realization input from HA 1.3.4.14 and the first part of the proof of 1.3.4.7. It assumes a wide union-of-components simplicial subcategory, with no interval objects, projections, two-out-of-three or model structure on the input. It recovers the enriched localization as the colimit of all degreewise ordinary localizations, with a specified zero-degree leg. It does not say that degree zero alone suffices: the parent's cylinder argument proves that missing fact. It is statement-only, with no proof or proof dependencies.

For its future splitter: the source constructs T[n] from the translation functors t[n] (Notation 1.3.4.11), establishes the realization by mappingwise homotopy colimits and sifted fixed-object algebra colimits (1.3.4.10–14), and marks the component subcategory in the homotopy-colimit factorization at the start of the proof of 1.3.4.7. This is genuine realization machinery, not elementary tensor manipulation. This explanation belongs in the report, not the new unsplit statement.

## Not duplicates

- lem-coef-enriched-marked-realization vs lem-coef-diagonal-coherent-nerve-comparison: the latter compares only weak homotopy types of underlying simplicial sets, not marked localizations or colimits in Cat_infinity.
- lem-coef-enriched-marked-realization vs lem-coef-coherent-nerve-comparison: the latter gives the enriched/infinity correspondence and preserves an already established homotopy pushout; it does not establish the degreewise realization or track these markings.
- lem-coef-enriched-marked-realization vs lem-coef-associative-algebra-sifted-localization: the latter describes a forgetful functor preserving sifted colimits, without the degreewise relative-category realization or canonical zero-degree leg.
- lem-coef-enriched-marked-realization vs lem-coef-simplicial-interval-localization: the new node gives the colimit of all degrees with no interval hypothesis. The item proves that degree zero suffices by explicit interval calculations in Steps 1 and 3–6.

I searched the whole DAG by the degreewise-category/localization/realization concepts and HA 1.3.4.11/14, and the whole blueprint using blueprint_refs.py searches 'simplicial category', 'degreewise simplicial categories realization', 'marked realization' and 'localization realization'. No blueprint duplicate was found. The hit lem-coef-fixed-object-dg-free-model concerns dg mapping complexes and is different. The ancestor command returned prop-coef-integral-exceptional-adjoint. The child's via list prepends the item to its existing ancestry.

## Mathlib searches

The exact msearch.py queries and results are in searches.jsonl and the node records. I read every returned type and SimplicialNerve.lean:14–38,193–197. The coherent nerve is a definition there and its locally Kan foundations are still listed as projects. Ordinary localization, homotopy relations, simplicial-object enrichments and objectwise colimits do not state this comparison. Second semantic phrasings were tried for both nodes. The initial Loogle query 'SimplicialCategory, Localization' did not resolve the unqualified identifier; this is recorded explicitly, and the later quoted 'SimplicialNerve' query succeeded with only the definition as a hit. No unperformed search or service outage is recorded as a negative result.

## Review by Q37

I read HA 1.3.4.7, its proof, Notation 1.3.4.11 and Proposition 1.3.4.14 online, including the explicit vertex formula for r. I opened the full statements of the existing cited nodes. Neither their proofs nor a hidden construction from their proofs is used.

Step 1 is the written endpoint-retraction calculation and a finite induction along undirected edge zigzags. Closure of B under composition is checked on vertices. It uses no assumed saturation under equivalences. Step 2 cites the new node's colimit comparison and specified zero-degree leg; the union-of-components and wide-subcategory hypotheses were verified in Step 1. Its mapping sets may be non-Kan, as allowed by the new statement.

Step 3 transposes a map defined on all simplices, not just vertices. The monotone map q sends (i,0) to 0 and (i,1) to i. Composing two transposed arrows uses the same q in both factors, and injectivity of the given simplicial isomorphism proves functoriality; the identity calculation is written too. Step 4 specializes to endpoints to prove naturality, then verifies preservation of W_n at every vertex by two-out-of-three. These are elementary equations from the hypotheses, so no new lemmas are needed for them.

Step 5 uses exactly the full-functor universal property in lem-coef-hammock-infinity-localization, whose wide-subcategory hypotheses Steps 1–2 verify. It descends the transformations through that full equivalence. Their components are invertible because they are in W_n, and lem-cbc-enhanced-functor-cone-calculus states exactly the componentwise equivalence criterion needed. This is a generic off-unit tool, declared in split_report.tool_uses; it replaces no geometric or coefficient-unit step.

Step 6 uses that same criterion for the natural constant-simplex diagram map, computes the constant colimit by its mapping-space universal property and the contractibility of the simplex index, and uses the new theorem's colimit formula. Step 7 unpacks the full-functor localization definition explicitly included in the new statement. The degree-zero-leg condition ensures that the resulting restriction is the actual theta, rather than an unrelated equivalence.

I tested the new statement on the empty category, discrete enrichments (constant localization diagrams), the ordinary arrow category with only identities distinguished, and a one-object simplicial group with every arrow distinguished (both sides are its classifying space). For n=0 the cylinder construction is the tensor functor with its usual endpoints; for discrete mapping sets it reduces to identities with IX=X. No empty case, fibrancy or additional tensors are assumed. An arbitrary simplicial category need not admit the item's interval tensors but still satisfies the new realization theorem, confirming their different scopes.

I corrected the unsupported draft and replaced its citation strings with actual TeX substrings. The item statement and ancestry are retained, the child is unsplit, and proof_deps is the union of uses. No Lean was written or compiled, no agent was started and no delivery was pushed.

## Unfinished work

The new realization theorem is intentionally statement-only for a later worker. Independent second reading and delivery remain for the next worker after the dry run.

## Second reading by Q37

I independently opened Higher Algebra Proposition 1.3.4.7 (printed pp. 110–114), its hypotheses (1)–(4), the proof's endpoint and degreewise-cylinder construction, Notation 1.3.4.11, and Proposition 1.3.4.14 (pp. 112–113). I also opened the complete statements of every cited DAG node and checked the item's statement clause by clause against the source and those interfaces.

- Step 1: checked the endpoint retractions, two-out-of-three propagation along a single mapping-space edge, finite zigzags, and closure under identities and composition against HA 1.3.4.7 (pp. 112–113); verdict correct and elementary.
- Step 2: checked the definition of the degreewise categories against HA Notation 1.3.4.11 and the marked homotopy-colimit factorization in the proof (pp. 112–113), and checked that the cited realization statement supplies the zero-degree leg; verdict follows from the cited auxiliary node.
- Step 3: checked the explicit map (q(i,0)=0, q(i,1)=i), transposition through the stated interval universal property, and the identity/composition equations against the displayed (r)-construction on HA p. 114; verdict correct and elementary.
- Step 4: checked both endpoint identities and the vertexwise two-out-of-three argument for preservation of (W_n) against HA p. 114; verdict correct and elementary.
- Step 5: checked that the hammock node assumes only wide subcategories, that Steps 1–2 provide them, and that its universal property is on full functor infinity categories; checked the componentwise criterion node for the equivalence claim; verdict correct.
- Step 6: checked naturality under all simplex operators, contractibility of (N(\Delta^{\mathrm{op}})) via its initial object ([0]), the constant-colimit mapping-space argument, and the specified zero-degree leg against HA p. 114 and the two cited node statements; verdict correct.
- Step 7: checked the localization universal property and the identification of the induced map with the original (	heta) against the auxiliary realization statement and the item's displayed conclusion; verdict correct.
- New node `lem-coef-enriched-marked-realization`: checked every hypothesis and clause (small simplicial (A), wide union of mapping-space components, degreewise (A_n,B_n), derived coherent nerve, marked edges, colimit, degree-zero leg, and naturality) against HA Notation 1.3.4.11, Proposition 1.3.4.14, and the marked factorization in the proof of Proposition 1.3.4.7. The node is an explicitly stated auxiliary strengthening of that proof, and is intentionally unsplit; it does not assume the interval objects used by the item. Its localization definition is self-contained and its two definition dependencies were opened. Empty categories, discrete enrichments, (n=0), and a one-object simplicial group were checked as edge cases; verdict acceptable as a statement-only agent-derived input.

I searched the entire DAG for the degreewise relative-category realization, marked localization, and interval-tensor comparison before retaining the auxiliary node; no duplicate or more general existing node states these clauses. I reran the recorded semantic, Loogle, and grep searches and read the returned declarations; none is a Mathlib match. Every citation quote remains verbatim in `citations.json`, and every cited fact is supplied by the cited statement rather than its proof.

Changes made in this second reading: appended this audit section only. No mathematical statement or proof step required alteration after the source and dependency checks; no Lean source, compiler, Lake, or live project was touched.
