## Worker report

Files written (stage 1 only):

- dag/nodes/sec-six-functors-basics/lem-sfb-space-unramified-radicial-parameter-open.json: split, with six proof steps following Stacks 05X9.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-unramified-diagonal-open.json: one new statement-only node, unsplit, no Mathlib match. This is 05W1(1) for arbitrary algebraic-space targets.
- citations.json: exact statement excerpts for all citations in the six steps.

Attachments: none. The project-source search in lean/WeilConjectures for the exact blueprint id, unramified/universally-injective combinations, and the corresponding declaration names found no finished declaration. Sheaf/AlgebraicGeometry/UniversalUnramifiedRadicialOpen.lean:84 states only the scheme specialization and its proof is sorry. It cannot attach this algebraic-space item.

WANTED: none. All sources used are present in literature/stacks-project/.

The item agrees with 05X9, including its three hypotheses, its algebraic-space parameters and both conclusions. Its doubled TeX backslashes have been normalized; no mathematical hypothesis or conclusion was changed and there is no statement dispute. The existing node lem-sfb-space-closed-source-unramified-base-open states precisely 05X8 and is used instead of creating an unramified-parameter-locus duplicate. Existing forward diagonal node lem-sfb-unramified-space-open-diagonal has a scheme target; existing lem-sfb-space-unramified-open-diagonal is the converse, not the implication required here. These distinctions matter even though the sources share 05W1.

Nothing remains unfinished in this one-level split. The one new input is deliberately statement-only for its later worker. No Lean was written and no compiler or Lake was run.

## New nodes

lem-sfb-space-unramified-diagonal-open states 05W1(1), with both source and target arbitrary algebraic spaces, using the existing chart-test and open-subspace definitions. Its statement is self-contained, including its universe convention and what a representable open immersion means. It has no proof, no proof dependencies, no embedded proof sketch and no Mathlib match. LeanSearch, Loogle, LeanFinder with two distinct phrasings, and the recorded Mathlib grep all ran successfully. The hits were scheme results. I read FormallyUnramified.lean:126 and its surrounding scheme variable context; the instance requires Scheme source and target and is not a one-line specialization to algebraic spaces. Mathlib UniversallyInjective and its diagonal theorem are likewise about schemes. Exact query text and actual result summaries are preserved in mathlib_searches and searches.jsonl; the item's own new searches are recorded separately from its inherited searches.

For this node I searched the entire DAG by 05W1, the diagonal/unramified/open-immersion concepts, the proposed id, and by reading every statement that combined these concepts with algebraic spaces. I searched the project Lean source and ran blueprint_refs.py search for 'diagonal unramified', 'open diagonal', '05W1', and 'universally injective'. None supplies the forward implication with arbitrary space target. The item was also searched in the blueprint using 'unramified universally injective' and '05X9'; no matching blueprint node exists.

## Blueprint and route

I read the chapter and unit records and the newest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, particularly (3). The item is a deeply nested supporting input for the alteration/moduli/graph construction recorded in its inherited blueprint.from.place, not the unit's key theorem. That inherited chain has blueprint.from.node = null; blueprint_refs.py ancestor returns None for it. I retain that null ancestor, extend the exact place by the 05X9 diagonal sentence, and prepend this item to the new node's via list. Neither chapter nor unit was changed. The new node's same_as is empty after the whole-blueprint search.

The generic tools from the trace-formula and real-sheaves units are the sheaf fibre-product construction, the point-lifting theorem 03H4, open factorization 03IE, and open-subspace construction 03BZ. They are exactly the background results invoked by 05X9. Their use is explained in split_report.tool_uses for maintainer review; no top-level tool_uses approval was written.

## Not duplicates

lem-sfb-space-unramified-diagonal-open vs lem-sfb-unramified-space-open-diagonal: the existing forward implication requires a scheme target; the new statement allows an arbitrary algebraic-space target. Generalization requires etale-chart descent, not a one-line specialization of that restricted statement.

lem-sfb-space-unramified-diagonal-open vs lem-sfb-space-unramified-open-diagonal: the existing node is 05W1(2), open diagonal plus local finite type implies unramified; the new node is 05W1(1), unramified implies open diagonal, for arbitrary space targets.

lem-sfb-space-unramified-diagonal-open vs lem-sfb-dm-geometric-inertia-trivial: the existing node uses 05W1 among the sources for representability of a DM stack with trivial geometric inertia; its statement asserts no open-diagonal theorem for a given morphism of spaces.

lem-sfb-space-unramified-diagonal-open vs lem-sfb-space-unramified-radicial-parameter-open: the new lemma is a basic property of the relative diagonal of one unramified map, with no closed projections, family or parameter-locus assertion; it is not a restatement of the item's conclusion or a parameter-locus clause.

The general stack node lem-sfb-stack-universal-injectivity-criteria was inspected; a new space-only diagonal criterion would duplicate its more general content. Instead step 5 writes the short point proof directly from the existing fibre-product calculus, and creates no such node. The scheme node lem-sfb-universal-unramified-radicial-open is not a duplicate of the item: its objects and its quantified tests are schemes, whereas the item requires arbitrary algebraic spaces.

## Review by Q112

I read spaces-more-morphisms.tex at lemma-where-unramified and lemma-where-unramified-universally-injective (05X8 and 05X9) in full. I checked the open-diagonal input against spaces-morphisms.tex, lemma-diagonal-unramified-morphism (05W1), including its compatible-chart proof. I read the point-square lemma in spaces-properties.tex, lemma-points-cartesian (03H4), and the open-subspace and factorization lemmas lemma-open-subspaces (03BZ) and lemma-factor-through-open-subspace (03IE). The short diagonal criterion in step 5 matches spaces-morphisms.tex, lemma-universally-injective (040X), equivalence (2)--(3). It is written as the three elementary point calculations rather than hiding an extra lemma behind a tag.

Step 1 uses the statement of lem-sfb-space-closed-source-unramified-base-open, not its proof: it explicitly quantifies arbitrary space changes and says factorization is equivalent to unramifiedness. I checked that the original p is both locally finite type and closed, and that the triangle is the given one. Applying it to B0 itself really gives unramified f0; no local finite type of q or properness is needed.

Step 2 uses lem-trf-space-fibre-products-etale-covers for the sheaf fibre-product universal property and lem-a1-space-open-factor-scheme-tests for the point set of a pullback of an open. Both statements were opened. The identification of the relative square is written on each test scheme as a pair with equal C image and a common B coordinate; hence the diagonal identification is justified as well. The relative closed-set formula proves closedness after restriction to B0. This is a restriction to an open base, and does not assume that a closed map is universally closed.

Step 3 uses the new 05W1(1) statement only after step 1 has established unramified f0. No scheme target is assumed. The cited algebraic-space definition supplies the scheme atlas needed by lem-a1-space-invariant-open-quotient, whose statement constructs the open subspace with exactly the prescribed open point image. The open-subspace definition justifies composing the two open inclusions by scheme tests. The only closed-image input here is the restricted r from step 2. E is merely a closed subset; I do not invent a closed subspace structure on it.

Step 4 uses the cited fibre-product universal property for D_T and its diagonal, the open-factor node for the inverse-image point set and unique open factorization, and the point-open-calculus node for surjectivity onto pairs of matching points. All these clauses occur verbatim in their statements (citations.json includes the whole open-factor statement because two separated clauses are used). In particular, each pair (d,t) with d in E and r(d)=h(t) has a lift, so the empty-inverse-image equivalence is valid without flatness, scheme representability of T, or universal closedness.

Step 5 invokes only the two cited general fibre-product/point statements. For the forward implication, injectivity of the first projection, which is one of the base changes in the definition, and its diagonal section imply surjectivity of the section. For the reverse, point lifting preserves surjectivity of the diagonal under every base change, and lifting a pair of source points over a common target point then makes those points equal. These are elementary identities and applications of the quoted surjectivity formulas. I removed the initially contemplated use of the stack universal-injectivity criterion: no comparison of algebraic-space and stack quantifiers is necessary. This also avoids creating a duplicate lemma for that criterion.

Step 6 assembles only earlier steps. I checked both directions in the original base, using uniqueness of factoring through the subfunctor B0, and the fibre-product identifications already written in step 2. It uses no new theorem and changes no hypotheses.

For the new node, small cases include the empty source (empty open diagonal), an identity, arbitrary nonseparated unramified examples, and a degree-two finite etale map over a field (the diagonal is one of the open-and-closed components, not necessarily all of the square). No separation hypothesis was added. For the item, an empty source gives V=B; a finite etale double cover over a field has empty radicial parameter locus; an identity has V=B whenever the stated closed-map hypotheses hold. A nonempty map Spec(k[e]/e^2) to Spec(k) has empty unramified parameter locus, so the diagonal argument is only applied after the first reduction. Empty T factors through every open, and the unique empty-source induced map has both properties, as the claimed equivalence requires. I checked that no proof step exceeds 2000 characters and no step contains an unextracted standard subclaim: the longest step is the explicit three-calculation point criterion. B1--B10, C1--C8, D1--D5 and E1--E7 were checked against the actual files and sources as described above. No mathematical statement error was found.
