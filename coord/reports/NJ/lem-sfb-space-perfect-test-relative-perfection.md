# Stage-1 report: lem-sfb-space-perfect-test-relative-perfection

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-test-relative-perfection.json: item, split in six steps, statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-tests-pseudocoherence.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-generator-detects-lower-bound.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-perfect-fibre-criterion.json: statement, unsplit; no Mathlib match.
- citations.json: one verbatim statement quote for each node cited by each proof step.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, relative-perfectness names, generator/boundedness detection, and perfect tensor/pseudo-coherence tests. The sole related affine finite-presentation flat pseudo-coherence declaration concerns a complex already supplied with flat finitely presented terms; it neither gives the item's detection theorem nor these new criteria. No attachment is claimed.

## WANTED

None. All mathematical sources used are present under literature/stacks-project/.

## Corrections and route

The item was unsplit, with no sandbox from an earlier attempt. The imported statement agrees with Tag 0GFL and is unchanged. Read SETUP.md's three levels, the chapter and recorded unit, and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. This is a technical commutative structure-sheaf input below the existing stable-curve/duality/affine-adjoint route; no coefficient category or unit route is replaced. The unit record is not this item's key statement and was not edited.

The source proof of 0GFL says that detecting bounded below yields D-minus. Proposition 0GFI actually gives D-plus, which is what 0GFK requires. Step 2 writes D-plus. The source also calls its fibre Y a scheme, although a fibre of an algebraic space is only guaranteed to be an algebraic space. This is a type-level overclaim: base change gives an algebraic space over the residue field, without a schematicity hypothesis. Steps 3–5 use precisely that type; all inputs apply to algebraic spaces. Neither slip changes the theorem statement. There is no STATEMENT-DISPUTED change.

The statement's existing definitions and inline conventions were retained. The ancestor command returns blueprint.from.node = None; retained the existing detailed provenance and its via chain, and extended it for the three children. Searches of the whole imported blueprint for relatively perfect, pseudo-coherent, pseudo coherence, perfect generator, bounded below, fibre perfect, and the relevant Stacks tags found no existing equivalent blueprint statement. No repository or launcher files were written, and no Lean/compiler/Lake command was run.

## Mathlib research

Ran msearch.py under NJ and this item for the item and all three new nodes: two LeanFinder phrasings, LeanSearch, Loogle, and source grep for each. Read their hits; exact raw outputs are retained in search-results.jsonl, and searches.jsonl is the tool's own execution log. The services all answered. Results give ordinary flat scheme morphisms, ordinary module-sheaf presentations or adjunctions, and general derived IsGE/IsLE characterizations. None detects bounds from a geometric perfect generator, detects pseudo-coherence by global tests, or gives fibrewise relative Tor amplitude. The grep hits for bounded/generator refer to unrelated cardinality, probability, and topology facts. No Mathlib leaf is claimed. Also researched affine pullback of a generator; this was subsequently written as an elementary adjunction argument using existing DAG statements, not created as a fourth node.

## Not duplicates

lem-sfb-space-perfect-tests-pseudocoherence vs lem-sfb-perfect-tests-detect-pseudocoherence: the existing node only states the test for schemes, whereas the new node applies to algebraic spaces; descent from global tests on a space to the hypotheses of the scheme statement is not a specialization.

lem-sfb-space-perfect-tests-pseudocoherence vs lem-sfb-space-perfect-test-relative-perfection: the new lemma assumes only pseudo-coherent test complexes and concludes pseudo-coherence; the item must additionally prove lower bounds on K and its derived fibres and hence relative finite Tor amplitude. This is the first pair of source inputs (0GFJ and 0DII), not a renamed statement of 0GFL.

lem-sfb-space-generator-detects-lower-bound vs lem-sfb-space-perfect-weak-generator: the existing statement detects zero by all shifts, not a cohomological lower bound from vanishing in sufficiently negative degrees. The same distinction rules out the compact-generator and localizing-generation nodes as substitutes.

lem-sfb-space-relative-perfect-fibre-criterion vs lem-sfb-space-relative-perfect-base-change: the existing statement preserves relative perfection under base change; it does not deduce relative finite Tor amplitude from lower bounds on the complex and its fibres.

The new nodes' source tags have no same-source-tag existing nodes in the read DAG. Scheme affine pullback of a generator, lem-pc-perfect-generator-pullback, was not generalized into a new node: the algebraic-space case is proved in the item's step 4 from existing algebraic-space adjunction and affine conservativity.

## Review by NJ

I read spaces-more-morphisms.tex, lemma-characterize-relatively-perfect (0GFL), including its displayed derived Hom computation. For the new pseudo-coherence input I read lemma-characterize-pseudo-coh-improved (0GFJ) and lemma-relative-pseudo-coherent-is-moot (0DII): the former works for separated finitely presented algebraic spaces and yields relative pseudo-coherence; the latter converts this to absolute pseudo-coherence when flat and locally finitely presented. The new statement packages those hypotheses exactly and does not require Noetherianity or properness. It is a genuinely weaker test and conclusion than the item.

For the lower-bound detector I read spaces-perfect.tex, proposition-detecting-bounded-below (0GFI), especially equivalences (1), (2)/(3), (6). The shift convention Hom(G,K[j]) corresponds to Ext^j and detects negative cohomology, not positive cohomology. The generator means zero detection in every integer shift; it does not mean a generator of the abelian category. For the relative-perfection criterion I read spaces-more-morphisms.tex, lemma-bounded-on-fibres (0GFK) and its affine reduction: pseudo-coherence, flatness, and local finite presentation are required; local lower bounds for K and each fibre suffice, with no single bound over the base. Its statement writes the Tor-amplitude condition rather than using a tag as a definition.

In step 1 I opened lem-pc-finite-projective-complex-free-model and def-pc-ring-pseudo-coherent-complex. The former gives exactly the finite-free bounded-above replacement needed to pass from each perfect A-model to the latter definition; projective does not silently mean free. The new pseudo-coherence detector then applies with all three morphism hypotheses in force.

In step 2 I opened lem-sfb-space-perfect-weak-generator, lem-sfb-ringed-site-perfect-duality, and the new lower-bound detector. They state, respectively, existence of a generator, perfectness of its dual, and the implication from a lower bound for the dual tensor test. Finite presentation over an affine base supplies quasi-compactness and quasi-separatedness. The perfect test has a bounded model, so the bounded-below hypothesis is literal. This corrects the source's D-minus typo.

In step 3 I opened lem-sfb-space-derived-qcoh-pullback-tensor; it states derived pullback preserves quasi-coherent cohomology for arbitrary morphisms of algebraic spaces. I use no boundedness preservation from it. Perfection of the pullback is the termwise pullback of a local bounded projective-summand model; the splittings pull back, so no flatness of the residue field over A is presumed. The fibre projection is affine by base change of Spec k -> Spec A, and Y remains an algebraic space.

In step 4 I opened lem-sfb-space-derived-etale-chart-calculus, whose statement explicitly includes Lu* adjoint to Ru*, and lem-sfb-space-affine-derived-pushforward-conservative, which explicitly states both quasi-coherence of pushforward and reflection of isomorphisms without boundedness. Shifted derived adjunction turns zero tests for the pulled-back generator into zero tests for Ri_*F, and applying conservativity to 0 -> F finishes the two-line argument. This avoids a new affine-pullback-generator node.

In step 5 I opened lem-sfb-space-affine-perfect-hom-base-change. Its statement gives the full D(k) isomorphism of derived Hom, for flat X -> Spec A, arbitrary A -> k, perfect first argument and quasi-coherent second argument; all are established. It also identifies degree-j cohomology with shifted Hom. I use neither its proof nor a per-degree substitute. The perfect-duality node converts global Hom on X to the dual tensor test. I opened lem-sc-perfect-pullback-perfect-residue: it states extension of scalars preserves a perfect ring complex, exactly what is needed for the residue-field tensor. The lower-bound detector then applies on the quasi-compact quasi-separated fibre with the generator from steps 3–4. No smoothness, properness, or schematicity is introduced.

In step 6 I opened the new fibre criterion and checked each hypothesis against steps 1, 2, and 5. Its finite relative Tor interval together with pseudo-coherence is precisely the original conclusion. The final lower-boundedness clause is already supplied by step 2. Every citation is quoted verbatim in citations.json; quoted full statements include the clauses used above. The two cross-unit ring-complex tools are explicitly declared in split_report.tool_uses.

I checked delivery-errors B–E: children are self-contained statement-only nodes with empty proofs and proof dependencies, sources use the correct tag-label pairs, all definition dependencies exist, no claim is obtained by citing a node's proof or a definition as a theorem, and all non-elementary inputs have a node. Searched the DAG by tags and concepts before creating children; there are no exact duplicates. New lemmas use hypotheses different from the item and do not merely relabel its clauses. Step 4 is elementary after its cited adjunction/conservativity facts; no fourth node is needed. All six steps are below 2000 characters.

For small cases, X empty and K zero give zero tests, vacuous/zero lower bounds and relative perfection. For X = Spec A the hypothesis includes E = A and forces K itself perfect, consistent with the conclusion and the three criteria. Over a field, a bounded-above but infinitely left-unbounded complex fails the lower-bound test, so the detector is not replacing all-shift zero detection by a single vanishing. The fibre criterion retains the lower bound on K itself; it is not inferred from fibrewise vanishing alone. The residue-field extension uses derived tensor, not the underived fibre. These checks exposed no false child statement.

## Unfinished work

No part of the assigned one-level split is left unfinished. The three new unsplit nodes are future stage-1 items as required; they have statements and actual recorded searches, not recursive splits.
