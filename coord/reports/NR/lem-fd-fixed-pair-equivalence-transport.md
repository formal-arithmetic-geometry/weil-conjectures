# Stage-1 delivery: lem-fd-fixed-pair-equivalence-transport

## Files written

- dag/nodes/sec-fourier-transform/lem-fd-fixed-pair-equivalence-transport.json: statement unchanged; six complete proof steps; status split. The full item is not a Mathlib leaf.
- citations.json: verbatim statement quotations for every node used by every proof step.
- searches.jsonl: five searches actually run with the prescribed msearch.py; read their hits. Inherited mathlib_searches were retained and these results appended.

No new nodes and no new Mathlib leaves. report.md records the review; write_split.py is only a sandbox preparation script.

## Attachments

None. Searched lean/WeilConjectures by the exact item id and by fixed-pair, IsoAlgebra, transport, equivalence and fully-faithful names. CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso and its object/morphism formulas exist in WeilConjectures/Mathlib/CategoryTheory/Endofunctor/Algebra.lean:280–297. CategoryTheory.Endofunctor.IsoAlgebra.fullyFaithfulMapOfNatIso exists in WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebraFullyFaithful.lean:36–55. Neither provides the entire item: in particular the latter has no essential-surjectivity statement or arbitrary-target structure lift. The adjunction version assumes autoequivalences F and G, hypotheses absent here. Therefore none is claimed as an exact attachment.

## WANTED

None. The argument is marked agent-written: the blueprint motivates coefficient transport but does not state this general lemma or its full proof. General category theory used here is available locally in Stacks and Mathlib.

## Problems found and corrected

The imported auxiliary had an empty proof. No statement correction or dispute was needed. The proof now spells out the naturality calculation in both directions and constructs the target lift for every specified v, including its inverse, instead of saying only that structures transport. Its source.place inherited a reference to an earlier report; the current proof and this report are self-contained. All inherited metadata, statement dependencies, blueprint lineage, citations and searches in the node are retained. No unit or chapter files changed.

## Unfinished work

None for this one-level stage-1 split. No Lean was written or compiled. The delivery remains subject to the maintainer's independent mathematical review.

## Not duplicates

No new node was created. Whole-DAG searches for full faithfulness, essential surjectivity, isomorphism lifting and fixed pairs found the existing leaves used below. blueprint_refs.py ancestor identified def-fd-trace-function. Whole-blueprint searches for fixed-pair, equivalence transport, invertible structure and fully faithful found no blueprint node stating this general transport theorem. The fixed-pair sheaf/Weil nodes have scheme and coefficient hypotheses and are not equivalent restatements. same_as is consequently empty.

## Review by NR

I read coord/delivery-errors.md B–E in both copies and checked the delivered statement and proof against those examples. I read GOAL.md, the three blueprint levels in SETUP.md, the Fourier chapter record and the sk-def-trace unit, and the complete main-20261015 def-fd-trace-function source. The unit is a definition with no proof steps. Its last coefficient-category sentence needs a comparison of whole pairs, which is the exact role of this general auxiliary. No route above this auxiliary changes and no SGA source is used.

For the general equivalence facts I read literature/stacks-project/categories.tex, definition-equivalence-categories, lemma-construct-quasi-inverse and lemma-equivalence-categories (Tag 02C3, verified in tags/tags). I also read the actual declarations in Mathlib/CategoryTheory/Equivalence.lean:540–552 and 601–650, and Functor/FullyFaithful.lean:160–222. These establish the Hom bijection, the explicit inverse-lift construction, and the criterion with the displayed functor retained. Mathlib's ordinary Algebra.equivOfNatIso at Endofunctor/Algebra.lean:195 only treats naturally isomorphic endofunctors on the same category and does not discharge this item. The LeanSearch, Loogle and two LeanFinder queries and the Mathlib grep are genuine logged searches. I read the hits: congrLeft concerns functor categories, conjugateIsoEquiv concerns mates, and neither supplies the assertion about invertible structure maps with all the displayed formulas.

I opened and read the statement of every cited node. Here is what each proof step takes from those statements and why the hypotheses hold:

1. lem-sf-quasi-inverse-hom-bijection states bijectivity on each Hom set for a functor with a quasi-inverse and the two natural isomorphisms. The given equivalence J provides exactly that data, even without triangle identities on the chosen isomorphisms. This gives full faithfulness. def-weil-endofunctor-fixed-pair-category really defines objects with an invertible map from the endofunctor, not a noninvertible algebra. The composite J(theta) b^{-1} and its inverse b J(theta^{-1}) have the required types; functoriality checks their products directly.
2. No external theorem is hidden in this step. Naturality of the assumed b is G(Ju)b_K = b_K'J(Fu). Substitution gives the two displayed expressions with the same right factor b_K^{-1}; cancellation and the injection proved in step 1 prove the equivalence. Thus the proof does not merely assert a compatibility.
3. The fixed-pair definition states exactly the intertwining equation and that identities and composition are inherited. The preceding calculation gives well-definedness, and the Hom bijection already obtained supplies the unique preimage of each intertwining arrow. This proves the restricted Hom claim for all source pairs, not just isomorphisms.
4. lem-cbc-fully-faithful-isomorphism-lift states bijectivity of Iso(U,V) to Iso(JU,JV) for a fully faithful functor. Apply it with U=FK and V=K after step 1. The arrow w has source J(FK), through b_K to G(JK), G(v) to GH, psi to H, and v^{-1} to JK. Its explicit inverse has the reverse types. Full faithfulness is the only hypothesis of that node. The previously proved Hom bijection makes the isomorphism lift the unique arrow lift as well, and functoriality proves the formula for its inverse. This does not assume F or G is an equivalence.
5. The fixed-pair definition gives precisely the condition on v and v^{-1}. Both are verified in the text. The inverse equation follows by multiplying the first one by v^{-1} and G(v^{-1}); this uses only the elementary identity G(v)G(v^{-1})=id. Thus the underlying object isomorphism has actually become a pair isomorphism.
6. lem-trf-fully-faithful-ess-surj-equivalence states exactly the criterion used, with smallness in a common sufficiently large universe. The item already makes that universe convention. Fixed-pair objects and morphisms are sets/subsets built inside such a universe (enlarge once to contain all the given data). The counit of J gives the required isomorphism for every target underlying object; steps 4–5 add its pair structure. Step 3 supplies bijectivity on pair Hom sets. The existing Mathlib leaf's asEquivalence construction has precisely the given functor. The trace-formula chapter in this node's name imposes no additional trace hypothesis: I checked its statement, which is pure category theory.

All cited results are existing Mathlib leaves, so no off-unit route exception is needed. The non-elementary inputs are cited as nodes rather than tags alone; every such citation has its full verbatim statement in citations.json. The remaining steps are short substitutions, restrictions of a bijection, and inverse checks; no step exceeds 2000 characters. No clause is repackaged into a new node, no fact is taken from a cited proof rather than its statement, and all proof dependencies equal the union of uses. There is no new-node self-containedness, false-leaf, tag-duplicate or relabelling issue because no new node was introduced.

I tested the statement on the empty category (both categories empty under an equivalence, so pair claims are vacuous), terminal categories, and F=G=id with J=id and b=id (ordinary conjugation of automorphisms). I also checked a genuinely non-equivalent endofunctor: on Set, take F=G the constant singleton functor and J=id, b=id. Fixed pairs are singleton sets with their unique structure maps, and every formula and the arbitrary-v lift still work. The formulas also allow a nonidentity natural automorphism b of an identity functor: theta transports to theta b^{-1}, and the target lift is v^{-1}psi v b. These tests check the orientation of b and confirm that no equivalence hypothesis on F or G was silently used. Noninvertible target structure maps are excluded by the target pair definition, exactly as required. The statement and all its clauses were retained unchanged.
