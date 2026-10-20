# Stage-1 delivery: lem-sfb-braided-sheaf-tensor-generators

1. Files written:
   - dag/nodes/sec-proetale-coefficients/lem-sfb-braided-sheaf-tensor-generators.json: item, statement, split without a change to its statement.
   - dag/nodes/sec-proetale-coefficients/lem-sfb-local-equivalences-braided-tensor.json: statement, Mathlib leaf, GrothendieckTopology.W.monoidal with its two end-existence families inferred from small completeness.
   - dag/nodes/sec-proetale-coefficients/lem-sfb-braided-monoidal-localization.json: statement, Mathlib leaf, ordinary braided monoidal localization and strong braided localization functor, one declaration per structure.
   - citations.json: one verbatim statement quotation per cited node per item step.
2. Attachments: none. The project declarations monoidalCategory_sheaf_of_essentiallySmall and braidedCategory_sheaf_of_essentiallySmall in WeilConjectures/CategoryTheory/GrothendieckAbelian/Monoidal/Defs.lean cover structures, but do not give all clauses, including the prescribed tensor comparison and Hom bijections, of the item. No exact blueprint-tagged project declaration exists. Project derived braiding constructions concern derived tensor and include sorry; they are not this abstract ordinary localization result.
3. WANTED: none. All material used is available locally.
4. The imported node has a correct statement, but no proof. Its earlier Mathlib searches correctly identified component results, not an exact attachment for all clauses. The original construction referenced symmetric-only sheaf tensor nodes, which cannot be used at braided generality. This split retains the generality and uses ordinary braided localization. No statement dispute, target change, coefficient-category identification, or unit-route departure is made.
5. Unfinished: none for the one-level split. Both new nodes are Mathlib leaves with statements only. No Lean was written or compiled; the repository and launcher were read only. The unit is not this item's own key statement, so its realized fields are untouched.

## Sources and searches

I read the current main-20261015 chapter record and unit sk-def-sfb-module-pushforward-pullback, the ancestor lem-sfb-pushforward-comp-monoidal statement and full proof (especially its first sentence), and the existing symmetric tensor local-iso and tensor-structure statements and proofs. The latter's conjugation/cancellation argument explains why identifying the actual tensor matters, but its symmetry hypothesis prevents direct citation.

For the local-map leaf I read Mathlib/CategoryTheory/Sites/Monoidal.lean:104-154, in particular W.whiskerLeft, W.whiskerRight, and W.monoidal. The left side uses the presheaf internal hom into a sheaf; the right side uses the braiding, not its square being the identity. I also read Enriched/FunctorCategory.lean:47-54 and 290-296, Limits/Shapes/End.lean:209 and Limits/Shapes/Multiequalizer.lean:1046-1047: the enriched-end hypotheses are literally small limits, not an additional finiteness or concreteness assertion. The coefficient category's small limits are supplied by the existing lem-coef-grothendieck-small-limits.

For the localization leaf I read Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean:89-101, 124-185 and 447-477 and Braided.lean:124-139. These construct the monoidal category, its strong functor, the two hexagons, and the braided functor equation. Choosing the unit parameter to be L(1) and epsilon = Iso.refl gives the stated identity unit comparison. I read Sites/Localization.lean:31-91 as an independent check on the item's explicit reflector-localization argument, not as an uncited input.

Mathlib searches were run only through the prescribed msearch.py; searches.jsonl records their original results. The item was searched with two semantic phrasings, Loogle, LeanSearch and grep. Each new leaf was searched with its own statement in mind using LeanFinder, Loogle, LeanSearch and grep, and the hits were read at the lines above. Two narrow single-file grep calls expose the search tool's filename parser limitation; they are not used as file/line evidence. The directory-scoped calls give the correct files and lines. No unrun search is recorded. Existing searches in the item are preserved.

The whole-DAG and blueprint searches used the terms sheaf tensor, enriched, internal hom, monoidal localization, stable under tensor, braided monoidal, W.monoidal, LocalizedMonoidal, sheafification-inverting and local equivalences. The closest cases are distinguished below; none states either new result at its generality. Project Lean searches covered the item tag, braided sheaf/tensor terminology and the generic localization names; they found no exact project attachment. No SGA source is used.

## Not duplicates

lem-sfb-local-equivalences-braided-tensor vs det-def-sfb-sheaf-tensor-local-iso: the existing node inherits closed symmetric Grothendieck abelian, additive coefficients from det-def-sfb-sheaf-tensor-presheaf; the new Mathlib leaf assumes only complete closed braided coefficients, and does not assume sheafification. It supplies the missing braided case.

lem-sfb-local-equivalences-braided-tensor vs det-def-sfb-sheaf-tensor-hom-sheaf: the existing statement asserts sheafhood of internal Hom only in the symmetric inherited setting; it does not state tensor stability for braided coefficients.

lem-sfb-local-equivalences-braided-tensor vs det-def-sfb-sheaf-tensor-presheaf: the existing statement constructs symmetric presheaf tensor and internal Hom, whereas the new leaf states the local-map stability consequence without symmetry or abelian hypotheses.

lem-sfb-local-equivalences-braided-tensor vs lem-weil-pbc-tensor-local-bijection-universes: the latter is about sectionwise tensor over a presheaf of commutative rings and locally injective/surjective maps with abelian weak sheafification, not arbitrary complete closed braided coefficient categories with the categorical Hom test.

lem-sfb-local-equivalences-braided-tensor vs lem-pe-internal-section-tensor-comparison: the latter assumes local-map monoidality and compares two module tensors; it does not prove local-map stability.

lem-sfb-braided-monoidal-localization vs lem-coef-relative-symmetric-monoidal-localization: the latter is about symmetric monoidal infinity-categories and homotopy coherent localization; the new Mathlib leaf is an ordinary braided monoidal category result, requires no symmetry, and has no infinity-categorical hypotheses.

lem-sfb-braided-monoidal-localization vs det-def-sfb-sheaf-tensor-structure: the latter prescribes a sheafified tensor for symmetric Grothendieck coefficients and explicit unit-map constraints. The new leaf is generic ordinary localization; it does not identify its lifted tensor with the item's prescribed sheafification tensor. That identification is proved in item steps 6--7.

## Review by ND

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the actual node statements and the sources above. Both new nodes introduce their own objects, hypotheses and meanings. They have no proof steps or hidden proof in their statements, complete blueprint origins through the current item, and recorded actual Mathlib searches. No new node is an elementary fact: tensor stability uses enriched Hom/sheafhood; monoidal localization constructs a localized bifunctor and its coherence. Neither is the item or a clause of it restated: one provides an independent local-map theorem without a reflector, the other a generic localization theorem without a site. The item still proves its own tensor identification, normalization and generator tests. All its steps are below 2000 characters.

Step 1 uses exactly the monoidal data in def-sfb-monoidal-category and the sheafification adjunction in def-weil-pbc-sheafification. Pointwise identity, composition, naturality and coherence are checked at each object, not inferred from a symmetric-only result.

Step 2 uses the new leaf's definition of W and the stated unique extension adjunction. I checked the two tests H = aP and H = aQ: a left inverse comes from surjectivity, and injectivity gives the right inverse. The unit Hom test is precisely the universal property. Fullness of the given inclusion gives the counit inverse. citations.json quotes the definition of W here, not the unrelated stability conclusion.

Step 3 uses precisely the existing small-limit theorem's universe-matched conclusion and the new leaf's left/right tensor stability. A V-small C and its slice categories have V-small end diagrams; the Grothendieck category has Hom sets and colimits in V, exactly the hypotheses of the existing limit node. The two-unit tensor is a composite of one left and one right tensoring. No symmetry, flatness, enough points, or tensor preservation of limits is used.

Step 4 proves the full localization property from the adjunction, including natural transformations, with extension TU, the isomorphism T(eta), and the counit isomorphism. The localization property is not taken from a definition node that states less: the factorization and its inverse are written out.

Step 5 uses exactly the generic leaf's conclusion. Step 1 supplies a braided monoidal source, steps 2--3 supply its multiplicative tensor-stable W, and step 4 supplies localization. Its unit parameter is explicitly aI.

Step 6 proves the comparison to the actual tensor, using c = (epsilon diamond epsilon) mu^{-1}. I checked its direction and naturality. For each expression B the recursive c_B has source B_* and target B_diamond. Defining each constraint by c_target^{-1} old_constraint c_source makes adjacent c_B factors cancel. Naturality proves the same formula inside a larger tensor expression. Thus the pentagon, triangle and both hexagons reduce to the known diagrams. This is the written conjugation calculation, not an implicit claim that two chosen tensor bifunctors are definitionally equal.

Step 7 checks the prescribed strong tensor map. Naturality of old mu at eta_P and eta_Q, then epsilon_{aP} a(eta_P) = 1, gives mu_PQ c_{aP,aQ} Delta_PQ = 1 after cancelling mu_PQ. Since every factor is invertible, this is Delta_PQ^{-1}. The same c conjugation in the old functor equations proves strong braided compatibility, and the sheaf braiding is a(beta^p), without imposing beta squared = 1.

Step 8 uses only the unit's naturality and the exact unique-extension property of def-weil-pbc-sheafification. I checked that the maps are h mapped to U(h) composed with the stated t or u. These are maps of whole presheaves, so the proof does not assume every section of a sheafified tensor is a single tensor or comes from a global presheaf section.

Step 9 applies the preceding small-site construction on a small skeleton, as the statement explicitly requests. It does not take an end over an essentially small category without shrinking its objects.

Edge cases: with the trivial topology a and eta can be identities, all comparisons reduce to the original pointwise tensor. For the empty site its unique sheaf category makes every constraint and Hom bijection the unique one. Zero sheaves and the zero abelian category cause no inversion of zero maps other than isomorphisms of zero objects. On a site with empty covers, sheaves satisfy the required terminal-object condition and the Hom test still works. As a nonsymmetric test, graded rational vector spaces with braiding x_m tensor y_n mapped to 2^(mn) y_n tensor x_m are closed braided Grothendieck abelian; the double braiding in degrees (1,1) is 4. Every step remains valid there, and no use of a symmetry equation occurs.

The corrections made during review were to distinguish the abstract localized tensor from a(UF tensor UG), spell out the coherence cancellation and the exact strong tensor map, and replace the step-2 citation quote by the W definition it actually uses. All original item statement clauses, source metadata, previous searches and citations are retained. The off-unit existing definitions and the small-limit theorem are generic tools, declared only under split_report.tool_uses as required by brief-stage1; no top-level tool_uses is set. No false statement or unproved inline non-elementary sublemma remains.

The first dry run required a separate mathlib_match.line field in each new leaf; I added the already-read source lines (152 and 447), retaining the per-clause line details in how. No mathematical change was required.
