# Worker report: lem-sfb-etale-algebra-extension-ext

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-algebra-extension-ext.json: item, split into nine complete proof steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-polynomial-cotangent-comparison.json: statement, unsplit; no Mathlib match for derived comparison with arbitrary sheaf generators and its differential cokernel.
- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-cotangent-ext-representative.json: statement, unsplit; no Mathlib match for representing global sheaf cotangent Ext classes after changing generators.
- dag/nodes/sec-six-functors-basics/lem-sfb-two-term-derived-hom-boundary.json: statement, unsplit; no exact or one-line Mathlib match for the two-term boundary calculation together with its degree-zero identification.
- citations.json: verbatim statement quotes for every cited node in every proof step.
- searches.jsonl: actual searches recorded by msearch.py; retained as evidence. Supporting scripts and duplicate-review.json are sandbox working records, not DAG delivery files.

## Attachments

None. Whole-project searches in lean/WeilConjectures for the item tag and for square-zero sheaf extensions, ringed-topos extensions, cotangent classification and Ext representatives found no finished declaration stating every clause. The ring-level cotangent and square-zero ring declarations are not this sheaf theorem. No compiler was run.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Corrections and source reading

The item had no proof. Its statement and existing source field are retained. I read defos.tex Tags 0GQ5 (lemma-extensions-of-relative-ringed-topoi), 0GQ6 (remark-extensions-of-relative-ringed-topoi), 0GQ7 (lemma-extensions-of-relative-ringed-topoi-functorial), 0GQ8 (remark-extensions-of-relative-ringed-topoi-functorial), 08UG (lemma-huge-diagram-ringed-topoi), 08UJ (lemma-NL-represent-ext-class-ringed-topoi), and 08UK (lemma-choices-ringed-topoi). I read sites-modules.tex Tags 08TY (lemma-NL-up-to-qis), 08TS (lemma-differential-seq), and the universal differential construction at 04BL (lemma-universal-module), and derived.tex Tags 0149 (lemma-representable-homological) and 06XS (lemma-negative-exts).

The Stacks torsor construction omits a calculation, and its functoriality proof mentions an omitted compatibility. I do not import those omissions as facts. The item constructs the conormal class directly, proves injectivity by subtracting a derivation, and constructs the inverse by the graph quotient. The coefficient, Baer-sum and automorphism calculations are written explicitly. This is marked proof_origin.by = agent because I supply this assembly rather than simply reproduce a document proof. No SGA source is used.

A sign in the 08UG proof's prose is inconsistent: after defining the difference as b minus nu a, its subsequent sentence reverses a and b, and the correction is displayed with a plus. Our proof fixes a single convention throughout: delta_2 minus delta_1 = theta d, and b' = b minus i_2 theta d. Then b' restricted to J equals i_2 delta_1. This is a correction to the argument's sign, not a change to the item's statement.

The newest blueprint is literature/blueprint/latest, whose COMMITS.txt records main-20261023-1620 at 7284bb09daf97437d544c51882b325f9c52cd345. I read the current chapter, the unit _section.md and the direct-images proof (3). The inherited DAG unit record is older, but this supporting deformation lemma does not change any chapter or unit route. The ancestor tool returns None; the inherited blueprint.from.node = null and via list are preserved. Whole-blueprint searches for cotangent, extension, polynomial presentation, two-term and the relevant tags found no blueprint node stating a new support fact. The two cotangent matches concern affine tangent spaces and trace local terms, respectively. DAG searches by tags and concepts were made before creating each support node.

## Source error

The 08UG sign discrepancy just described is avoided by the explicit checked formula b' = b - i_2 theta d. There is no STATEMENT-DISPUTED issue: the imported statement remains true with all its original hypotheses, including arbitrary, possibly non-quasi-coherent coefficient sheaves.

## Review by Q55

I reviewed the split against delivery-errors B through E with the source and the cited node statements open. In particular I did not assume that the free module on a sheaf of generators is projective. The new representative node is needed because an Ext class need not be represented on one fixed polynomial presentation. It is exactly the smaller existence fact of 08UJ, not an extension-classification clause. The comparison node is 08TY and 08TS in derived form, not merely isomorphisms of the two cohomology sheaves. The two-term node is the Hom exact sequence of the actual complex and the truncation identification, rather than an unqualified appeal to abstract Hom exactness. Each new node is self-contained, statement-only, has empty proof/proof_deps, defines or cites its notions, and records actual successful searches and inspected hits.

Step 1 uses def-sfb-space-naive-cotangent-complex for the actual small-etale complex and its derived Ext convention. The comparison node supplies its presentation isomorphism and coker(d) = Omega; the two-term node supplies boundary kernel and Ext^0 = Hom(coker(d),G). The existing lem-trf-sheafified-module-differentials-cokernel supplies that the sheafified differential module represents sheaf derivations. It works on arbitrary small sites with arbitrary sheaves of rings, and requires neither schemes nor quasi-coherence nor flatness. This is the only off-unit proof citation, recorded as a generic tool use, not as a replacement of a unit step.

Step 2 uses polynomial evaluation from def-weil-pbc-mv-polynomial-ring, the canonical derived comparisons from the comparison node, and naturality from the two-term node. Taking E to be the extension's underlying sheaf always provides a lift and a sheaf-surjective polynomial map. For two choices the coproduct generator sheaf has both lifts, so there is an actual common conormal map. Thus the cited statements suffice to compare classes; nothing is taken from a cited node's proof.

Step 3 applies the two-term node only after using the common presentation comparison, so equality of classes really gives delta_2 - delta_1 = theta d on the same conormal sheaf. I checked the correction b' = b - i_2D preserves products, annihilates ker(a), fixes the kernel and quotient, and descends by local lifts. The two final local arguments prove injectivity and surjectivity of the descended h; we do not assume that global sections of a sheaf epimorphism are surjective.

Step 4 uses precisely the conormal-representative existence statement of the representative node; the module-sheaf category node supplies quotients as sheafifications of sectionwise quotients. The ideal property of the graph, the injectivity of G into the quotient, and the local kernel formula are all computed. These are elementary algebra with the semidirect product's displayed multiplication. This step proves realization of every Ext class and computes the class of the realized object; no new lemma restates the item's bijection.

Step 5 uses only polynomial evaluation and the boundary formula to show the split origin has zero class. Step 6 checks coefficient pushout directly with a graph quotient and applies the two-term node's explicit postcomposition naturality to u delta. The identity works for an arbitrary O-linear u, so no monomorphism, epimorphism or flatness assumption was slipped in. Step 7 uses the same common presentation and the boundary node's additivity: the two projections give (delta_1, delta_2), and addition gives delta_1 + delta_2. This proves the Baer-sum clause, which is not itself an independently quoted Stacks theorem.

Step 8 is the explicit square-zero algebra calculation T_d(t) = t + i d p(t). The comparison and two-term nodes, together with the existing universal differential node, justify exactly the Ext^0 and Hom identifications at its end. The inverse is T_{-d}; composition is addition because pT_e = p. The converse derivation is defined with local lifts and is independent of the lift since T fixes the kernel. Step 9 checks qi_G = i_H u and qT_d = T_{ud}q, and also checks identity on the additional H summand in the pushout quotient. The two-term and differential nodes supply naturality of the identifications, so the argument proves the coefficient compatibility rather than merely saying it transports.

I tested the new statements and the item on the empty site/empty X, G = 0, the zero coefficient map G -> 0, u = identity, and the zero abelian category. For d = 0 as a two-term differential, the boundary identifies Hom(M,G) with its natural summand of Ext^1([M -> F],G), and Ext^0 is Hom(F,G); for d = identity both assertions vanish, as they should. For O = A, derivations and naive cotangent Ext vanish and every A-algebra extension splits via its structure map. In characteristic two, subtraction equals addition but the displayed Leibniz and composition formulas remain valid. The quotient graph intersects the added module trivially even for delta = 0 or noninjective delta. No term in the statements requires a projective sheaf, a quasi-coherent coefficient, or a nonempty site.

All nine steps are shorter than 1,100 characters; no non-elementary step exceeds 2,000 characters or hides a separate comparison lemma. The proof quotes every non-elementary input as an actual node statement. Every uses entry has a verbatim quote in citations.json; compound uses quote the whole statement so hypotheses cannot be clipped away. proof_deps is exactly the union of uses. The new statements do not depend on the item, and the original item statement dependencies are retained.

Mathlib searches were performed with msearch.py for the item and each proposed new node, using LeanFinder, Loogle, source grep and LeanSearch, plus alternate phrasings. searches.jsonl records the actual outputs; no unavailable result is presented as absence. I inspected Algebra.Extension.cotangentComplex and its cotangent-space source in Mathlib/RingTheory/Extension/Cotangent/Basic.lean (lines 52-72), the differential presheaf constructions in Algebra/Category/ModuleCat/Differentials/Presheaf.lean, and Triangle.yoneda_exact and coyoneda_exact in CategoryTheory/Triangulated/Pretriangulated.lean (lines 244-273). The former are ring-level maps, and the latter are exactness for a supplied triangle; neither states the new combined two-term calculation or the sheaf-presentation theorems in one specialization. No Mathlib leaf is claimed.

## Not duplicates

lem-sfb-sheaf-polynomial-cotangent-comparison vs def-sfb-space-naive-cotangent-complex: the existing node constructs the complex using the canonical generator sheaf O_X; the new node compares arbitrary sheaf polynomial presentations in the derived category and identifies their common differential cokernel. The comparison is not part of that definition's statement.

lem-sfb-sheaf-cotangent-ext-representative vs lem-sfb-etale-algebra-extension-ext: the new node represents an arbitrary derived Ext class by a linear conormal map after changing generators, with no extension of ring sheaves as its output; the item constructs and classifies such extensions and proves its operation and automorphism clauses.

lem-sfb-two-term-derived-hom-boundary vs lem-trf-bounded-constructible-derived-hom-continuity: the existing statement is continuity under inverse limits of schemes for constructible complexes; the new statement is boundary exactness and degree-zero Hom for a two-term complex in an arbitrary abelian category.

lem-sfb-two-term-derived-hom-boundary vs lem-pc-perfect-hom-triangle-row-presentations: the existing statement presents covariant five-term rows for a scheme and a supplied triangle; it does not identify the boundary from a conormal term or Hom from a two-term complex into a heart object.

lem-sfb-two-term-derived-hom-boundary vs def-sc-ext-sheaf: the existing definition uses sheaves as both Ext arguments on a scheme; the new statement has a two-term complex as source and proves its specific boundary kernel and cokernel-Hom formula in an arbitrary abelian category.

lem-sfb-two-term-derived-hom-boundary vs lem-sfb-orthogonal-triangle-counit-normalization: the existing statement normalizes the counit of a fully faithful adjunction under orthogonality; it gives neither the boundary sequence nor the two-term degree-zero calculation.

lem-sfb-two-term-derived-hom-boundary vs lem-sfb-adjunction-generator-defect-criterion: the existing statement proves full faithfulness on a finite triangulated closure under a generator hypothesis; the new statement has no adjunction or generators and computes a specific two-term derived Hom.

lem-sfb-two-term-derived-hom-boundary vs lem-sfb-reduction-single-cohomology-normalization: the existing statement handles derived reduction by n and normalization for one-degree cohomology; the new complex may have nonzero cohomology in both -1 and 0 and involves no coefficient reduction.

lem-sfb-two-term-derived-hom-boundary vs def-per-derived-hom-pullback: the existing definition specifies pullback on Hom groups for composite scheme morphisms; the new statement proves an exact boundary calculation with no pullback.

lem-sfb-two-term-derived-hom-boundary vs lem-weil-pbc-hom-into-triangle-exact: the existing statement is covariant Hom into a supplied triangle; the new statement constructs the particular two-term boundary and identifies contravariant Hom from the complex with Hom from its cokernel.

lem-sfb-two-term-derived-hom-boundary vs lem-weil-pbc-triangle-morphism-extension: the existing statement extends morphisms between supplied triangles; it does not construct a two-term complex triangle or prove its degree-zero truncation formula.

lem-sfb-two-term-derived-hom-boundary vs lem-weil-pbc-derived-single-fully-faithful: the existing statement has both source and target in degree zero; the new source has a potentially nonzero degree -1 cohomology and also gives an Ext^1 boundary with its kernel.

lem-sfb-two-term-derived-hom-boundary vs lem-weil-pbc-hom-out-of-triangle-exact: the existing statement gives contravariant Hom exactness for a supplied distinguished triangle; the new statement additionally constructs the two-term boundary using its quotient chain map and identifies Hom from its nonpositive source with Hom from coker(d). This requires the two-term triangle and truncation argument, not just substituting names into the existing statement.

lem-sfb-two-term-derived-hom-boundary vs lem-pur-good-truncation-exact-normalization: the existing statement assumes cohomology concentrated in degree zero and normalizes exact-functor comparisons; the new source may have H^{-1} nonzero and computes its maps into G[0] as well as the boundary into G[1].

lem-sfb-two-term-derived-hom-boundary vs lem-cbc-kan-realization-mapping-classes: the existing statement compares Kan mapping classes and topological homotopy classes; the new statement is an abelian derived category calculation. The shared numeral tag occurs in that source field for another reference and creates no mathematical overlap.

lem-sfb-two-term-derived-hom-boundary vs def-pur-good-truncation-normalization: the existing definition applies to an object concentrated in degree-zero cohomology; the new two-term source can have nonzero H^{-1}, and the output is Hom and Ext rather than a normalization isomorphism.

lem-sfb-two-term-derived-hom-boundary vs lem-pur-degree-zero-derived-map-gluing: the existing theorem glues morphisms of degree-zero-cohomology objects on scheme covers; the new statement does not assume its source is concentrated in cohomology degree zero and asserts no gluing.

lem-sfb-two-term-derived-hom-boundary vs lem-pur-vector-frame-integration-site-descent: the existing statement descends coordinate integration and compares etale/pro-etale vector-bundle traces; the new statement has no schemes, integration, trace or site comparison.

## Remaining work

This is a one-level stage-1 split. The three statement-only support nodes await their own splits. All requested clauses of the item have a complete natural-language assembly proof. No Lean files, repository files or launcher scripts were written, and no compiler, Lake or local DAG check was run.

## Validation

The first delivery dry run rejected the phrase “the item's complex” in Step 1 under the self-contained wording check B2. I replaced it with the explicit symbol NL_{X/B}; the statement and mathematical argument did not change.

The second dry run printed OK (not pushed) at 1aae651a2a0. Before delivery I completed an additional search of the DerivedCategory truncation API: the new recorded queries found Ext.homEquiv, right-fraction lemmas and the isLE/isGE machinery, but no theorem stating the full supporting two-term boundary calculation. I read DerivedCategory/TStructure.lean lines 100-190 and recorded these actual results on the supporting node. A final dry run checks this final record.
