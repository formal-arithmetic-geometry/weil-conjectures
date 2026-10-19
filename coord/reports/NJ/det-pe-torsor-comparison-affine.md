# Stage-1 split: det-pe-torsor-comparison-affine

1. Files written:
   - dag/nodes/sec-proetale-coefficients/det-pe-torsor-comparison-affine.json — statement, split in nine steps; no Mathlib match.
   - dag/nodes/sec-proetale-coefficients/lem-pe-set-sheaf-cover-descent.json — statement only, unsplit; no Mathlib match after LeanFinder twice, LeanSearch, Loogle and two Mathlib greps.
   - citations.json — one verbatim statement quote per citation in each numbered step.
2. Attachments: none. Project source searches by the exact blueprint tag and by torsor/comparison found no declaration stating this item. Existing site Torsor/TorsorGluing files concern additive torsors and gluing specified maps, not noncommutative affine pro-etale descent. No Lean file was changed or compiled.
3. WANTED: none. All sources read are available in literature/.
4. Faults corrected: the imported references sk-prop-pe-affine-basis and sk-prop-pe-comparison-morphism do not exist in the current DAG. Their needed statements are supplied by lem-weil-pbc-ind-etale-basis and the set-sheaf clause of lem-weil-pbc-comparison-sections. The imported finite-cover argument incorrectly attributed the finite subfamily to quasi-compactness alone, although weakly etale maps need not be open. The finite-affine refinement now comes directly from the fpqc covering condition, as in Stacks 098D. Refining the resulting weakly etale affine disjoint union once by 097Z avoids an extra finite-product ind-etale lemma. The statement itself is unchanged.
5. Nothing mathematical remains unfinished in the item's proof. The one generic auxiliary theorem is intentionally statement-only under the one-level split rule. This delivery adds one new node and zero Mathlib leaves. No unit record was edited: the affine detail is not the unit's key statement.

## Sources and route

I read the current chapter and sk-lem-pe-torsor-comparison unit records, the current main-20261015 affine statement and proof, and the unit proof. The nine steps retain its single affine trivialization, transition function, finite-stage cocycle and etale gluing route. The comparison classifies arbitrary set torsors, with no abelian or finite-group hypothesis.

For the item I read literature/stacks-project/proetale.tex: lemma-compare-cohomology-nonabelian (099X), lemma-proetale-affine (098D), proposition-weakly-etale (097Z), and lemma-limit-pullback (099S). For the new node I read literature/stacks-project/sites.tex, the gluing datum immediately preceding lemma-glue-sheaves (04TR), that lemma's whole statement and compatible-tuples construction, and lemma-glue-maps (04TQ) with its sectionwise equalizer proof. The new node is precisely set-sheaf gluing and morphism gluing, rather than a renamed torsor-comparison assertion.

Mathlib searches are the actual msearch.py calls saved in searches.jsonl; their query strings are copied into the relevant node. Both semantic phrasings were read. The stack theorem CategoryTheory.Pseudofunctor.isEquivalence_toDescentData requires an IsStack instance; reading IsStack.lean lines 49–74 confirms that it does not prove the sheaf pseudofunctor is a stack. Generic section gluing, dense-subsite equivalences, and scheme gluing do not give effective descent of these local set sheaves in one line. No unavailable search was labelled absent. All services used returned results successfully.

## Review by NJ

Step 1 uses the set-sheaf epic/local-surjectivity equivalence to produce actual local sections, the exact finite-affine refinement and singleton-cover statements in sk-def-pe-site, finite affine coproduct = spectrum of the product, the open/disjoint coprojections of the scheme-coproduct node, and weakly-etale source locality. I read these statements and checked that they apply to the given affine X and the finite opens in the original trivializing cover. Sections on the disjoint union glue by the sheaf equalizer axiom, including the empty scheme. This repairs the misuse of ordinary topological compactness.

Step 2 uses the closed refinement theorem exactly for the weakly etale ring map R to B. The definition node identifies its affine scheme and ring conventions, ind-etale stability gives weak etaleness, and the faithfully-flat-surjective-spectrum node gives surjectivity of Spec B' to Spec B. The definition of the site then makes the affine surjection a covering. The ind-etale-algebra definition supplies a small nonempty filtered presentation by finitely presented etale algebras. Surjectivity of every finite-stage scheme follows just by factorization of the same surjection, without openness or surjectivity of the transition maps.

Step 3 uses only the sectionwise-limits node and the torsor isomorphism in the item's hypothesis. I checked the order of noncommutative multiplication: s1 = g12 s2 and s2 = g23 s3 give s1 = (g12 g23) s3. The blueprint convention is used throughout. Stacks 099X writes its initial transition relation in the opposite direction while printing this cocycle order; our explicit left-action computation removes that convention ambiguity.

Step 4 uses the affine fibre-product formula, finite limits in the small etale category, ind-etale stability, and the natural section formula whose last sentence explicitly includes sheaves of sets. I checked that X and all stage products are affine, that the stages are etale of finite presentation, and that the indexing category stays small and nonempty. The displayed test-scheme universal property proves the limit/product interchange. Naturality applies to both group multiplication and projection restriction; it is not a continuity theorem about module sheaves used on groups without justification.

Step 5 uses exactly clauses (1) and (3) of the filtered-colimit-of-sets node, first for a representative and then equality at one later stage. I checked that there are only two elements to compare on the triple product and that the induced group laws are the same ones from step 4. Diagonal normalization and the inverse equation follow by the written substitutions, so the gluing datum includes repeated indices.

Step 6 uses the sectionwise-limits node for the product sheaves, and the new node's existence clause on the singleton etale cover, then its map-gluing clause for the left action and the inverse of the torsor-action isomorphism. Right multiplication by c commutes with left multiplication even in a noncommutative group. I checked the transition convention e2 = right(c) e1; consequently s01 = c s02. The set-sheaf epi/local-surjectivity node applies to the base-changed covering of each object, and proves T0 is locally inhabited. The action laws are equalities of sections checked by the sheaf axiom. No torsor or cocycle classification theorem is being smuggled into a definition citation.

Step 7 uses finite-limit preservation in the comparison geometric-morphism statement for the pulled-back group and action, its explicit adjunction unit for the pulled-back section, the affine-basis statement to test the local maps, ind-etale stability to view each test object over V, its definition to present it by etale V-affines, etale-composition to regard them over X, and the set-sheaf section formula to compute their pullbacks. I checked each source/target and wrote the natural colimit identifications, rather than assuming inverse image commutes with localization without proof. All groups are group objects in set sheaves here, with no change of coefficient category.

Step 8 uses only the new node's unique morphism gluing, with the overlap relation h2 = h1 g written explicitly. The images hs1 and (hg)s2 coincide, so the maps glue; their inverses glue too and uniqueness checks both composites. Equivariance is checked on the same covering. This establishes the comparison isomorphism as a G-torsor isomorphism, not only an isomorphism of underlying sets.

Step 9 uses exactly conditions (1) and (2) of det-pe-classical-sheaves-image, and carries the actual section over the already fixed V through the comparison isomorphism. This proves the affine etale surjection, its T0-section, classicality and etale triviality together.

For the new statement, I tested singleton identity covers, repeated indices, empty covering families when allowed by the topology, and covers of the empty object. The all-pairs cocycle implies identity and inverse transition maps; there is no need to assume different indices or nonempty intersections. The universe is explicitly large enough for the compatible-tuple products. It has a complete self-contained statement, definitions for sites and slice restriction, no proof sketch, and no proof dependencies.

Against delivery-errors B–E: I retained single TeX escapes via JSON serialization, specified the precise Stacks tags and labels, searched both the DAG and whole blueprint before naming the new node, and kept its proof empty. I opened each cited node and copied its actual statement into citations.json; no proof-only material is cited. Every non-elementary step has a statement citation and the only elementary step is the explicit torsor/group calculation in step 3. The new lemma is generic sheaf descent, independent of etale/pro-etale comparison, so it neither restates a clause of the item nor creates a cycle. No SGA source is used, and the unit route is unchanged. Tool uses from other units are recorded in split_report.tool_uses for maintainer review.

## Source error

Stacks 099X writes $g\,s_1=s_2$ but prints $g_{12}g_{23}=g_{13}$. With a left action the former convention gives $g_{13}=g_{23}g_{12}$ instead. For example take the trivial left torsor for $S_3$, choose noncommuting transpositions $a,b$, and sections $s_1=1$, $s_2=a$, $s_3=ba$ at a triple of points of a split three-sheet covering. Then its convention gives $g_{12}=a$, $g_{23}=b$, $g_{13}=ba$, whereas $ab\ne ba$. The current blueprint uses $s_1=g_{12}s_2$, which gives its claimed cocycle order correctly. The split follows that current blueprint convention and verifies both the overlap coordinate change $h_2=h_1g_{12}$ and the comparison-map calculation explicitly. No item statement is changed.

## Not duplicates

lem-pe-set-sheaf-cover-descent vs lem-sfb-sheaf-cover-local-isomorphism: the existing Mathlib leaf detects invertibility of an already given morphism of category-valued sheaves after restriction to a covering family; it neither constructs a global set sheaf from local sheaves and cocycle isomorphisms nor extends an arbitrary compatible family of local morphisms. The auxiliary node is therefore not a specialization of that leaf.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-site-module-sheaf-gluing-aux: the existing node requires local module structures and linear transition maps; arbitrary set sheaves and noncommutative torsors have no such structure.

lem-pe-set-sheaf-cover-descent vs def-weil-pbc-proetale-local-submodule-gluing-data: the existing node defines module or torsor-representation data; the new node is an existence and morphism-gluing theorem for arbitrary sheaves of sets.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-connected-torsor-module-descent: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-associated-module-comparisons: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-module-descent-equivalence: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-ordinary-evaluation: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-equivariant-module-is-sheaf: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs def-weil-pbc-site-module-compatible-tuples: the existing node defines module or torsor-representation data; the new node is an existence and morphism-gluing theorem for arbitrary sheaves of sets.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-equivariant-module-recover-linear: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-graph-evaluation: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-section-evaluation: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-continuous-lattice-finite-coproduct: the existing node assembles integral coefficient lattices on a finite scheme coproduct; the new node is set-sheaf descent along any site covering.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-site-module-sheaf-gluing: the existing node requires local module structures and linear transition maps; arbitrary set sheaves and noncommutative torsors have no such structure.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-ordinary-evaluation-equivariant: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs def-weil-pbc-proetale-local-subobject-kernel: the existing node defines module or torsor-representation data; the new node is an existence and morphism-gluing theorem for arbitrary sheaves of sets.

lem-pe-set-sheaf-cover-descent vs def-weil-pbc-torsor-associated-module: the existing node defines module or torsor-representation data; the new node is an existence and morphism-gluing theorem for arbitrary sheaves of sets.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-normalized-graph-evaluation: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-equivariant-module-diagonal-evaluation: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-proetale-local-subobject-kernel-effective: the existing node concerns abelian/module subobjects of a specified global object; the new node descends arbitrary set-sheaf objects without a global ambient sheaf.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-proetale-compatible-local-submodules: the existing node concerns abelian/module subobjects of a specified global object; the new node descends arbitrary set-sheaf objects without a global ambient sheaf.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-proetale-compatible-local-subsheaves: the existing node concerns abelian/module subobjects of a specified global object; the new node descends arbitrary set-sheaf objects without a global ambient sheaf.

lem-pe-set-sheaf-cover-descent vs def-weil-pbc-torsor-section-representation: the existing node defines module or torsor-representation data; the new node is an existence and morphism-gluing theorem for arbitrary sheaves of sets.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-invariant-sections: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-diagonal-evaluation-bijective: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-associated-module-essential-image: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-proetale-local-quotient-vanishing: the existing node concerns abelian/module subobjects of a specified global object; the new node descends arbitrary set-sheaf objects without a global ambient sheaf.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-section-evaluation-bijective: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-equivariant-presheaf-sheaf: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-section-evaluation-local: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-associated-module-full: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-torsor-diagonal-evaluation: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-site-module-compatible-tuples: the existing node requires local module structures and linear transition maps; arbitrary set sheaves and noncommutative torsors have no such structure.

lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-constant-module-locally-constant: the existing node concerns modules or linear/equivariant section maps for a specified finite etale torsor; the new node descends arbitrary set sheaves on a site and has no finite-group, coefficient or representation hypotheses.

lem-pe-set-sheaf-cover-descent vs lem-pur-sheaf-hom-is-sheaf: the existing node concerns the module-valued sheaf of linear homomorphisms; it gives no effective descent of set sheaves.

lem-pe-set-sheaf-cover-descent vs lem-pur-sheaf-hom-cover-gluing: the existing node glues linear maps of module sheaves; the new node glues arbitrary set sheaves as objects and their arbitrary maps.

## Validation

The required deliver.py --no-push dry run printed OK (not pushed), preflight passed, at 618648a60b. A final dry run checks the report's explicit source-error example and the added step-6 sectionwise-product citation. The sandbox is reserved for the second reader; this worker has not pushed.


## Second reading by NJ

- Step 1: checked the epi/local-surjectivity, fpqc finite-affine refinement, finite affine coproduct, disjoint scheme coproduct and weakly-etale source-locality statements against Stacks 098D and 099X; valid, including the empty affine scheme.
- Step 2: checked the refinement against Stacks 097Z and each cited ind-etale, faithfully-flat spectrum and site statement; valid: surjectivity of U implies surjectivity of every stage by factorization, without any assumption on transition-map images.
- Step 3: checked sectionwise limits and the torsor axiom against the blueprint's Step 2 and Stacks 099X; valid with s1 = g12 s2, including noncommutative groups. The existing source-error report is correct.
- Step 4: checked the actual affine fibre-product, etale finite-limit, ind-etale stability and set-sheaf comparison-sections statements against Stacks 099S; valid after explicitly giving the finite presentation of the tensor powers. The limit universal-property argument handles arbitrary cofiltered indices.
- Step 5: checked clauses (1) and (3) of the cited filtered-colimit node and the diagonal/swapped-pair substitutions; valid, with one later stage enforcing the one cocycle equality. The displayed diagonal normalization holds even for a singleton cover with nontrivial self-overlap.
- Step 6: checked the new auxiliary statement against Sites 04TR/04TQ, and the cited sectionwise-limit and epi statements; valid after explicitly naming the descent node and writing the local torsor inverse's overlap calculation (ac)(bc)^(-1) = ab^(-1). Right multiplication by the transition commutes with the left action, so no abelian hypothesis is used.
- Step 7: checked every cited comparison-morphism, affine-basis, ind-etale stability/definition, etale composition and set-sheaf section-formula statement against the blueprint's Step 5 and Stacks 099S; valid after explicitly proving finite presentation under composition. On each basis object Z over U the natural colimit of the coordinate bijections is the inverse of h maps to h s', so no unproved localization comparison is invoked.
- Step 8: checked the morphism-gluing clause of the new node against Sites 04TQ and the equations on both overlaps; valid. The equality h s1 = (h g) s2 gives agreement of the actual maps, their inverses agree, and uniqueness checks their composites and equivariance.
- Step 9: checked conditions (1) and (2) of det-pe-classical-sheaves-image and the section already constructed over V; valid, proving every conclusion of the unchanged affine statement.
- New node lem-pe-set-sheaf-cover-descent: compared every hypothesis, transition direction, cocycle and conclusion with the gluing datum before Sites lemma-glue-sheaves (04TR), that lemma, and lemma-glue-maps (04TQ) on C/U; valid and self-contained with site, universe and localization definitions. Its existence clause is a substantial independent theorem, not an elementary calculation, a torsor-comparison clause, or an existing module-gluing specialization.

I independently searched the whole blueprint for sheaf gluing and descent, the DAG for 04TR/04TQ and the related terminology, and slopmaster2 for this item's id, the new id, and torsor/comparison. No exact closed source declaration was found. I read the actual additive torsor and torsor-map gluing signatures in WeilConjectures/CategoryTheory/Sites/Torsor.lean and TorsorGluing.lean: they do not state noncommutative comparison or effective descent of arbitrary set sheaves. Three fresh msearch.py calls used the slice-sheaf pseudofunctor/Type vocabulary, a different Loogle name pattern, and generic instance/definition patterns. All succeeded, and their actual results are appended in the auxiliary node and searches.jsonl. IsStack.lean lines 49–74 assume the stack property; DescentData.lean lines 462–470 only identify two images of a given global map. None closes the new theorem in one specialization. Zero Mathlib leaves remain.

Edge checks: over a field and for the trivial group the argument retains ordinary simply transitive set torsors; identity covers reduce the construction to the given sheaf. For the empty base, the site sheaf axiom gives singleton sections, the finite disjoint union may be empty, and the empty affine is its own etale surjective cover. Empty allowed covers in the auxiliary theorem force the unique sheaf on the localized site by the sheaf axiom. Repeated indices in a non-monomorphic cover do not assert that the transition on the whole self-overlap is identity: its pullback along the diagonal is identity, and swapping the two factors gives its inverse. This is exactly what Step 5 proves and Step 6 uses. No statement dispute or statement change was necessary.

Changes made: supplied the finite generators-and-relations calculations in Steps 4 and 7; replaced Step 6's ambiguous “that node” with the descent citation and gave the inverse-map overlap equation; added the three independent actual search records; regenerated every citation quote from the current statements; retained the first worker's split_report.tool_uses proposals, as explicitly required by coord/brief-stage1.md, “Tool uses”. These are requests for review, not the maintainer-owned top-level tool_uses field; the distinction was rechecked against tools/review_split.py. The first worker's report sections remain intact. The cross-unit tools requested for maintainer registration are also listed below and preserve the unit's affine-refinement/finite-stage-cocycle/gluing route.

- lem-weil-pbc-ind-etale-stability: Generic tool: Stability and diagonal of an ind-etale algebra. Its statement supplies exactly the fact cited in the displayed steps; this preserves the unit’s affine refinement, finite-stage cocycle, and torsor-gluing route.
- def-weil-pbc-ind-etale-algebra: Generic tool: Ind-etale and ind-Zariski algebras. Its statement supplies exactly the fact cited in the displayed steps; this preserves the unit’s affine refinement, finite-stage cocycle, and torsor-gluing route.
- lem-weil-pbc-comparison-sections: Generic tool: Sections of the comparison inverse image. Its statement supplies exactly the fact cited in the displayed steps; this preserves the unit’s affine refinement, finite-stage cocycle, and torsor-gluing route.
- def-weil-pbc-site-comparison-morphism: Generic tool: The comparison morphism of sites. Its statement supplies exactly the fact cited in the displayed steps; this preserves the unit’s affine refinement, finite-stage cocycle, and torsor-gluing route.
- lem-weil-pbc-ind-etale-basis: Generic tool: The ind-etale subsite is a basis. Its statement supplies exactly the fact cited in the displayed steps; this preserves the unit’s affine refinement, finite-stage cocycle, and torsor-gluing route.
- det-pe-classical-sheaves-image: Generic tool: The essential image of the comparison inverse image. Its statement supplies exactly the fact cited in the displayed steps; this preserves the unit’s affine refinement, finite-stage cocycle, and torsor-gluing route.

Additional same-source comparisons read independently: lem-pe-set-sheaf-cover-descent vs lem-weil-pbc-glue-sheaves-of-modules concerns arbitrary set sheaves on slice sites rather than modules on topological opens; vs lem-weil-pbc-sheaf-isomorphism-local-open-cover only tests a specified module map on topological opens; vs lem-sc-glue-component-transition-cocycle glues invertible modules for a Zariski cover; vs lem-weil-pbc-projective-space-twist-glued-identification identifies two specified invertible modules on projective space; vs lem-weil-pbc-torsor-diagonal-evaluation concerns representations for a finite etale group torsor; vs lem-weil-pbc-quasi-coherent-iso-on-affine-cover tests quasi-coherent module maps; vs new-r4-self-tor-conormal-dual-chart-iso gives a derived conormal comparison, not sheaf descent; vs def-sc-local-free-generator only defines a module generator; vs det-pe-constructible-comparison-local treats classical module sheaves on an open covering; vs prop-pur-a1-invariance concerns prescribed normalized derived comparisons on an affine line. None supplies this arbitrary set-sheaf existence theorem.

Validation uses the installed deliver.py syntax with two positional arguments: the requested trailing dot prints usage and is omitted on retry. No Lean files or compiler/build tools, shared repository writes, live launcher writes, or direct git commands were used.

Second-reader dry run: the first complete run refused one newly merged same-source-tag node, lem-sfb-sheaf-cover-local-isomorphism, which was not yet in the shared checkout. I read its full current statement in the read-only live DAG mirror and added the exact distinction under Not duplicates; no mathematical dependency or citation changed.

The next required dry run passed duplicate/citation checks and reached preflight, but its terminal session ended with signal 15 before any result was returned. This is not recorded as a passed check. The exact command is retried with its output preserved.

Final second-reader validation: the required deliver.py NJ det-pe-torsor-comparison-affine --no-push retry printed OK (not pushed) at 85a9154d22: preflight passed. Delivery now uses the same repaired node files and the report with this validation result appended; its own preflight runs again before push.
