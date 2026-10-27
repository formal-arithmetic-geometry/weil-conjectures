# Stage-1 report: lem-sfb-exact-monoidal-equivalence-total-kflat

Group ND, 2026-10-22. Direct delivery; stage 1 only.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-exact-monoidal-equivalence-total-kflat.json: existing statement, now split into twelve steps; statement unchanged; no whole-item Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-monoidal-equivalence-inverse-structure.json: new statement, Mathlib leaf. CategoryTheory.Equivalence.inverseMonoidal, Mathlib/CategoryTheory/Monoidal/Functor.lean:1163, and the four unit/counit equations at 1185, 1190, 1196, 1201 give every clause.
- dag/nodes/sec-six-functors-basics/lem-sfb-additive-total-tensor-cone-comparison.json: new statement, unsplit; no Mathlib match. It states the derived isomorphism, with a natural chain lift and its cone-inclusion compatibility. It has no proof or proof dependencies.
- citations.json: one entry for each cited node in every numbered step, quoting its statement verbatim.
- searches.jsonl: actual msearch.py calls and returned service records, retained without alteration. All recorded searches were run and the hits read. write_split.py is sandbox-only preparation, not a project tool.

## Attachments and existing Lean

No ATTACH claim for the item: the blueprint-tag search in lean/WeilConjectures found none. Concept searches found partial results, not a conjunction giving all clauses under these hypotheses. CategoryTheory.Functor.mapCochainComplexMonoidal supplies monoidal comparison data; CategoryTheory.Functor.preservesFlat_of_isEquivalence supplies flat-object preservation; the derived monoidal equivalence file assumes closed Grothendieck categories and functorial flat resolutions. None establishes this whole item.

For the new general cone statement there are existing project candidates: CochainComplex.mapBifunctorMappingCone₂Iso (WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone:493), CochainComplex.mapBifunctorMap_inr_mapBifunctorMappingCone₂Iso_hom (same file:500), and CochainComplex.mapBifunctorMappingCone₂Iso_hom_naturality (WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality:90). I read their types and proofs, which contain no sorry. The first two are already bound to the sheaf-specific lem-pc-tensor-mapping-cone-iso, whose written statement cannot be cited for arbitrary abelian categories (C4). The new statement has the required general derived form and a natural chain lift; its stage-2 reader can bind that general form to localization of these existing project declarations. I make no unsupported claim about the transitive axiom closure, and did not compile anything.

## WANTED

None. All documentary sources used were available in the read repository. No SGA source used.

## Problems found and corrected

The item was unsplit. Its abstract extension is agent-written, not a verbatim Stacks 06YP theorem; proof_origin records that honestly. The source's proof uses exactness of total tensor on the homotopy category and the cone criterion. I made the cone comparison an explicit supporting statement, and used the existing general cone criterion. The comparison is stated in D(C), together with its concrete chain lift, following the 2026-10-21 derived-form instruction.

I did not strengthen the hypothesis to all small colimits in order to cite lem-sfb-termwise-strong-monoidal or lem-sfb-total-tensor-homotopy: their written statements require more than the item. I wrote the coproduct, differential and monoidal-constraint calculations with countable coproducts only. Finite powers of the integer indexing set are countable, and no exactness of countable coproducts is needed.

The inverse's monoidal structure and its unit/counit equations are a general Mathlib fact, so I made them a Mathlib leaf instead of postponing a standard transport argument. The first search mentioned uniqueness; the delivered statement makes only the existence and four compatibility claims actually verified in the source.

## Not duplicates

lem-sfb-monoidal-equivalence-inverse-structure vs def-sfb-strong-monoidal-functor: the latter defines a coherent structure on a given functor; the former constructs such a structure on a specified inverse equivalence with four unit/counit equations. A definition alone does not assert this theorem, despite the shared notion tag 0FFL.

lem-sfb-additive-total-tensor-cone-comparison vs lem-pc-tensor-mapping-cone-iso: the latter's written statement is for sheaves of modules over a commutative ringed site; the new node is for arbitrary monoidal abelian categories with countable coproducts and states the derived comparison plus its natural chain lift. The existing Lean declaration is more general than the older node's written statement.

lem-sfb-additive-total-tensor-cone-comparison vs lem-weil-pbc-total-tensor-homotopy-cone-signs: the latter assumes a small ringed site and module sheaves and also asserts shifts, homotopies and K-flat properties; it does not assert the abstract monoidal-abelian case.

lem-sfb-additive-total-tensor-cone-comparison vs lem-sfb-exact-monoidal-equivalence-total-kflat: the cone lemma is an independent tool about one category and one arrow; it assumes no equivalence and gives no flatness or K-flatness equivalence. The item's proof uses it only after constructing and checking the signed equivalence comparisons, so its content has not been moved into the new node.

lem-sfb-monoidal-equivalence-inverse-structure vs lem-pd-monoidal-adjunction-equivalence-transport: the latter transports a lax structure between two adjunctions under already specified strong monoidal equivalences; it does not construct the strong monoidal quasi-inverse of a given one-sided monoidal equivalence.

Whole-DAG searches checked the source tags 0FFL, 0G6E, 06YM, 06YP, 07A3 and concepts including tensor cones, exact equivalence, inverse monoidality, cohomology and coproduct preservation. blueprint_refs.py searches covered K-flat, monoidal equivalence, tensor mapping cone, inverse monoidal, monoidal inverse, quasi-inverse, signed total, flat equivalence, cone, 0G6E, 06YM, and preservation of colimits. No blueprint node states either new fact at the required generality. from.node is the ancestor printed by blueprint_refs.py; the inherited via chain is retained and extended by the item for the new nodes. The chapter and unit records were read and left unchanged.

lem-sfb-additive-total-tensor-cone-comparison vs def-sp-total-tensor-summand-interface: the existing node defines canonical inclusions and aliases for total tensors of sheaves of modules; it asserts no mapping-cone comparison or derived isomorphism and does not address arbitrary monoidal abelian categories. Shared tag 0G6E is background for totalization, not equality of statements.

## Review by ND

I read sites-cohomology.tex at definition-K-flat and lemma-K-flat-quasi-isomorphism (06YN/06YP), including the cited lemma-derived-tor-exact (06YM), and derived.tex at remark-double-complex-as-tensor-product-of (0G6E), including its warning that shifting the second argument involves signs. For cohomology I read homology.tex lemma-exact-functor (010N); for cone detection I read derived.tex lemma-acyclic (05RT). For coproducts I read categories.tex lemma-adjoint-exact (0038) and, for the monoidal axioms, definition-functor-monoidal-categories (0FFL). I read Mathlib's inverseMonoidal and all four compatibility declarations with their exact types, rather than relying on search summaries. For the new cone node I read the project chain comparison, inclusion lemma and naturality statement. Its hypotheses are additive bifunctors, the necessary countable total sums, and binary biproducts; all are present in the node. The project supplies a concrete chain isomorphism, which localizes to the derived form. No exactness of sums, enough projectives, boundedness, flat cohomology, resolution choices or closedness is being inferred.

Step 1 uses exactly the natural cohomology comparison stated by lem-weil-pbc-exact-functor-complex-cohomology and the cohomology definition of quasi-isomorphism in def-weil-abstract-derived-category. I wrote the faithfulness argument reflecting zero and the inverse argument reflecting isomorphisms; both F and G are exact as required.

Step 2 uses the full equivalence-preserves-limits-and-colimits statement of lem-galois-equivalence-preserves-limits for the existing countable sums, not an existence assertion for missing colimits. The new Mathlib leaf constructs the inverse structure and states precisely the four equations subsequently used. The equivalence is expressed in adjoint form, with triangular unit and counit, so those formulas apply.

Step 3 uses the universal property actually given by def-weil-pbc-category-colimit and the specified inverse structure maps of def-sfb-strong-monoidal-functor. It constructs both maps and checks both inverse identities. Step 4 uses the actual signed differential and tensor map formulas in def-sfb-preserves-kflat-quasi-iso and naturality from def-sfb-strong-monoidal-functor, testing equality by the same coproduct universal property. Its two displayed terms include the coefficient (-1)^p, including negative degrees.

Step 5 constructs the monoidal constraints rather than citing an all-small-colimits theorem under countable hypotheses. It uses the monoidal axioms explicitly stated by def-sfb-monoidal-category, the differential from def-sfb-preserves-kflat-quasi-iso and coproduct uniqueness. The three differential coefficients for a triple tensor are written down, and the pentagon and triangle reduce summandwise to the corresponding assumed identities. Step 6 uses the inverse forms of the associativity and both unit equations in def-sfb-strong-monoidal-functor, plus the colimit universal property. No proof from another node is invoked in place of its statement.

Step 7 uses the signed tensor definition and coproduct uniqueness only; the symmetry hypotheses are explicitly in the item's statement. I checked both differential terms and both hexagon sign identities. Step 8 reuses the earlier direct constructions for G and uses the counit tensor equation expressly stated by the inverse-structure node. It writes the equation after F and epsilon which proves symmetry of G by faithfulness. Its last assertion follows from the four stated compatibility equations on each coprojection. It does not merely say that coherence transports.

Step 9 conjugates tensor by M with the exact equivalences using the specified inverse tensorator and counit. Preservation of finite limits and colimits by a composite and by a natural isomorphism follows directly by applying the corresponding universal properties, so this is a short step rather than another node. The unit gives reflection. Step 10 quantifies over every acyclic N and writes the chain isomorphism used in the transfer. The reverse implication tests all acyclic A and uses reflection of cohomology, not any flat resolution. Both tensor orders are related by the already checked signed swap.

Step 11 cites lem-pur-quasi-iso-cone-acyclic for exactly the cone criterion its written statement gives, and the new general cone node for exactly its derived comparison. It uses the cohomology functors of def-weil-abstract-derived-category to read that derived comparison. The general cone criterion is declared as a black-box tool from outside the unit, not a change to the unit's finite-coefficient adjunction route. The tensor definition node supplies the map whose quasi-isomorphism is being established; it is not cited as a flatness theorem. Step 12 proves the converse from the definition using 0 -> A, and then combines the preceding equivalences. It requires preservation of quasi-isomorphisms with arbitrary endpoints, exactly as the item says.

I checked B-E of delivery-errors.md against the written files: new nodes are statements only, self-contained, with explicit objects and notions; the new cone is a derived identification; all searches are real logged calls, and candidate general termwise-cone lemmas were rejected for the correct scope reason. Every cited node's statement was opened, and citations.json contains actual verbatim text. No cited existing node depends back on this item. The nodes are smaller tools rather than restated conclusions; the substantive equivalence, signs, constraints and quantified K-flat argument remain in the item's steps. All steps are under 2000 characters; steps marked elementary contain the actual coprojection/sign/universal-property argument rather than a hidden source lemma.

Small cases checked by hand: F=G=id makes tau the identity coproduct map; the zero category and zero complex satisfy all tests; complexes concentrated in degrees p,q reduce tau to c and the symmetry to (-1)^(pq) beta; degrees p=q=1 and p=-1,q=1 give the required negative swap; P=1[0] makes the tensor-cone comparison the usual unitor identification; u=0 gives the direct sum of the target tensor and the shifted source tensor; u=id has contractible cone; the converse K-flat test uses 0 -> A without assuming A flat or bounded. These checks exposed the danger of forgetting the second-variable cone sign, so the non-elementary cone comparison is isolated as a node rather than silently treated as an unsigned degreewise identity.

## Unfinished work

No item clause is left without a proof step. The new general cone node is deliberately statement-only and remains available for its own later processing; the project-source candidates above give its likely existing binding. No Lean file was written and no compiler, Lake, build or local DAG/preflight checker was run. The required dry run and push are performed only by the prescribed delivery tool.
