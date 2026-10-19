## Files written

- `dag/nodes/sec-six-functors/lem-coef-small-flat-subsheaf.json`: retained the earlier attempt's nine-step explicit construction, checked it against the current repository and sources, and added actual fresh logged Mathlib searches. The statement is unchanged; status is `split`.
- `citations.json`: retained and rechecked all fifteen step/node entries against the current statements; every quotation is verbatim.
- No new nodes, new definitions, or Mathlib leaves. No unit record is changed: this item is infrastructure below a unit, not its key statement. Sandbox scratch files are not delivery files.

## Attachments

None. A fresh search under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for `lem-coef-small-flat-subsheaf`, small-flat, pure-subsheaf, bounded-subsheaf, Recktenwald, and Kaplansky vocabulary found no declaration stating the item. The only Kaplansky matches concern unique factorization domains. Reference material with a sorry would not be an attachment.

## Sources and WANTED

Read the chapter and unit records `sec-six-functors` and `sk-prop-sf-biduality-general`, the current main-20261015 statement and proof of `prop-coef-integral-exceptional-adjoint` in `sec-six-functors/sk-thm-sf-package/`, and the item's historical blueprint ancestry. Paragraph 2 still invokes derived coefficient adjunction. This foundational split expands a descendant of that invocation; it changes no geometric route or unit binding.

The proof inputs actually read are Stacks `sites.tex`, Tag 00VH (`definition-site`), Tag 00WB (`theorem-plus`), Tag 00WK (`lemma-sections-sheafification`), and `section-sheaves-algebraic-structures`, especially (beta) and (gamma); and `sites-modules.tex`, Sections 03CS/03CV for the module operations, Tag 03CY (`lemma-sheafification-presheaf-modules`), the cokernel construction immediately preceding Tag 03DA (`lemma-abelian`), and Tag 08FC (`lemma-flat-eq`), equivalence (1) and (2). The cardinal construction and finite-system closure are explicit agent arguments, correctly recorded with `proof_origin.by = agent`.

WANTED: Rene Recktenwald, *Construction of Six Functor Formalisms* (2019), Proposition 2.5.31, Lemmas 2.5.12 and 2.5.25, Corollary 1.4.7 and the bounded-subobject portion of Corollary 2.5.33, printed pp. 73–76, cited by the inherited node. It is not archived locally and was not consulted in this pass. The proof does not use an assertion attributed to these unread pages. Nothing was downloaded or written into the literature.

## Findings and corrections

There is no statement dispute. The original repository item is unsplit and has exactly the hypotheses and conclusion retained here: a small site, a commutative ring sheaf, tensor-flatness, a uniform bound on all sections, a nonzero flat subobject, and a flat sheaf quotient. No points or flatness on sections are assumed.

The earlier attempt already repairs the delicate mathematical inferences: the countable sectionwise union is sheaf-closed before being used as the subobject; quotient sections lift only locally; the ambient sheaf is used through 08FC, never through sectionwise flatness. The retained target-labelled restriction codes cover empty and repeated-arrow coverings without bounding their original index sets. I found no further mathematical correction necessary. Fresh candidate searches and source checks were added to the item; this report replaces the inherited author/second-reader narrative so the next independent reader can sign their own reading.

## Not duplicates

No new nodes were created. Fresh whole-DAG searches included the tags 08FC, 03CY and 00WK, bounded/pure subsheaf and small-flat vocabulary; whole-blueprint searches included `small flat`, `pure subsheaf`, `finite linear`, and `cardinal`. The cardinal hits concern constructible stalk sizes, curve Betti numbers, traces and locally constant sheaves, not uniformly small flat subsheaves. `blueprint_refs.py ancestor` confirms the retained ancestor `prop-coef-integral-exceptional-adjoint`; `same_as` remains empty.

`lem-weil-pbc-site-flat-equational-criterion` supplies exactly the local criterion needed. The arbitrary-site module-sheafification interface, underlying-set compatibility, and local-sections nodes supply the quotient argument. Ringed-space-only cokernel or sheafification nodes are not used for this arbitrary site. Steps 2–3 prove bounded generation directly, and Steps 4–6 prove the required solution reflection directly; neither argument is moved into a duplicate or a new statement restating a clause of the item.

## Mathlib searches

The retained records from the earlier attempt are preserved. This pass ran the following additional or repeated searches only with `msearch.py NN lem-coef-small-flat-subsheaf`; their actual records are in `searches.jsonl` and the item records their exact tool/query text:

- LeanFinder: `Every nonzero flat sheaf of modules has a nonzero pure subsheaf of uniformly bounded cardinality with flat quotient`.
- LeanFinder, second phrasing: `Kaplansky theorem for flat sheaves on ringed sites: closure under finite linear equations produces a bounded pure subobject`.
- Loogle: `"SheafOfModules", "Flat"`.
- grep: `pure.*subsheaf|subsheaf.*pure|small.*flat|Kaplansky.*flat`.
- LeanSearch: `A flat module sheaf on a small site has a small flat subobject and a flat cokernel`.

All services answered. Loogle had zero hits. The other results were ordinary module flatness, sheaf generator/finite-presentation predicates, colimit existence instances, or the different categorical notion of flat functor. I read the returned signatures and relevant source declarations in `Mathlib/Algebra/Category/ModuleCat/Sheaf/{Generators,Quasicoherent,Colimits}.lean`, `Mathlib/RingTheory/Flat/{Basic,EquationalCriterion}.lean`, and `Mathlib/CategoryTheory/Functor/Flat.lean`. `Module.Flat.of_shrink` preserves flatness under a universe equivalence; it does not construct a small submodule. The equational criterion in Mathlib applies to one ordinary module, not a sheaf whose flatness is only local. No hit states this item or specializes to it in one line.

## Review by NN

I reread delivery-errors B–E with the sandbox item, its cited node statements, and the above Stacks passages open. The item is self-contained and unchanged. There are no new nodes to audit for B1–B9 or to test as separate statements. The retained proof is an argument rather than a relabelling of the conclusion: bounded closure is constructed explicitly, solution reflection is proved from that closure, and two applications of a pre-existing flatness criterion prove the two flatness clauses. The statement dependencies define the site, module sheaves and tensor-flatness. The proof dependencies are exactly the union of step citations. No dependency uses a proof hidden inside a node or requires a hypothesis absent here.

Step 1 cites `def-weil-pbc-sites-and-cohomology`, whose statement gives the small object/morphism sets and covering families. I checked the infinite-cardinal equalities and the encoding by target, arrow support and restrictions. A repeated arrow gives identical restrictions; the argument does not claim its removal is a covering. For an empty covering the target label is still part of the code.

Step 2 cites `def-weil-sheaf-of-modules-category`. Its statement explicitly gives section modules and semilinear restriction maps. Restricting coefficients as well as generators proves that the sectionwise spans form a subpresheaf. Finite tuples of generators and ring sections give the bound; no unspecified bounded-generation theorem is used.

Step 3 cites both preceding definitions. The site's pullback/composition axioms give restriction stability, common refinements for addition and composite witnesses for gluing; the sheaf axiom of F gives the unique glue. A chosen restriction code determines at most one section by separatedness. There are at most lambda targets, 2^lambda supports, and kappa^lambda choices of restrictions. This proves the asserted bound from the displayed construction, including the empty-cover case.

Step 4 cites the module-sheaf definition and applies the preceding construction. F is nonzero exactly when some section is nonzero. At each stage only matrices over ring sections and finite right-hand-side tuples from the bounded stage are enumerated, so there are at most kappa systems. Selecting one existing solution per solvable system adjoins at most kappa sections. Including every old-stage section makes the recursion increasing. The step imposes no flatness condition on F(V).

Step 5 cites the site and module-sheaf definitions for the sectionwise union and refinements. Finite sums lie in a common stage because the stages increase; the countable union has size at most kappa. Its local saturation is the actual subsheaf P, retains the nonzero section, and has the bound proved in Step 3. For finitely many constants one refines finitely many coverings; each resulting member has its own finite maximum stage index. A uniform index over an infinite covering is neither asserted nor needed.

Step 6 is elementary from Steps 4–5 and has no external citation. On each member the restricted matrix and right-hand side are among the systems actually enumerated at that stage. The given ambient solution witnesses solvability, so the next stage contains a chosen solution. This proves local reflection of simultaneous finite systems, rather than invoking an unrecorded purity theorem.

Step 7 cites `lem-weil-pbc-site-flat-equational-criterion`. I read its entire statement and checked it against 08FC: tensor-flatness is equivalent to the stated local relation factorizations on an arbitrary small ringed site. The criterion applied to F gives a coefficient matrix and a solution tuple. Step 6 replaces that tuple by local sections of P for the same matrix, so the coefficient identities still hold. The converse criterion proves P flat. This does not identify sheaf-flatness with flatness on sections.

Step 8 cites five statements, all of which I opened. The module-category definition says cokernels are sheafified sectionwise cokernels. `lem-pc-sites-module-sheafification-interface` says the underlying abelian sheaf is the abelian sheafification. `lem-pc-sites-sheafification-underlying-sets` identifies its underlying set sheafification. `lem-weil-pbc-site-sheafification-sections-local` supplies both local representatives and local equality. The site definition supplies finite covering refinements. All apply to an arbitrary site, and the fixed universe convention contains the site data. Their conclusions give local lifts from Q to F. If an F section maps to zero, local equality puts it locally in P; the subsheaf axiom then puts it globally in P. A finite tuple lifts simultaneously after finitely many refinements, without claiming sectionwise surjectivity.

Step 9 cites the same 08FC node and the site definition. The lifted relation has error c in P by Step 8; its equation is solvable in F, so Step 6 solves it locally in P. Subtracting gives an actual zero relation in F. Its flatness factorization descends to Q because the subtracted entries vanish there. The coefficient identities descend unchanged, and composition of coverings gives exactly the converse criterion's hypothesis. This establishes quotient flatness independently of any unjustified assertion that a flat subobject has flat quotient.

For edge cases I checked the empty site, zero ring sheaf and zero module sheaf (the nonzero-F assertion is then vacuous); the one-object trivial site over a field (the construction is finite-equation closure of a nonzero vector); empty coverings (the sheaf axiom forces the unique section at the target); repeated arrows (the code counts their common restriction once); and systems with zero equations or unknowns. Empty relations in Steps 7 and 9 use the empty factorization. The zero-generated subpresheaf still has a zero section at each object, accounted for by the infinite bound on objects. These checks expose no false statement or missing hypothesis.

All four generic off-unit sheafification/flatness tools are requested, with reasons, only in `split_report.tool_uses`, for the maintainer to judge. No maintainer-owned field, source checkout, shared project file, compiler, Lake command, excluded SGA route, or other agent was used. The exact source claims and all fifteen quotations were checked against current files, not merely accepted from the inherited report.

## Unfinished work

No mathematical step is left unresolved and no new unsplit node was introduced. The unarchived Recktenwald reference is not a proof input. The next independent reader and eventual delivery remain outside this author's dry-run handoff.

## Second reading by NN

I independently opened the item node, its six statement dependencies, the nine proof steps, `citations.json`, and the Stacks passages named in each step. The item statement agrees clause by clause with the retained agent-formulated bounded-flat-subsheaf input: small site, commutative ring sheaf, fixed-universe size, nonzero tensor-flat sheaf, nonzero bounded subobject, and tensor-flat sheaf quotient. No new node files are present, so B1–B7 and the new-node source/search checks are vacuous; the existing-node searches and blueprint ancestry were nevertheless checked in the repository and the logged Mathlib searches.

Step 1 was checked against the site definition in Tag 00VH and the displayed cardinal coding. The object, morphism, ring-section, repeated-arrow, and empty-cover cases are accounted for; the step uses only elementary cardinal arithmetic and is marked elementary.

Step 2 was checked against the module-sheaf definition and Sections 03CS/03CV. The restriction maps act on both coefficients and generators, and the finite-tuple count gives the claimed bound; it adds no unstated sectionwise-flatness hypothesis.

Step 3 was checked against Tags 00VH and the sheaf axiom in the module definition. Pullback and composition give restriction stability and common refinements, gluing gives local saturation, and the target-plus-arrow-plus-section code gives the cardinal estimate. Empty coverings and repeated arrows were tested explicitly; the displayed estimate remains valid.

Step 4 was checked against the section operations in 03CV and the preceding construction. The finite matrix systems, finite right-hand sides, choice of one ambient solution, inclusion of the prior stage, and cardinal bound are all explicit. The zero-equation and zero-unknown cases cause no exception, and no ordinary sectionwise flatness is used.

Step 5 was checked against the site axioms and Step 3. The increasing countable union is a subpresheaf, local saturation is the sheaf P, and finite tuples are localized to a stage with an index allowed to vary over covering members. This correctly avoids treating the raw countable union as a sheaf.

Step 6 was checked directly against Steps 4–5. After restricting coefficients and right-hand sides to a covering member, the exact restricted system was among those enumerated at the corresponding stage, so its chosen solution lies in P. The step is genuinely elementary from the two cited constructions and introduces no purity terminology.

Step 7 was checked against the complete statement of Tag 08FC (08FC, `lemma-flat-eq`). The matrix with entries from the ambient factorization is the finite system reflected by Step 6; coefficient identities restrict unchanged, and the converse half of 08FC gives flatness of P. The empty relation case was checked.

Step 8 was checked against the module-sheaf cokernel description, Tag 03CY, the underlying-set interface, and Tags 00WB/00WK. Local representatives give lifts, local equality gives kernel membership in P, and finite successive refinements give simultaneous lifts. No sectionwise surjectivity is asserted. The zero quotient and empty-cover cases were checked.

Step 9 was checked against Step 8, Step 6, the site composition axiom, and both directions of 08FC. The lifted relation is corrected by a locally P-valued solution, leaving a zero relation in F; flatness of F then factors it and the factorization descends to Q. Empty tuples and relations were checked.

I searched the whole DAG for the item and its bounded/pure-subsheaf vocabulary, searched the current blueprint for a duplicate, and inspected the existing dependency statements before retaining them. The current blueprint ancestor and `from.place` are recorded in the item. The Mathlib searches in `searches.jsonl` are actual msearch runs; their returned declarations concern ordinary module flatness, generators, finite presentation, or unrelated Kaplansky results, so no Mathlib leaf replaces this item.

Changes made in this second reading: added this step-by-step review section; made no mathematical or node-file changes because every cited statement, hypothesis, edge case, citation quote, and delivery-owned field checked out. The sandbox still contains one existing item node, zero new nodes, and the unchanged first-reader `## Review by NN` section.
