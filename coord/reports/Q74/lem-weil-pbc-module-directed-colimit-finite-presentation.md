# Stage-1 report: lem-weil-pbc-module-directed-colimit-finite-presentation

1. Files written
- dag/nodes/sec-proper-base-change/lem-weil-pbc-module-directed-colimit-finite-presentation.json: statement unchanged; shorter four-step assembly with all equations.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-colimit-cocone-op-limit.json: statement; exact Mathlib leaf IsColimit.op, HasLimits.lean:1054.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-limit-cone-unop-colimit.json: statement; exact Mathlib leaf isColimitCoconeUnopOfCone, Opposites.lean:100.
- citations.json: verbatim statement quotations for every assembly step citation.

2. Attachments: none. The project theorem in lean/Sheaf/AlgebraicGeometry/ModuleDirectedColimitFinitePresentation.lean ends in `by sorry`; the WeilConjectures search found no exact declaration for this item. No finished proof is claimed.

3. WANTED: none.

4. Repair and discrepancies: the released order requires two new nodes and retention of the existing route. Both categorical transports are already proved in Mathlib, so the brief's Mathlib-leaf requirement forces status mathlib, rather than unsplit, for these statement-only extractions. They have no proof steps. The explicit extraction order is the reason to name these transports separately although the old split described its dualization as elementary. No new geometric theorem, duplicate reindexing theorem, or restatement of the item has been invented. The hypotheses, statement dependencies, Lean metadata, and existing review metadata are unchanged.

5. Unfinished work: no unverified mathematical input was added; the existing 01PJ theorem retains its existing proof obligations. This delivery writes no Lean and runs no compiler.

## Review by Q74

I read Properties 01PK (lemma-directed-colimit-finite-presentation, properties.tex:3193-3223), the full statement of 01PJ at 3040-3058, and Categories 0032 (lemma-directed-category-system, categories.tex:2710 onward), especially its duality sentence. I read the chapter and unit records and the current main-20261015 constructible-representation proof. This is the module approximation subargument inherited through the recorded ancestor; no unit-level route changes. I checked the two new statements against Mathlib's actual proofs at HasLimits.lean:1054-1065 and Opposites.lean:100-108. The first constructs the unique limit lift by taking the opposite of the colimit desc; the second constructs the colimit desc by removing opposite signs from the limit lift. Each universal property is stated in full with all objects introduced. Smallness is required only of the index; the target category need not be small and needs no independent completeness assumption.

Step 1 cites the existing 01PJ node. I read its statement: it supplies the small filtered category, each finite-presentation module, the compatible legs and the colimit witness, exactly as used. Its hypotheses are the item's qcqs X and quasi-coherent F; no finite-type assumption on F is introduced.

Step 2 cites the new forward leaf. Its statement is about an arbitrary diagram M:J to C and a given colimit cocone, so it applies with J=I and C=Mod(O_X). I wrote the three reversed filteredness conditions explicitly; they prove cofilteredness by definition. The cone vertex is F^op, and its legs point from F^op to M(x)^op. No existence assertion is substituted for the given colimit witness.

Step 3 cites the existing cofiltered-limit-directed-reindex node. I read its full statement, including retention of the same vertex and legs. It applies because I^op is small and cofiltered and step 2 supplies the required limiting cone in Mod(O_X)^op. Its arrows x_b to x_a in I^op are psi_ba:x_a to x_b in I; its composition equation therefore becomes psi_cb psi_ba=psi_ca. The selected inverse-system maps are exactly M(psi_ba)^op, with no arbitrary transition choices.

Step 4 cites the new unop leaf with A the directed index, C=Mod(O_X), and D=E. E has domain A^op and codomain C^op, exactly the leaf's hypotheses, even though E need not be syntactically an opposite of a pre-existing functor. Its unop diagram has precisely the modules and transitions stated in the item. I checked identity, composition and cocone equations explicitly and retained them in the assembly. Finite presentation is inherited from step 1 by selecting its objects. The final witness is a colimit in the full module-sheaf category, not merely its quasi-coherent subcategory.

B-E self-check: both new nodes have no proof or proof dependencies, complete quantified statements, TeX, actual source labels and tags, blueprint ancestry, and logged searches. No hollow definitions or new notions are introduced: opposite categories and cones are spelled out, and the existing colimit definition is cited. The Mathlib hits were read rather than inferred from names. All four assembly uses have verbatim quotes in citations.json. There is no dependence from a new leaf back to the item. No step exceeds 2000 characters. For J empty, the forward statement correctly converts an initial object into a terminal object of the opposite category, and the inverse statement converts a terminal object in C^op into an initial object in C; both assume those witnesses. For a singleton identity category both are the same universal property with arrows reversed. For a directed preorder already indexing M, the selected system has the same identity and composition laws. The empty scheme and zero module satisfy the same 01PJ hypotheses. No statement dispute was found.

The search was run through msearch only and is in searches.jsonl. The first phrasing found the exact forward theorem immediately; the inverse phrasing found isColimitCoconeUnopOfCone, whose full source handles arbitrary opposite-valued diagrams. The existing item's historical searches were retained and current semantic, Loogle and grep results added. The blueprint search for colimit cocone, limit cone and finite presentation directed found no ordinary-category statement equal to either leaf. The DAG search also found no existing generic opposite transport node. Generic directed reindexing already exists and was reused, not duplicated.

## Argument preservation

The old step 1 remains the 01PJ invocation. The forward universal-property argument of old step 2 is the new forward leaf (the chosen lift is the opposite of the unique factorization of the compatible family); small/cofiltered reversal remains explicit in assembly step 2. Old step 3's entire reindexing invocation, arrow orientation and inverse-limit witness remain in assembly step 3; its conversion back to a colimit is now the new unop leaf. All of old step 4's assignments, finite presentation and three equations remain in assembly step 4. The old explanation that global colimit existence is unnecessary remains in the assembly. For precise comparison, here is the original argument verbatim:

Old step 1:

*Step 1 (the filtered diagram).* By [lem-weil-pbc-module-filtered-colimit-finite-presentation] (Properties 01PJ; $X$ is qcqs and $\mathcal F$ quasi-coherent) there are a small filtered category $\mathcal I$, a functor $M:\mathcal I\to\Mod(\mathcal O_X)$ with every $M(x)$ of finite presentation, and maps $\varphi_x:M(x)\to\mathcal F$ with $\varphi_y\circ M(a)=\varphi_x$ for $a:x\to y$, such that $(\mathcal F,(\varphi_x)_x)$ is a colimit of $M$.

Old step 2:

*Step 2 (dualize).* The opposite category $\mathcal I^{\rm op}$ is small and cofiltered (the three conditions of filteredness for $\mathcal I$ [def-weil-pbc-category-colimit] read in $\mathcal I^{\rm op}$ are the three conditions of cofilteredness: nonempty, any two objects receive morphisms from a common object, any two parallel morphisms are equalized on the source side). Let $\mathcal C=\Mod(\mathcal O_X)^{\rm op}$ and $D=M^{\rm op}:\mathcal I^{\rm op}\to\mathcal C$. A family $g_x:T\to D(x)$ in $\mathcal C$ with $D(a)\circ g_x=g_y$ is a family $M(x)\to T$ in $\Mod(\mathcal O_X)$ compatible with the $M(a)$, so the colimit property of $(\mathcal F,(\varphi_x))$ (Step 1) says exactly that $(\mathcal F,(\varphi_x^{\rm op}:\mathcal F\to D(x))_x)$ is a limit cone of $D$ in $\mathcal C$ in the sense of [lem-weil-pbc-cofiltered-limit-directed-reindex] (a limit in $\mathcal C$ is a colimit in $\mathcal C^{\rm op}=\Mod(\mathcal O_X)$). This is the definition read in the opposite category.

Old step 3:

*Step 3 (reindex by a directed set: Categories 0032).* By [lem-weil-pbc-cofiltered-limit-directed-reindex] (Categories, Lemma 0032, Mathlib `IsFiltered.exists_directed` with `Functor.Final`; applied to the small cofiltered category $\mathcal I^{\rm op}$, the category $\mathcal C=\Mod(\mathcal O_X)^{\rm op}$, $D=M^{\rm op}$ and the limit cone of Step 2) there are a nonempty directed set $(A,\le)$, objects $x_a$ of $\mathcal I$ ($a\in A$) and morphisms $x_b\to x_a$ of $\mathcal I^{\rm op}$, i.e. morphisms $\psi_{ba}:x_a\to x_b$ of $\mathcal I$ ($a\le b$), with $\psi_{aa}=\mathrm{id}$ and $\psi_{cb}\circ\psi_{ba}=\psi_{ca}$ ($a\le b\le c$), such that $(\mathcal F,(\varphi_{x_a}^{\rm op})_{a\in A})$ is a limit in $\mathcal C$ of the inverse system $(D(x_a),D(\psi_{ba}^{\rm op}))$; read back in $\Mod(\mathcal O_X)$ as in Step 2, $(\mathcal F,(\varphi_{x_a})_{a\in A})$ is a colimit of the system $(M(x_a),M(\psi_{ba}))_{a\le b}$ over $A$. (Stacks also invokes the existence of colimits in $\Mod(\mathcal O_X)$; it is not needed here, since the cited lemma transfers the colimit property itself, Mathlib `Functor.Final.isColimitWhiskerEquiv`.)

Old step 4:

*Step 4 (conclusion).* Put $I=A$, $\mathcal F_a=M(x_a)$, $\varphi_{ba}=M(\psi_{ba})$ for $a\le b$, and $\varphi_a=\varphi_{x_a}$. Each $\mathcal F_a$ is of finite presentation (Step 1); $\varphi_{aa}=M(\mathrm{id})=\mathrm{id}$ and $\varphi_{cb}\varphi_{ba}=M(\psi_{cb}\psi_{ba})=\varphi_{ca}$ by functoriality of $M$; $\varphi_b\circ\varphi_{ba}=\varphi_{x_b}\circ M(\psi_{ba})=\varphi_{x_a}=\varphi_a$ by the cocone property of Step 1; and $(\mathcal F,(\varphi_a))$ is a colimit of the system [def-weil-pbc-category-colimit] by Step 3. This is the statement.

## Not duplicates

lem-weil-pbc-colimit-cocone-op-limit vs lem-coef-cardinal-filtered-poset-reindex: the existing node constructs a directed/final reindexing; this leaf changes variance of a given cone or cocone without changing or replacing its index.

lem-weil-pbc-colimit-cocone-op-limit vs lem-pc-chosen-module-flat-proper-stage: the existing statement concerns Eventual flatness and proper support for one chosen module; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-pc-flat-module-descent-preorder-stage: the existing statement concerns Flatness descends to one stage of a directed preorder; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-pc-flat-module-descent-preorder: the existing statement concerns Flat-module descent over a directed preorder in arbitrary cartesian models; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-pc-filtered-cartesian-flat-complex-descent: the existing statement concerns Flat complex descent from a fixed cartesian model; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-pc-filtered-cartesian-perfect-descent: the existing statement concerns Perfect descent refining a fixed cartesian model; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-pc-chosen-complex-flat-proper-refinement: the existing statement concerns Common flat proper refinement of an already chosen complex; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-filtered-colimit-normal-ring-integrally-closed: the existing statement concerns Integral-closedness part of Stacks Tag 037D.; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-module-directed-colimit-finite-presentation: the item constructs finite-presentation module approximations on a qcqs scheme; this leaf only reverses a given universal property in arbitrary categories and constructs no approximation or directed index.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-colimit-rings-flat: the existing statement concerns Flatness over a filtered colimit of rings; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-cofiltered-limit-directed-reindex: the existing node constructs a directed/final reindexing; this leaf changes variance of a given cone or cocone without changing or replacing its index.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-affine-closed-henselian-ring-presentation: the existing statement concerns Affine closed henselian ring presentation; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-filtered-colimit-rings-zero: the existing statement concerns Equality and vanishing in a filtered colimit of rings; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs def-weil-pbc-finite-stage-pair-category: the existing statement concerns Finite-stage pair category; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-filtered-colimit-normal-ring-domain: the existing statement concerns Domain part of Stacks Tag 037D.; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs prop-weil-pbc-common-stage-calculus: the existing statement concerns Common-stage additive and shift calculus; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-filtered-colimit-modules-elementwise: the existing statement concerns Elements, equality and vanishing in a filtered colimit of modules; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-cofiltered-etale-cohomology-cocone: the existing statement concerns Cohomology colimit cocone of a cofiltered system over a fixed scheme; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-filtered-category-exists-directed-final: the existing node constructs a directed/final reindexing; this leaf changes variance of a given cone or cocone without changing or replacing its index.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-filtered-category-directed-cofinal: the existing node constructs a directed/final reindexing; this leaf changes variance of a given cone or cocone without changing or replacing its index.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-cofiltered-fixed-base-cohomology-continuity: the existing statement concerns Continuity of a supplied fixed-base cohomology cocone; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-filtered-colimit-normal-ring: the existing statement concerns A filtered colimit of normal rings is normal; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-global-sections-limit-comparison: the existing statement concerns Global sections of a fixed pullback sheaf at cofiltered limits; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-etale-complex-first-page-reindexing: the existing node constructs a directed/final reindexing; this leaf changes variance of a given cone or cocone without changing or replacing its index.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-fixed-base-cohomology-class-descent: the existing statement concerns Descent of a fixed-base cohomology class at an inverse limit; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-cofiltered-etale-cohomology-continuity: the existing statement concerns Ordinary etale continuity for small cofiltered categories; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-etale-complex-abutment-presentations: the existing statement concerns Functorial etale complex abutment presentations; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-coef-cardinal-filtered-poset-reindex: the existing node constructs a directed/final reindexing; this leaf changes variance of a given cone or cocone without changing or replacing its index.

lem-weil-pbc-limit-cone-unop-colimit vs lem-pc-chosen-module-flat-proper-stage: the existing statement concerns Eventual flatness and proper support for one chosen module; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-pc-flat-module-descent-preorder-stage: the existing statement concerns Flatness descends to one stage of a directed preorder; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-pc-flat-module-descent-preorder: the existing statement concerns Flat-module descent over a directed preorder in arbitrary cartesian models; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-pc-filtered-cartesian-flat-complex-descent: the existing statement concerns Flat complex descent from a fixed cartesian model; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-pc-filtered-cartesian-perfect-descent: the existing statement concerns Perfect descent refining a fixed cartesian model; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-pc-chosen-complex-flat-proper-refinement: the existing statement concerns Common flat proper refinement of an already chosen complex; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-filtered-colimit-normal-ring-integrally-closed: the existing statement concerns Integral-closedness part of Stacks Tag 037D.; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-module-directed-colimit-finite-presentation: the item constructs finite-presentation module approximations on a qcqs scheme; this leaf only reverses a given universal property in arbitrary categories and constructs no approximation or directed index.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-colimit-rings-flat: the existing statement concerns Flatness over a filtered colimit of rings; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-cofiltered-limit-directed-reindex: the existing node constructs a directed/final reindexing; this leaf changes variance of a given cone or cocone without changing or replacing its index.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-affine-closed-henselian-ring-presentation: the existing statement concerns Affine closed henselian ring presentation; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-filtered-colimit-rings-zero: the existing statement concerns Equality and vanishing in a filtered colimit of rings; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs def-weil-pbc-finite-stage-pair-category: the existing statement concerns Finite-stage pair category; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-filtered-colimit-normal-ring-domain: the existing statement concerns Domain part of Stacks Tag 037D.; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs prop-weil-pbc-common-stage-calculus: the existing statement concerns Common-stage additive and shift calculus; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-filtered-colimit-modules-elementwise: the existing statement concerns Elements, equality and vanishing in a filtered colimit of modules; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-cofiltered-etale-cohomology-cocone: the existing statement concerns Cohomology colimit cocone of a cofiltered system over a fixed scheme; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-filtered-category-exists-directed-final: the existing node constructs a directed/final reindexing; this leaf changes variance of a given cone or cocone without changing or replacing its index.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-filtered-category-directed-cofinal: the existing node constructs a directed/final reindexing; this leaf changes variance of a given cone or cocone without changing or replacing its index.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-cofiltered-fixed-base-cohomology-continuity: the existing statement concerns Continuity of a supplied fixed-base cohomology cocone; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-filtered-colimit-normal-ring: the existing statement concerns A filtered colimit of normal rings is normal; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-global-sections-limit-comparison: the existing statement concerns Global sections of a fixed pullback sheaf at cofiltered limits; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-etale-complex-first-page-reindexing: the existing node constructs a directed/final reindexing; this leaf changes variance of a given cone or cocone without changing or replacing its index.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-fixed-base-cohomology-class-descent: the existing statement concerns Descent of a fixed-base cohomology class at an inverse limit; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-cofiltered-etale-cohomology-continuity: the existing statement concerns Ordinary etale continuity for small cofiltered categories; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-limit-cone-unop-colimit vs lem-weil-pbc-etale-complex-abutment-presentations: the existing statement concerns Functorial etale complex abutment presentations; this leaf asserts only ordinary-category opposite transport of a given universal property, with no ring, scheme, module descent, cohomology, or spectral-sequence data.

lem-weil-pbc-colimit-cocone-op-limit vs lem-weil-pbc-limit-cone-unop-colimit: the first starts with a covariant diagram and its colimit and produces the opposite limiting cone; the second starts with an arbitrary opposite-indexed, opposite-valued diagram and its limit and produces the unop colimit. They are the two directional transport interfaces, realized by distinct Mathlib declarations, used on different diagrams on either side of the reindexing.

## Returned-delivery repair: current citation revalidation

The maintainer's single return point was that the statement of lem-weil-pbc-module-filtered-colimit-finite-presentation changed after the reviewed delivery. The first required dry run reproduced this precisely: the old step-1 quotation was no longer verbatim. I compared that retained quotation with the current statement in the shared read clone. The changes replace the combined scheme-conventions citation by def-weil-pbc-quasi-compact-scheme and def-weil-quasi-separated-morphism, and add def-weil-pbc-module-finite-type-presentation beside the same local presentation formula. The filtered category, its smallness and three filteredness conditions, the functor, the finite-presentation objects, the compatible maps, and the colimit conclusion are unchanged.

I opened the three definition statements: quasi-compactness is the finite-subcover condition on the underlying space; a quasi-separated scheme is one whose map to Spec Z has quasi-compact diagonal; finite presentation is locally the cokernel of a map between finite free modules. These are the item's existing hypotheses and its displayed local exact sequence. In particular, the convention node's correction of finite presentation for scheme morphisms is irrelevant here: this argument uses finite presentation of module sheaves. I reread Properties 01PJ and 01PK at their labels, whose hypotheses and conclusions agree with this use. I changed assembly step 1 to spell out that hypothesis match, and replaced its quotation with the current statement verbatim. This is a content and citation repair, not an unchanged re-push. The delivery tool constructs the rebased commit on current main.

I also reread every other cited statement. The retained step-3 quotation still equals the current directed-reindexing statement, including the same vertex and selected legs, and both step-2 and step-4 quotations still occur verbatim in the retained Mathlib leaves. I reread HasLimits.lean:1054-1065 and Opposites.lean:100-108 and confirmed the stated variance and universal properties. The new leaves, their citations, their logged search results, their blueprint ancestry and the original argument-preservation record are retained. I read searches.jsonl, including the exact theorem hits and the finite-presentation search results; no search question changed, so no search was repeated or invented. The project source search again found no finished attachment; the Sheaf theorem still has a sorry proof. No additional nodes, assumptions or source routes are introduced by this repair. All four citations pass a direct verbatim comparison in the sandbox, and the assembly remains below 3000 characters with each step below 2000. The empty-scheme, zero-module, empty-category and singleton-category checks in the Q74 review still apply.
