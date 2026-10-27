# Q11 stage-1 repair: lem-trf-nodal-family-noetherian-approximation

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nodal-family-noetherian-approximation.json`: split item, statement unchanged; five assembly steps, 2713 proof-text characters.
- `dag/nodes/sec-trace-formula/lem-trf-nodal-limit-lci-pure-stage.json`: statement, unsplit, no Mathlib match; carries returned steps 3--4 (2376 characters of argument).
- `dag/nodes/sec-trace-formula/lem-trf-first-fitting-unramified-finite-stage.json`: statement, unsplit, no Mathlib match; carries returned steps 5--6 (1874 characters of argument).
- `dag/nodes/sec-trace-formula/lem-trf-lci-unramified-singular-nodal-recognition.json`: statement, unsplit, no Mathlib match; carries returned step 7 (1005 characters of argument).
- `citations.json`: one exact, complete statement quotation per use in each parent step.
- `report.md`: this report and the full retained arguments below. Search outputs and exact command log are retained as sandbox support files.

## Attachments

None. I searched the project under lean/WeilConjectures for the item tag, approximation/nodal terms, Fitting, syntomic, and local complete intersections. No declaration there states this item or the three new assertions with a completed proof. The corresponding live Sheaf.TraceFormula.NodalFamilyNoetherianApproximation theorem ends in `sorry`, so it is not an attachment. Its statement and eight-part docstring agree with the returned natural-language item; no Lean file was changed or compiled.

## WANTED

None: all sources used are present in literature/stacks-project.

## What was wrong and what changed

The human's return requires spreading the 7848-character argument across new statement-only nodes. This is a decomposition repair, not a change to the theorem. The sandbox initially contained only launcher markers, with no retained node, report, citations, or search log. The initial required dry run exited with “no node files”. I therefore copied the current returned node into the sandbox, retained all its statement, provenance, blueprint fields, old searches, and audit metadata, and used its eight proof steps as the repair baseline. No repository or launcher file was written and no git command was run manually.

Returned steps 1--2 and the final assembly of step 8 remain in the parent; the three new lemmas allocate the other five steps as indicated above. Their sizes are comparable mathematical tasks, rather than a new node which contains the whole theorem. Each has its own introduced base system or family, all hypotheses, and a definite conclusion. All have status unsplit, proof [], proof_deps [], and proof_origin null. In particular the new nodes contain no proof sketch disguised as a statement. The complete old arguments are copied below, to preserve rather than erase the mathematical work that future workers must formalize.

A minor prose correction is recorded for the future proof of the first new lemma: the restricted geometric fibre in old step 3 is an open subscheme of the original fibre, not necessarily the whole fibre. The parent step 1 already proves the needed inheritance; the new lemma is applied to this restricted family. This does not change any statement. The parent step 2 removes repeated notation but retains model existence, qcqs, finite presentation, tail limits, and the explicit finite-generators argument.

The three sources were read in the local TeX, with tags verified against tags/tags. The first is Curves 0C5F (lemma-descend-nodal-family), first paragraph, using 0C4E (lemma-nodal-lci), Limits 0C3L (lemma-descend-syntomic), Limits 0EY2 (lemma-descend-dimension-d), and fibre-dimension base change. The second is Divisors 0C3I (lemma-base-change-and-fitting-ideal-omega) and the final paragraph of Curves 0C5F using Limits 0C4W (lemma-descend-unramified). The third is the reverse implication of Curves 0C59 (lemma-nodal-family), Curves 0C4E, Divisors 0C3K (lemma-d-fitting-ideal-omega-smooth), and Morphisms 02G7 (lemma-unramified-over-field). For the parent I read the first proof, first paragraph of Curves 0CBY (lemma-etale-local-structure-nodal-family). No SGA source is used.

## Unfinished work

The three new nodes intentionally await their own workers; they are delivered statement-only as the return requires. There is no unresolved mathematical gap in the parent's assembly relative to the stated dependencies. Validation and delivery results are appended after running the required server-side tools.

## Review by Q11

I read sections B--E of delivery-errors.md and checked the statements, not merely the presence of dependency IDs. The parent's statement is byte-for-byte unchanged. Its source route remains the inherited historical nodal local-equation branch: this delivery does not alter the unit's current contracting-correspondence proof, the chapter, the unit record, or any target.

In parent step 1, the affine-basis lemma gives an affine neighbourhood inside the chosen inverse image, and the factorization lemma actually supplies the restricted morphism. Flatness and local finite presentation are local as their definition nodes state. Open geometric fibres retain their local rings and their completed node rings; purity uses the irreducible locally-algebraic dimension lemma on the components. The smooth-restriction lemma's clause (b) is exactly the direction needed to retain nonsmoothness of x. I have not taken base-change or smoothness theorems from a definition node.

In parent step 2, the integer-subalgebra inverse-system node states both finite type of each stage and its affine transitions. The qcqs permanence lemma makes the affine restricted morphism finitely presented, preserves finite presentation under base change, and supplies qcqs of the model schemes. Clause (1) of thm-pd-spreading-out supplies the model, with its qcqs-base hypotheses met by the affine stages. The scheme-over-limit statement includes the directed tail and the limit of the pulled-back model. The last finite-type assertion is the written algebra argument: finitely many generators for a chart over a finitely generated integer algebra, together with the base generators, generate it over the integers.

In parent step 3, the first new lemma assumes exactly the nodal geometric-fibre hypothesis inherited in step 1, for every algebraically closed field and every geometric-point map, not just a chosen algebraic closure of a residue field. Step 2 verifies its finite presentation, qcqs, and affine-transition hypotheses. Its conclusion supplies flatness, local finite presentation, ordinary purity, geometric purity and geometric local complete intersections simultaneously on a directed tail. Its argument includes the previously explicit ordinary/geometric purity comparison; it is not just a relabelled invocation of the lci descent node.

In parent step 4, the existing nodal-family-fitting-singular node actually concludes that Sing(h) maps unramified to the limit base. I use that conclusion only after the restricted family has its nodal hypotheses. The second new lemma then applies to the finitely presented finite-type-integer model from step 2; it explicitly identifies the first-Fitting subschemes under every base change and concludes finite-stage unramifiedness. It has no nodality hypothesis, so this step does not assume that the finite-stage family is already nodal. Its future proof must check finite type and qcqs of the singular scheme; the full old quotient-algebra and Noetherian argument is retained below. It does not infer finite presentation of an arbitrary closed immersion over a non-Noetherian base.

In parent step 5, d is at least c, so the first new lemma's entire tail conclusion applies at d. The third new lemma requires flatness, local finite presentation, pure geometric dimension one, geometric local complete intersections and unramifiedness of the first-Fitting subscheme. These are precisely steps 2--4. Its conclusion covers EVERY nonsmooth geometric-fibre point, not just closed points: its argument must use the smooth-locus identification and discreteness of an unramified scheme over a field to establish closedness before using the closed-point curve criterion. After nodality has been established, the existing nodal-family-fitting-singular theorem applies to f_0 and identifies its pullback with Sing(h), with both underlying nonsmooth loci. The image of the chosen nonsmooth point lies in Sing(f_0), proving the final nonsmoothness assertion. Associativity of the Cartesian identifications is just the fibre-product universal property already in the statement's definitions.

For the new statements I checked all three common pitfalls. The first new lemma is an intermediate nodal-to-lci-and-purity descent argument, with no nodal finite-stage conclusion, no unramified singular locus, and no local chart. The second proves generic Fitting formation plus descent for the closed subscheme without assuming nodality or flatness; this cannot be replaced by the existing forward nodal-family theorem. The third is relative recognition from lci and unramifiedness, including the passage from closed points to all nonsmooth points. The existing field-curve criterion only quantifies over closed points and does not by itself state this relative assertion. None of the new lemmas restates the approximation theorem or introduces the whole theorem under a new name.

I tested the empty fibre and empty total space in the new lemmas: their fibre conditions are vacuous and the first-Fitting scheme of the empty source is empty; nothing forces nonemptiness. For a constant inverse system, the requested stage can be the original stage. For a smooth pure-dimensional curve the singular scheme is empty and recognition imposes no completed-ring condition. For the nodal curve uv=0 over an algebraically closed field, the first-Fitting ideal is (u,v), whose point is unramified; the recognition assertion recovers the node. For a cusp v^2-u^3 over characteristic zero, the first-Fitting singular scheme is nonreduced and unramifiedness fails, as required. A smooth zero-dimensional fibre fails the pure-dimension-one hypothesis, and higher-dimensional smooth families likewise cannot enter recognition. No excellence assumption, properness, connectedness, or nonemptiness has been smuggled in.

I searched the whole DAG by tags and concepts and the whole imported blueprint using blueprint_refs search for nodal, complete intersection, unramified, Fitting, pure dimension and finite presentation; no blueprint node states any new assertion. The blueprint ancestor and via list are inherited, with the item prepended for each new node. Relevant old assertions are compared below. The mandatory command was used for every new-node Mathlib query: LeanFinder twice in different words, LeanSearch, Loogle and source grep. All outputs are retained verbatim in search-results and the node records use the exact query text from searches.jsonl. The services returned real answers. Loogle's two unknown-identifier responses are described as such, not treated as substantive absence evidence. LeanFinder/LeanSearch and the source grep give no exact or one-line-specialization match. I opened the returned smooth-relative-dimension definitions, unramified locus, local-flat-descent instances, and affine-transition-limit morphism-equality results: none states a Fitting singular scheme, a nodal criterion, or syntomic pure-dimension limit descent. Fitting decomposition for Artinian modules is a different notion from Fitting ideals.

The new nodes have no proof steps longer than 2000 characters, or any proof steps at all. No parent step exceeds 2000 characters. The long returned step-3--4 argument has been allocated to a distinct queued lemma with its own hypotheses and conclusion; it has not been hidden in a longer assembly step.

## Not duplicates

lem-trf-first-fitting-unramified-finite-stage vs def-trf-first-fitting-singular-subscheme: defines the subscheme and localization convention; it supplies neither arbitrary base-change comparison nor unramified descent or recognition.

lem-trf-first-fitting-unramified-finite-stage vs lem-trf-nodal-family-fitting-singular: assumes the whole family already nodal and proves the forward singular-locus properties; the new assertions respectively prepare lci fibres, work without nodality, or prove the reverse recognition direction.

lem-trf-first-fitting-unramified-finite-stage vs lem-trf-nodal-family-noetherian-approximation: constructs an integer-finite-type nodal model around a specified nonsmooth point; each new assertion is a strictly intermediate argument and none gives that model.

lem-trf-first-fitting-unramified-finite-stage vs lem-trf-unramified-limit-descent: takes an existing qcqs locally-finite-type morphism; it does not construct or base-change the Fitting closed subscheme or verify its qcqs hypotheses.

lem-trf-lci-unramified-singular-nodal-recognition vs def-trf-first-fitting-singular-subscheme: defines the subscheme and localization convention; it supplies neither arbitrary base-change comparison nor unramified descent or recognition.

lem-trf-lci-unramified-singular-nodal-recognition vs def-trf-nodal-geometric-fibres: is a definition requiring nonempty connected fibres, and supplies none of the new theorem conclusions.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-trf-dth-fitting-smooth-locus: identifies the support of a Fitting subscheme with a nonsmooth locus, without lci nodal recognition or finite-stage descent.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-trf-geometric-fibre-unramified-criterion: the existing node concerns Unramifiedness tested on geometric fibres for a locally finite type morphism; it does not state the new combination of family hypotheses and conclusion.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-trf-nodal-curve-lci-criterion: is a field-curve equivalence only at closed points; the new relative assertions must control arbitrary geometric base changes and/or finite stages.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-trf-nodal-family-etale-local-model: constructs an etale uv-h chart around a nonsmooth point; none of the new assertions constructs such a chart.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-trf-nodal-family-fitting-singular: assumes the whole family already nodal and proves the forward singular-locus properties; the new assertions respectively prepare lci fibres, work without nodality, or prove the reverse recognition direction.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-trf-nodal-point-local-criterion: is a local criterion at a preassigned closed point, with residue-field and local-ring hypotheses, rather than a relative family or finite-stage assertion.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-trf-projective-nodal-family-geometry: assumes a projective nodal family over a Noetherian base and gives forward geometry; the new statements do not have projectivity, connectedness or assumed nodality at the finite stage.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-trf-semistable-marked-base-change: is preservation of a marked semistable family under base change, without first-Fitting recognition or descent to finite stages.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-trf-unramified-field-fibre-decomposition: the existing node concerns Unramified schemes over a field are disjoint unions of finite separable spectra; it does not state the new combination of family hypotheses and conclusion.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-trf-unramified-over-field-local-criterion: the existing node concerns Local criterion for a locally finite type scheme to be unramified over a field; it does not state the new combination of family hypotheses and conclusion.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-weil-pbc-unramified-algebra-over-field-product: the existing node concerns An unramified algebra over a field is a finite product of finite separable extensions; it does not state the new combination of family hypotheses and conclusion.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-weil-pbc-unramified-fibre-point-isolated: the existing node concerns A point unramified in a locally finite type morphism is isolated in its fibre; it does not state the new combination of family hypotheses and conclusion.

lem-trf-lci-unramified-singular-nodal-recognition vs lem-weil-pbc-unramified-over-field-discrete: the existing node concerns A scheme unramified over a field is discrete; it does not state the new combination of family hypotheses and conclusion.

lem-trf-nodal-limit-lci-pure-stage vs lem-sc-curve-base-change-relative-dimension-one: the existing node concerns Base changes of a smooth curve are smooth of relative dimension $1$; it does not state the new combination of family hypotheses and conclusion.

lem-trf-nodal-limit-lci-pure-stage vs lem-sc-fibre-dimension-after-base-change: the existing node concerns Fibre dimensions are preserved by base change; it does not state the new combination of family hypotheses and conclusion.

lem-trf-nodal-limit-lci-pure-stage vs lem-trf-complete-intersection-fibres-limit-descent: assumes lci geometric fibres already and supplies no ordinary/geometric pure-dimension conclusion.

lem-trf-nodal-limit-lci-pure-stage vs lem-trf-nodal-curve-lci-criterion: is a field-curve equivalence only at closed points; the new relative assertions must control arbitrary geometric base changes and/or finite stages.

lem-trf-nodal-limit-lci-pure-stage vs lem-trf-nodal-family-noetherian-approximation: constructs an integer-finite-type nodal model around a specified nonsmooth point; each new assertion is a strictly intermediate argument and none gives that model.

lem-trf-nodal-limit-lci-pure-stage vs lem-trf-nodal-point-local-criterion: is a local criterion at a preassigned closed point, with residue-field and local-ring hypotheses, rather than a relative family or finite-stage assertion.

lem-trf-nodal-limit-lci-pure-stage vs lem-trf-pure-relative-dimension-finite-stage: assumes ordinary purity already and supplies no nodal-to-lci or geometric-purity comparison.

lem-trf-nodal-limit-lci-pure-stage vs lem-trf-relative-dimension-base-change: the existing node concerns Pure relative dimension is preserved by base change; it does not state the new combination of family hypotheses and conclusion.

## Full allocation of the returned arguments

These are the complete returned proof texts, not proof fields in the new nodes. The proof obligations and the nodes they use remain visible for the workers who will split them. In the first new lemma, replace old notation g_a by the statement's g_a and h by its limit morphism; the reference to step 1 is discharged by the new lemma's stated hypothesis. In the second, the input unramifiedness of Sing(h) is a hypothesis, supplied by parent step 4. In the third, the input flatness, lci, purity and unramifiedness are hypotheses; the base-change comparison must be proved using the existing differential/Fitting nodes (or the new second lemma's stated comparison).

### Returned step 1 -> parent step 1

Choose an affine open $S^\circ\ni s$ and then an affine open $X^\circ\ni x$ inside $f^{-1}(S^\circ)$ using [lem-weil-pbc-affine-opens-basis]. The restricted morphism $h:X^\circ\to S^\circ$ exists by [lem-weil-pbc-morphism-factors-through-open-subscheme]. Flatness and local finite presentation restrict by their local definitions [def-weil-flat-morphism, def-sbc-locally-finite-presentation]. The geometric fibres of $h$ are open subschemes of those of $f$, so they still have the stipulated completed local rings. They are empty or pure of dimension one: each component is a nonempty open of a component of the original fibre, whose dimension is unchanged by [lem-sc-dimension-locally-algebraic]. Finally $x$ is nonsmooth for $h$, since smoothness of $h$ on a neighbourhood of $x$ would imply smoothness of $f$ there by [lem-weil-pbc-smooth-restrict-open-subschemes](b).

Cited statements: lem-weil-pbc-affine-opens-basis, lem-weil-pbc-morphism-factors-through-open-subscheme, def-weil-flat-morphism, def-sbc-locally-finite-presentation, lem-sc-dimension-locally-algebraic, lem-weil-pbc-smooth-restrict-open-subschemes.

Source: literature/stacks-project/curves.tex, Tag 0CBY, first proof, first paragraph: affine localisation on X and S.

### Returned step 2 -> parent step 2

Write $S^\circ=\operatorname{Spec}A$. By [lemma-nagata-noetherian-inverse-system-affine], it is the inverse limit of the spectra $S_i$ of finitely generated integer subalgebras of $A$, with affine transition morphisms. The affine morphism $h$ is of finite presentation by [lem-weil-pbc-qcqs-morphism-permanence](1). Apply [thm-pd-spreading-out](1) to get a stage $a$, a finitely presented $g_a:X_a\to S_a$, and $X^\circ\cong X_a\times_{S_a}S^\circ$ over $S^\circ$. For $i\ge a$ put $X_i=X_a\times_{S_a}S_i$ and $g_i:X_i\to S_i$. These maps remain finitely presented, and $X_i$ is quasi-compact and quasi-separated, by [lem-weil-pbc-qcqs-morphism-permanence](2)--(3). The system $(X_i)$ has limit $X^\circ$ by [lem-weil-pbc-scheme-over-limit]. Passing to any directed tail retains this same limit, as is also included in that statement. Each $X_i$ is of finite type over $\mathbf Z$: finite-presentation chart algebras are finitely generated over their base chart algebras, and the union of two finite sets of generators generates their composite.

Cited statements: lemma-nagata-noetherian-inverse-system-affine, lem-weil-pbc-qcqs-morphism-permanence, thm-pd-spreading-out, lem-weil-pbc-scheme-over-limit.

Source: literature/stacks-project/curves.tex, Tag 0CBY first proof first paragraph; Limits Tag 01ZM and Tag 01YZ for the models and their limit.

### Returned step 3 -> lem-trf-nodal-limit-lci-pure-stage

For every algebraically closed field $\Omega$ and every geometric point $\operatorname{Spec}\Omega\to S^\circ$, the fibre $C=X^\circ_\Omega$ is a geometric fibre of $f$; if it is nonempty, all its closed points are smooth or nodes by the hypotheses retained in step 1. Apply [lem-trf-nodal-curve-lci-criterion], implication (1)$\Rightarrow$(2), over the algebraically closed field of this fibre. It makes $C$ a local complete intersection. The fibre is locally of finite type since local finite presentation is preserved by base change, [lem-weil-pbc-qcqs-morphism-permanence](3), and its algebra presentations remain finitely generated after dropping relations. Empty fibres are local complete intersections by the empty affine-cover convention. The generic descent result [lem-trf-complete-intersection-fibres-limit-descent], applied to $g_a$ over the given system, now gives $b\ge a$ such that every $g_i$ for $i\ge b$ is flat, locally finitely presented, and has local complete intersection geometric fibres over every algebraically closed field. Its qcqs hypotheses were checked in step 2.

Cited statements: lem-trf-nodal-curve-lci-criterion, lem-weil-pbc-qcqs-morphism-permanence, lem-trf-complete-intersection-fibres-limit-descent.

Source: literature/stacks-project/curves.tex, Tag 0C5F, first proof sentence (Limits Tag 0C3L); the fibrewise interpretation of syntomicity from Tag 0C59 and Morphisms Tag 01UF.

### Returned step 4 -> lem-trf-nodal-limit-lci-pure-stage

The ordinary nonempty fibres of $h$ are pure of dimension one as well. Here is the passage between ordinary and geometric purity that will also be used at finite stages. For a locally finite type scheme over a field, purity of dimension one is equivalent to local topological dimension one at every point: one direction is [lem-sbc-equidimensional-open-local-dimension] with the whole scheme as open; for the converse, at the generic point of each component take an affine neighbourhood and remove the finitely many other components through that chart, then [lem-sc-dimension-locally-algebraic] identifies its local dimension with the dimension of this component. Finiteness of the components of these affine charts is [lem-wf-affine-noetherian-components]. The field-extension projection is surjective by [lem-weil-pbc-surjective-base-change], since the map of one-point field spectra is surjective. Thus every ordinary-fibre point has a lift, and [lem-sc-fibre-dimension-after-base-change] identifies the two local dimensions. The same argument proves geometric purity from ordinary purity. Apply [lem-trf-pure-relative-dimension-finite-stage] to $g_b$ with $d=1$ to find $c\ge b$ such that every $g_i$ for $i\ge c$ has empty or pure-one-dimensional ordinary and geometric fibres.

Cited statements: lem-sbc-equidimensional-open-local-dimension, lem-sc-dimension-locally-algebraic, lem-wf-affine-noetherian-components, lem-weil-pbc-surjective-base-change, lem-sc-fibre-dimension-after-base-change, lem-trf-pure-relative-dimension-finite-stage.

Source: literature/stacks-project/curves.tex, Tag 0C5F dimension-one reduction; Limits Tag 0EY2 (existing pure-dimension descent); Morphisms Tag 02FY and Varieties lemma-dimension-locally-algebraic.

### Returned step 5 -> lem-trf-first-fitting-unramified-finite-stage

Put $Z_c=\operatorname{Sing}(g_c)\hookrightarrow X_c$, the first-Fitting closed subscheme [def-trf-first-fitting-singular-subscheme]. Its formation commutes with every base change, without a nodality hypothesis: on an affine pair $R\to B$ and a base change $R\to R^\prime$, [lem-weil-pbc-fibre-product-affine-spectra] gives $B^\prime=R^\prime\otimes_R B$, [lem-weil-pbc-kahler-differentials-base-change] identifies $\Omega_{B^\prime/R^\prime}=B^\prime\otimes_B\Omega_{B/R}$, and [lem-trf-fitting-ideal-independence-base-change](2) gives $\operatorname{Fit}_1(\Omega_{B^\prime/R^\prime})=\operatorname{Fit}_1(\Omega_{B/R})B^\prime$. The defining ideals therefore identify the closed subschemes and glue. In particular $Z_c\times_{S_c}S_i=\operatorname{Sing}(g_i)$ and $Z_c\times_{S_c}S^\circ=\operatorname{Sing}(h)$.

Cited statements: def-trf-first-fitting-singular-subscheme, lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-kahler-differentials-base-change, lem-trf-fitting-ideal-independence-base-change.

Source: literature/stacks-project/divisors.tex, Tag 0C3I (lemma-base-change-and-fitting-ideal-omega), used in Tag 0C5F; More on Algebra Tag 07ZA(3).

### Returned step 6 -> lem-trf-first-fitting-unramified-finite-stage

The schemes $S_c,X_c,Z_c$ are of finite type over $\mathbf Z$. For $Z_c$ this follows by taking a finite affine cover of $X_c$: the inverse image of each affine is its quotient by the defining ideal, and a quotient of a finitely generated algebra is generated by the images of the same generators. By [lem-weil-pbc-finite-type-over-noetherian] they are Noetherian, hence quasi-compact and quasi-separated. Also $Z_c\to S_c$ is locally of finite type by the same quotient calculation. The limit morphism $\operatorname{Sing}(h)\to S^\circ$ is unramified by [lem-trf-nodal-family-fitting-singular], since $h$ has the required nodal geometric fibres. Step 5 identifies it with the base change of $Z_c\to S_c$. Apply [lem-trf-unramified-limit-descent] to this morphism of qcqs $S_c$-schemes. It gives $d\ge c$ such that $\operatorname{Sing}(g_d)\to S_d$ is unramified. Notice that this descent only requires local finite type for the singular morphism, so it does not assume that an arbitrary closed subscheme of a finitely presented scheme is finitely presented.

Cited statements: lem-weil-pbc-finite-type-over-noetherian, lem-trf-nodal-family-fitting-singular, lem-trf-unramified-limit-descent.

Source: literature/stacks-project/curves.tex, Tag 0C5F, last paragraph, using Limits Tag 0C4W (lemma-descend-unramified).

### Returned step 7 -> lem-trf-lci-unramified-singular-nodal-recognition

We now recover the nodal condition on $g_d$. By steps 3--4 it is flat and finitely presented, and every geometric fibre $C$ is empty or pure of dimension one and a local complete intersection. For a nonempty such fibre over $\Omega$, step 5 identifies its first-Fitting singular scheme $Z_C$ with $\operatorname{Sing}(g_d)\times_{S_d}\operatorname{Spec}\Omega$. It is unramified by [lem-weil-pbc-unramified-base-change-open](1). Implication (2)$\Rightarrow$(1) of [lem-trf-nodal-curve-lci-criterion] therefore makes every closed point of $C$ smooth or a node. To cover every nonsmooth point, [lem-trf-dth-fitting-smooth-locus] with $d=1$ identifies that locus with $|Z_C|$, and [lem-weil-pbc-unramified-over-field-discrete] shows that every point of $Z_C$ is closed in $Z_C$. Since $Z_C$ is closed in $C$, each nonsmooth point is closed in $C$. It is thus a node; with $\Omega$ already algebraically closed, its defining completed-ring condition is exactly $\Omega[[u,v]]/(uv)$. The empty case is vacuous.

Cited statements: lem-weil-pbc-unramified-base-change-open, lem-trf-nodal-curve-lci-criterion, lem-trf-dth-fitting-smooth-locus, lem-weil-pbc-unramified-over-field-discrete.

Source: literature/stacks-project/curves.tex, Tag 0C59, reverse implication, expanded using Tag 0C4E; Divisors Tag 0C3K and Morphisms Tag 02G7.

### Returned step 8 -> parent step 5

Set $S_0=S_d$, $X_0=X_d$, and $f_0=g_d$. Step 2 gives finite type over $\mathbf Z$ and finite presentation; steps 3 and 7 give flatness and the required geometric-fibre condition. The two successive base changes identify $X^\circ\cong X_a\times_{S_a}S^\circ\cong X_d\times_{S_d}S^\circ$ by the fibre-product universal property. Let $x_0$ be the image of $x$. Apply [lem-trf-nodal-family-fitting-singular] to $f_0$: its singular subscheme pulls back to that of $h$, with underlying set the nonsmooth locus. Since $x$ is nonsmooth for $h$, its image lies in $\operatorname{Sing}(f_0)$ and $x_0$ is nonsmooth. All required data and the Cartesian square now have been constructed.

Cited statements: lem-trf-nodal-family-fitting-singular.

Source: literature/stacks-project/curves.tex, Tag 0CBY first proof first paragraph, including retention of the nonsmooth point under approximation.

## Citation audit of the retained subarguments

I opened the statement of every original dependency. Old step 3 uses the curve criterion in its forward direction to obtain geometric lci, qcqs permanence for base change and finite type, and complete-intersection-fibres-limit-descent with its explicit all-algebraically-closed-fields quantifier. Old step 4 uses equidimensional-open-local-dimension in the forward purity comparison and dimension-locally-algebraic after isolating a component in an affine chart; affine-noetherian-components supplies finiteness, surjective-base-change supplies lifts, fibre-dimension-after-base-change supplies the equality at those lifts, and pure-relative-dimension-finite-stage then applies to the ordinary fibres. Old step 5 uses the first-Fitting definition only to name the ideals; fibre-product-affine-spectra and kahler-differentials-base-change give the actual base-change algebra, and fitting-ideal-independence-base-change clause (2) gives the equality of ideals. Old step 6 uses finite-type-over-noetherian after the explicit quotient-algebra argument, the nodal-family-fitting-singular theorem only on the nodal limit family, and unramified-limit-descent only after checking locally finite type and qcqs for the closed subscheme. Old step 7 uses unramified-base-change-open clause (1), the reverse field-curve lci criterion, dth-fitting-smooth-locus with d=1 and flat locally finite presentation, and unramified-over-field-discrete for closedness. A point closed in a closed subscheme is closed in the ambient fibre. This is why closed-point recognition really covers every nonsmooth point. The literal parent citations are in citations.json; no step claims anything merely from a cited definition.
