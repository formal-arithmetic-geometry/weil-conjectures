## Worker report

1. Files written:
- dag/nodes/sec-trace-formula/lem-trf-generic-fibre-geometrically-reduced-open.json: existing statement unchanged; five assembly steps, 2161 characters, status split.
- dag/nodes/sec-trace-formula/lem-trf-generic-flat-reduced-base-model.json: statement, unsplit, no Mathlib match. Reduction and affine generic-flat preparation, with residue-field and fibre identifications.
- dag/nodes/sec-trace-formula/lem-trf-smooth-open-schematic-generic-density.json: statement, unsplit, no Mathlib match. Finite-type fibre finiteness, smooth-open generic density, schematic density and geometric reducedness of its fibres.
- citations.json: one verbatim statement quote per step/node citation.

2. Attachments: none. The named target has no matching declaration in WeilConjectures; the existing Sheaf.AlgebraicGeometry.GenericFibreGeometricallyReducedOpen theorem ends in sorry. It is not an attachment.

3. WANTED: none. All cited Stacks sources are available locally.

4. The return requires spreading the old 6041-character proof into at least two independently claimable tasks of comparable size. This repair creates two statement-only nodes, with empty proof/proof_deps and null proof_origin. The old arguments 1-2 occupy about 1600 characters and 3-5 about 2500 characters. The last field-extension argument already has a more general, proved DAG node, lem-sbc-geometrically-reduced-dominant-descent, created since the original split; reuse is mandatory. Searches initially considered a third child, but it was discarded after this existing node was found. No proof is lost and no duplicate of it is delivered. Each child's statement records its complete interface, including all comparisons needed by the assembly.

The sandbox initially contained only dispatcher marker files, with no node files, searches or report. I copied the current repository item, which still has the returned eight steps and the unchanged statement, and retained all of its source, searches, import and Lean metadata. returned-item.json retains that starting material in the sandbox. No repository or launcher files were written, no git command was run there, and no Lean compiler, Lake or build tool was invoked.

5. Unfinished: the two child proofs are intentionally left to independent stage-1 workers, as the return requires. No mathematical obstruction found. The target statement, chapter, unit and blueprint route are unchanged.

## Review by Q62

I read the item against Stacks more-morphisms.tex Tag 0578 (lemma-geometrically-reduced-generic-fibre), including its reduction, generic-flatness, smooth-locus and final schematic-density paragraphs. I read the chapter sec-trace-formula and unit sk-i-curve-zero: this is a descendant algebraic-geometric input of the existing constructibility/flatification route, not a replacement of the chapter's trace argument. The ancestor remains lem-trf-local-term-locality through the retained via chain. Whole-blueprint searches for 0578, 054M, 056E, smooth locus, schematically dominant, geometrically reduced, generic flat integral affine and schematically dense geometrically reduced found no duplicate of the two new statements.

For the first new node I read the first paragraph of 0578, morphisms.tex Tag 052A (proposition-generic-flatness), and the existing reduction theorem with Tag 054M. The base is only irreducible initially, so applying generic flatness before taking its reduction would be invalid; the new statement explicitly takes an affine open W of Y_red. It also gives that W maps homeomorphically to a nonempty open in Y and induces isomorphisms on residue fields, not merely radicial maps. Quotienting an affine ring by its nilradical leaves each residue field unchanged; associativity of the pullback supplies the stated fibre comparison. Thus no source reduction, generic geometric reducedness assumption, or nontrivial field extension is hidden. Restricting the generic-flat open further to an affine neighbourhood of the generic point keeps flatness and local finite presentation. The generic fibre's finite presentation is verified on the base-changed finite polynomial presentation, as in old step 2.

For the second new node I read 0578's next paragraph, varieties.tex Tag 056V (lemma-geometrically-reduced-dense-smooth-open), morphisms.tex Tag 01V9 (lemma-smooth-at-point, equivalence (1)-(2)), and Tags 056D (lemma-reduced-scheme-theoretically-dense) and 056B (lemma-scheme-theoretic-image-reduced). Its hypotheses supply flatness and local finite presentation for the fibre criterion; generic reducedness follows from the identity field extension. The dense smooth open of the generic fibre lies in the defined union U because each smooth generic-fibre point lifts to a smooth neighbourhood in X. Fibres of the smooth neighbourhoods are geometrically reduced; they cover U_y after every field extension. The node explicitly supplies the otherwise implicit quasi-compactness needed by the density tools: a finite type fibre over a field has a finite affine cover by Noetherian spectra, so descending closed chains stabilize on the whole fibre and every subset is quasi-compact. Open immersions into it are quasi-compact and their diagonals are isomorphisms, hence they are quasi-separated. This is a finiteness conclusion about the fibres, not a separatedness assumption on X or f. These are old steps 3-5 in one separate task, not a statement that geometrically reduced fibres spread to an open of the base.

I read every statement cited by the five assembly steps. Step 1 uses the first new node for its integral affine W, finite type/flat/locally finitely presented pullback and generic fibre comparison. These are all explicit clauses. Step 2 uses the second new node exactly for the generic sheaf injection, geometric reducedness of every U_w and quasi-compactness of open immersions in (X_W)_w. All its hypotheses hold after step 1, including the unchanged generic fibre. Step 3 uses the full statement of lem-trf-schematic-density-generic-fibre-open, whose source I read at Tag 0573 (lemma-scheme-theoretically-dense-generic-fibre). Its generic hypothesis is the same sheaf injection from step 2, not topological density. Its base need only be irreducible and its morphism finite type; both are supplied. Its conclusion is precisely the fibrewise injection used next. Step 4 uses the existing lem-sbc-geometrically-reduced-dominant-descent statement and its proved public helper in lean/Sheaf/AlgebraicGeometry/GeometricallyReducedDominantDescent.lean. With h=j_w and p the fibre structure map, step 2 supplies quasi-compactness and geometric reducedness of h;p, and step 3 supplies the zero kernel. No surjectivity or reducedness of the ambient fibre is assumed. This general tool is the geometric version of the old flat-pullback and nilpotent-section argument; its proof uses flat base change of schematic dominance and reducedness descent after every field extension. I read its source in morphisms.tex Tags 081I and 056B, and Tag 056E (lemma-reduced-subscheme-closure). Step 5 is only the topological image of an open under the supplied homeomorphism and invariance under the supplied field/fibre isomorphisms. It cites the first child's statement again. citations.json copies each exact cited statement, so these are statement uses rather than uses of an unexported proof construction.

I checked delivery-errors B-E individually: both children introduce every object and list definition dependencies; neither contains proof steps or a proof sketch in its statement; TeX is written once; every source gives a Stacks tag and label; their searches were run with msearch.py and the actual outputs retained. Both were searched twice semantically, by Loogle and by source grep; LeanSearch succeeded for the model task and was rate-limited for the smooth task, recorded as unavailable. Hits about smooth-locus definitions, existing flat morphisms, restriction of local finite presentation, reducedness and geometric reducedness do not assert these combined scheme-level constructions. For the discarded third task, searches found an algebraic injective-map descent theorem, but the already existing scheme-level DAG lemma takes priority. No new Mathlib leaf is claimed. Search logs are unchanged records of actual commands, including those for the discarded candidate.

The new preparation task is more than a clause of the item: it assumes no geometric reducedness and concludes no open of geometrically reduced fibres. It isolates the whole base reduction/comparison and generic-flat-model construction. The smooth task assumes flatness and local finite presentation already and stops at generic schematic density and a geometrically reduced open in each fibre, which is insufficient for the target until 0573 is applied. The last portion is not moved to a new restatement: an existing general descent lemma supplies it. No cyclic proof dependency was introduced. No assembly step is longer than 2000 characters; the total is below 3000.

Small cases checked: X empty gives empty fibres and an empty smooth open, with all injections between zero sheaves valid; irreducibility of Y still ensures a nonempty affine W. A nonreduced base Spec(k[epsilon]/epsilon^2) tests the unchanged-residue-field requirement and makes reduction essential. A reduced but geometrically nonreduced algebra k[t]/(t^p-a) over an imperfect field fails the geometric-reducedness premise of the smooth task, so it gives no false smooth-density conclusion. A nilpotent supported outside an open, for example k[x,epsilon]/(x epsilon,epsilon^2) with U=D(x), fails the sheaf-injectivity premise of descent; the target cannot infer reducedness from topological density alone. Schemes need not be separated; only Noetherian fibres and their open immersions enter the quasi-compactness check. Neither child claims all fibres are nonempty or that the base is Noetherian.

Corrections made while reviewing: replaced a nonexistent quasi-compact-morphism definition id with the existing finite-type convention node and an explicit meaning below; removed the would-be third child because the whole DAG contains the proved general dominant-descent result. No statement dispute was found and the parent statement is unchanged. The existing off-unit generic-flat tool is no longer a parent proof dependency; the new preparation task will use it when split. The existing dominant-descent theorem is declared as a generic tool use in split_report, with the old Stacks route preserved.

## Coverage of the returned argument

The complete returned proof is preserved below for the next workers. New task A is lem-trf-generic-flat-reduced-base-model (old 1-2); new task B is lem-trf-smooth-open-schematic-generic-density (old 3-5). Old 6 stays in parent step 3. Old 7-8 are supplied by existing lem-sbc-geometrically-reduced-dominant-descent, applied in parent step 4; the final transfer portion of old 8 is parent step 5. These allocation notes are in the report, not proof sketches inside statement-only nodes.

### Returned step 1

Base change to the reduction $r:Y_{\mathrm{red}}\to Y$. The cited reduction result makes $r$ a homeomorphism and $Y_{\mathrm{red}}$ reduced. It is irreducible because its underlying space is that of $Y$, hence integral by the stated characterization of integrality. Residue fields are unchanged: locally the quotient $R\to R/\sqrt{0}$ induces $(R/\sqrt{0})_{\mathfrak p}/\mathfrak p=\kappa(\mathfrak p)$. Associativity of the fibre product therefore identifies the old and new fibres over every point, including $\eta$. Finite type is preserved by the cited base-change theorem. Any nonempty good open of $Y_{\mathrm{red}}$ corresponds to a nonempty open of $Y$ with exactly the same fibres. It is therefore enough to prove the assertion with $Y$ integral. Restrict further to a nonempty affine open of $Y$; it contains $\eta$, and an open found there is also open in the original base.

Cited nodes: lem-weil-pbc-reduction-universal-homeomorphism, def-weil-pbc-scheme-reduction, def-pc-integral-scheme, def-pc-scheme-fibre, lem-sfb-finite-type-composition-base-change.

### Returned step 2

Apply generic flatness and local finite presentation to $f$ over the integral base. This gives a nonempty open $W\subseteq Y$ on which $f$ is flat and locally of finite presentation. Replace $Y$ by $W$ and $X$ by $X_W$. The generic point remains in $W$, its fibre is unchanged, and finite type persists by base change. These replacements suffice because any nonempty open obtained in $W$ is nonempty open in $Y$. The generic fibre is locally finitely presented: on each affine presentation $A\to A[t_1,\ldots,t_n]/(h_1,\ldots,h_m)$, tensoring with $\kappa(\eta)$ gives $\kappa(\eta)[t_1,\ldots,t_n]/(\bar h_1,\ldots,\bar h_m)$. The affine fibre-product formula identifies these algebras with the fibre charts.

Cited nodes: lem-sbc-generic-flat-finite-presentation, lem-sfb-finite-type-composition-base-change, def-sbc-locally-finite-presentation, lem-weil-pbc-fibre-product-affine-spectra.

### Returned step 3

Record a finiteness fact for every fibre $X_y$, including $X_\eta$. By finite-type base change it is of finite type over the field $\kappa(y)$, so it has a finite affine cover $\operatorname{Spec}B_i$ with each $B_i$ a finite type $\kappa(y)$-algebra. A field is Noetherian, since its only ideals are $0$ and the whole field. The finite-type algebra theorem and the affine-space theorem cited here show that each $\operatorname{Spec}B_i$ is topologically Noetherian. A descending chain of closed subsets of $X_y$ stabilizes after restriction to each of these finitely many affine charts; taking the maximum of the stabilization indices shows that it stabilizes on $X_y$. Thus $X_y$ is topologically Noetherian. Every subset of it is quasi-compact by the cited compactness theorem. In particular every open immersion into $X_y$ is quasi-compact: its inverse image of an affine open is such a subset. It is also quasi-separated, since the diagonal of an open immersion is an isomorphism. These facts will justify both density lemmas below without any quasi-separatedness hypothesis on $f$.

Cited nodes: lem-sfb-finite-type-composition-base-change, def-weil-finite-type-morphism, lem-weil-pbc-finite-type-algebra-noetherian, lem-sc-affine-noetherian-underlying-space, lem-sfb-noetherian-space-compact-subsets.

### Returned step 4

Let $U\subseteq X$ be the union of the open subschemes on which $f$ is smooth. Apply the dense-smooth-locus theorem to the locally finitely presented geometrically reduced $\kappa(\eta)$-scheme $X_\eta$. Its smooth locus is dense. At each point of that locus, the pointwise fibre criterion applies to $f$, because $f$ is flat and locally of finite presentation after step 2. It gives a smooth neighbourhood in $X$. Hence this dense locus lies in $U_\eta$, so $U_\eta$ is dense in $X_\eta$. Also, every $U_y$ is geometrically reduced: it is covered by the fibres of the smooth opens defining $U$; those fibres are geometrically reduced by the smooth-fibre theorem. After any field extension their corresponding opens still cover, and reducedness on an open cover implies reducedness of the whole base-changed $U_y$. This last deduction uses only the cited open-cover criterion.

Cited nodes: lem-pur-geometrically-reduced-dense-smooth-open, lem-trf-smooth-at-point-fibre-criterion, sbc-lem-smooth-geometrically-reduced, lem-trf-reduced-scheme-open-cover, def-pc-geometrically-irreducible.

### Returned step 5

The identity field extension in geometric reducedness shows that $X_\eta$ is reduced. The inclusion $U_\eta\hookrightarrow X_\eta$ has dense topological image by step 4, and is quasi-compact and quasi-separated by step 3. The reduced-target dense-image theorem therefore says that its scheme-theoretic image is all of $X_\eta$. By the kernel description of that image, the sheaf map $\mathcal O_{X_\eta}\to (j_\eta)_*\mathcal O_{U_\eta}$ is injective. Thus $U_\eta$ is scheme-theoretically dense in the sense required by the next step.

Cited nodes: def-pc-geometrically-irreducible, lemma-nagata-reduced-dense-image-schematic, def-nagata-scheme-theoretic-image.

### Returned step 6

Apply the schematic-density spreading lemma to the finite type morphism $f:X\to Y$ and the open $U$ just constructed. Its base is irreducible with generic point $\eta$, and its generic-fibre injectivity hypothesis was proved in step 5. It supplies a nonempty open $V\subseteq Y$ such that $U_y$ is scheme-theoretically dense in $X_y$ for all $y\in V$.

Cited nodes: lem-trf-schematic-density-generic-fibre-open.

### Returned step 7

Fix $y\in V$ and a field extension $L/\kappa(y)$. To verify density after this extension, work on an arbitrary affine open $C=\operatorname{Spec}D\subseteq X_y$. The restriction $U_y\cap C\to C$ is schematically dense by restriction of the injective sheaf map in step 6. It is quasi-compact and quasi-separated by step 3. The affine fibre-product formula identifies $C_L$ with $\operatorname{Spec}(D\otimes_{\kappa(y)}L)$. The field-extension theorem makes $D\to D\otimes_{\kappa(y)}L$ faithfully flat, hence flat; the flat affine criterion then makes $C_L\to C$ flat. Apply flat pullback of dense images to obtain that $(U_y\cap C)_L\to C_L$ has scheme-theoretic image $C_L$. By the image-kernel description, this means that its structure-sheaf map is injective. Its source is an open of $(U_y)_L$, which is reduced by step 4.

Cited nodes: lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-field-extension-base-change-faithfully-flat, lem-weil-pbc-flat-ring-map-iff-flat-affine, lemma-nagata-dense-flat-pullback, def-nagata-scheme-theoretic-image, def-pc-reduced-scheme.

### Returned step 8

For any open $T\subseteq C_L$, a nilpotent section of $\mathcal O_{C_L}(T)$ maps to a nilpotent section on $T\cap (U_y\cap C)_L$. That section is zero because the open source is reduced. Injectivity from step 7 forces the original section to be zero. Hence $C_L$ is reduced by the section-wise definition. The affine opens $C$ cover $X_y$, so their pullbacks $C_L$ cover $(X_y)_L$, and the open-cover criterion proves that $(X_y)_L$ is reduced. Since $L/\kappa(y)$ was arbitrary, $X_y$ is geometrically reduced. This holds for every $y\in V$. The reductions in steps 1 and 2 transfer this same nonempty good open back to the original base. Empty fibres cause no exception: their sections have no nonzero nilpotents and all the covering/injectivity arguments are vacuous.

Cited nodes: def-pc-reduced-scheme, lem-trf-reduced-scheme-open-cover, def-pc-geometrically-irreducible.

## Not duplicates

lem-trf-smooth-open-schematic-generic-density vs lem-trf-smooth-fibre-affine-ring-at-prime: the existing node assumes a supplied smooth neighbourhood of one fibre point and concludes smoothness of the affine fibre algebra A tensor_R kappa(p) at its kernel prime. Our node assumes a flat locally finitely presented finite type family with geometrically reduced generic fibre and concludes a global relative smooth open with schematically dense generic fibre, Noetherian fibre spaces and geometrically reduced open fibres. The local ring comparison neither constructs that open nor proves either density conclusion or the fibre finiteness; it can be a dependency of the future smooth-point proof, not a replacement of this task.

lem-trf-generic-flat-reduced-base-model vs lem-sbc-affine-reduction-preparation: requires an affine source and constructs a reduced replacement of the source; our source is arbitrary finite type and its actual pullback fibres are unchanged.

lem-trf-generic-flat-reduced-base-model vs lem-sbc-generic-radicial-geometrically-reduced-model: assumes an affine source and geometrically irreducible generic fibre and changes source/base to arrange geometric reducedness; our model keeps every fibre over identical residue fields and needs none of those premises.

lem-trf-generic-flat-reduced-base-model vs lem-sbc-radicial-generic-reduced-preparation: requires an affine source and geometrically irreducible generic fibre, changes the source and lacks flatness; our statement constructs a flat actual pullback with all fibres identified.

lem-trf-generic-flat-reduced-base-model vs lem-sbc-geometric-generic-cover-spread: spreads a supplied finite field cover and its closed subsets; it does not give a reduction model with unchanged fibres.

lem-trf-generic-flat-reduced-base-model vs lem-sbc-generic-closed-subset-fibre-nonempty: spreads nonemptiness of a closed subset; it does not construct the generic-flat reduction model.

lem-trf-generic-flat-reduced-base-model vs lem-sbc-affine-chart-generic-flatness: already assumes affine source and integral affine base and concludes only flatness after localization; our statement handles a nonreduced irreducible base, arbitrary finite type source, and fibre identifications.

lem-trf-generic-flat-reduced-base-model vs lem-sbc-generic-flatness: assumes the base integral and gives only flatness, without the reduction/residue-field/fibre comparison interface.

lem-trf-generic-flat-reduced-base-model vs lem-sbc-generic-flat-finite-presentation-lfp: assumes an integral base and only supplies local finite presentation; it does not construct the reduction model or compare fibres.

lem-trf-generic-flat-reduced-base-model vs lem-sbc-generic-flat-finite-presentation: assumes an integral base; our separate task constructs the integral affine reduction model from an irreducible base and supplies the residue-field and fibre identifications. This existing theorem is an input for that future proof, not the statement of the whole task.

lem-trf-generic-flat-reduced-base-model vs lem-sbc-generic-fibre-incidence-spread: constructs closed irreducible generic covers and spreads incidence data, not a flat reduction model with isomorphic fibres.

lem-trf-generic-flat-reduced-base-model vs lem-trf-simultaneous-proper-generic-flattening: assumes an integral Noetherian base and proper maps and constructs blowups and strict transforms; our base need not be Noetherian and the source is the actual pullback.

lem-trf-generic-flat-reduced-base-model vs lem-trf-generic-fibre-geometrically-reduced-open: the parent concludes an open of geometrically reduced whole fibres; this child instead gives a reduction model without a geometric-reducedness premise or conclusion.

lem-trf-generic-flat-reduced-base-model vs lem-trf-generic-constancy-geometric-reducedness: the existing node is generic constancy of the whole geometric-reducedness fibre locus; this child constructs a reduction model without such a conclusion.

lem-trf-generic-flat-reduced-base-model vs lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism: gives only the topological property of a surjective closed immersion, not residue-field isomorphisms or a flat locally finitely presented model.

lem-trf-generic-flat-reduced-base-model vs lem-weil-pbc-reduction-universal-homeomorphism: gives the reduction and its universal homeomorphism, not generic-flat affine preparation with fibre identifications.

lem-trf-generic-flat-reduced-base-model vs lem-pur-generic-quasi-separatedness: concludes only generic quasi-separatedness over an already integral base, not a reduction model or its comparison maps.

lem-trf-smooth-open-schematic-generic-density vs sbc-lem-smooth-criterion: tests a whole morphism for smoothness from all smooth fibres; it does not construct a dense smooth generic open or fibrewise schematic-density data.

lem-trf-smooth-open-schematic-generic-density vs lem-trf-generic-fibre-points-smooth: requires Noetherian schemes and all geometric fibres reduced and addresses component generic points; our task needs only one geometrically reduced generic fibre and no Noetherian base.

lem-trf-smooth-open-schematic-generic-density vs lem-trf-generic-fibre-geometrically-reduced-open: the parent concludes an open of geometrically reduced whole fibres; this child instead gives a smooth open with generic schematic density under already-flat hypotheses; spreading is still required.

lem-trf-smooth-open-schematic-generic-density vs lem-trf-affine-chart-stalk-differentials: identifies stalk maps and differential modules, not schematic generic density or geometric reducedness of the smooth open.

lem-trf-smooth-open-schematic-generic-density vs lem-trf-fibre-cotangent-localization-generators: is a ring/module cotangent comparison, not a construction of a smooth open in a family.

lem-trf-smooth-open-schematic-generic-density vs lem-trf-generic-constancy-geometric-reducedness: the existing node is generic constancy of the whole geometric-reducedness fibre locus; this child constructs a smooth open in an already-flat family and has no assertion of constancy.

lem-trf-smooth-open-schematic-generic-density vs lem-trf-affine-fibre-point-dimension: identifies affine charts, points and dimensions of fibres; it does not give the smooth-open or density conclusions.

lem-trf-smooth-open-schematic-generic-density vs lem-trf-smooth-at-point-differential-criterion: is a local differential test for smoothness, not global density of a smooth open in the generic fibre.

lem-trf-smooth-open-schematic-generic-density vs lem-trf-smooth-at-point-fibre-criterion: is the pointwise fibre criterion used in the future proof; it does not construct the generic schematically dense open or its fibre properties.

lem-trf-smooth-open-schematic-generic-density vs sk-thm-geo-generic-open: is constructibility of derived open pushforward for sheaves, with different objects and conclusion.

lem-trf-smooth-open-schematic-generic-density vs lem-sfb-flat-space-smooth-locus: gives a largest smooth open and its base-change compatibility for algebraic spaces, not generic schematic density or the Noetherian-fibre and geometric-reducedness conclusions.

lem-trf-smooth-open-schematic-generic-density vs lem-pur-geometrically-reduced-dense-smooth-open: gives topological density for a scheme over a field, not the relative smooth open in a flat family, schematic generic density, or its fibre finiteness.

The discarded lem-trf-geometrically-reduced-from-dense-open would have specialized lem-sbc-geometrically-reduced-dominant-descent. It is not delivered: the parent cites that existing node directly.


## Landing-return repair by Q62 (2026-10-22)

The maintainer returned the approved side delivery because its completion was never promoted to the live DAG. I continued the retained sandbox rather than reconstructing or discarding it. The first required dry run exited successfully at e3f8348fc16, before these repair edits. The delivery tool fetches the current meeting-point DAG and constructs the commit on that base; no git command was run in the shared read clone.

I compared the current live parent with returned-item.json and the retained split. The live parent still contains the original eight proof steps. Its statement, statement dependencies, source, blueprint ancestry, Lean metadata and old review agree with the retained baseline; only proof, proof_deps and split_report differ from the proposed split. The released stage-1 repair note explicitly reopens this reviewed node and requires at least two new statement-only tasks with an assembly under 3000 characters. Both retained child ids remain absent from the live DAG. Thus this is the outstanding requested re-split, not an attempt to replace a superseding live proof.

I re-read the current statements of lem-trf-schematic-density-generic-fibre-open and lem-sbc-geometrically-reduced-dominant-descent and the latter's public Lean helper. Neither statement differs from the verbatim quotes saved in citations.json. For step 3, finite type, the irreducible base and the generic structure-sheaf injection are exactly the spreading lemma's hypotheses; its conclusion is the fibrewise injection. For step 4 the descent statement asks for quasi-compactness and that same zero kernel, with geometrically reduced composite to the residue field. The smooth-open child's statement supplies quasi-compactness of every fibre open immersion and geometric reducedness of its source. I adjusted assembly step 2 to state this quasi-compactness conclusion explicitly, so step 4's reference to step 2 is visible without recovering an unstated intermediate fact. No stronger separation or Noetherian-base assumption is introduced.

I re-read Stacks 0578 and 0573 in more-morphisms.tex, and 052A, 081I and 056B in morphisms.tex. The reduction/flat preparation, smooth-open construction, density spreading and arbitrary-field-extension descent remain the same route. Steps 1 and 5 use only the first child's stated residue-field, fibre and homeomorphism comparisons; step 2 uses only the second child's stated clauses. All five step/node citation pairs still match their cited current statements verbatim. This also verifies C1 and C4 after rebasing. Empty fibres, a nonreduced irreducible base, and the imperfect-field countertest recorded above continue to satisfy the same checks. Both children remain statement-only, contain no hidden proof text, and no step exceeds 2000 characters.

The previous proof, source citations, returned argument, search-result files and searches.jsonl are retained unchanged. The mathematical statements and search questions did not change, so the existing actual search records were reused rather than rerun or invented. The repaired assembly and this report will be checked by a new final dry run, then pushed through the delivery tool.


## Current-base repair verification by Q62 (2026-10-22)

The required initial dry run completed successfully at 49b48950f19, without pushing. I compared returned-item.json with the current shared DAG parent field by field: they are identical. The retained proposal differs from that parent only in proof, proof_deps and split_report. Both new child ids remain absent from the current DAG. The released stage-1 repair order still explicitly requires this re-split, so there is no superseding live completion to overwrite. The delivery tool rebuilds on the freshly fetched meeting-point branch; this retry retains the existing arguments and search records.

I reopened all four proof-dependency statements, including both current existing nodes. All five citations.json entries remain verbatim substrings of those statements. The current spreading statement still takes exactly finite type, an irreducible base and generic sheaf injectivity; step 3 supplies these. The current dominant-descent statement still takes a quasi-compact map with zero structure-sheaf kernel and geometrically reduced composite; step 4 obtains all three from steps 2 and 3. No changed dependency requires a different route. I reread Stacks 0578 and 0573 in more-morphisms.tex and 052A, 081I and 056B in morphisms.tex: their reduction, flat preparation, density spreading and field-extension descent are the same route retained here. The project-source search again found no declaration under WeilConjectures stating the item.

This retry makes the application in step 4 explicit: it names the residue field and fibre structure map, identifies zero kernel with the injection from step 3, and identifies quasi-compactness and geometric reducedness of the composite with the clauses supplied in step 2. These are exactly the current descent statement's hypotheses. The displayed JSON escaping initially suggested a TeX issue, but checking the parsed strings found none; no TeX change was required. The five short steps still total less than 3000 characters and none reaches 2000 characters. Both children retain statement-only status; no search question changed, so the actual logged results are reused. The empty-source, nonreduced-base, imperfect-field and nilpotent-supported-on-the-complement checks above continue to apply. A fresh final dry run and push follow these edits.


## Landing-return repair by Q62 (2026-10-23)

The single returned point is the unpromoted side completion: rebase the approved re-split onto the current live DAG, reread changed cited nodes, adjust the split, and push again. I ran the required initial dry run before editing; it exited OK at e0de6e985ad. I then compared all parsed fields of returned-item.json, the live parent and the saved proposal. The returned baseline equals the live parent in every field; the proposal differs only in proof, proof_deps and split_report. Both child ids remain absent from the current DAG. The released stage-1 repair note still requires two new statement-only tasks and a short assembly. I rebuilt every untouched parent field from that live node, preserving its statement, statement dependencies, source, blueprint chain and maintainer metadata.

I reread both existing proof dependencies in their current files: lem-trf-schematic-density-generic-fibre-open still has finite type, irreducible base and generic sheaf injection as hypotheses, and supplies exactly the fibrewise sheaf injection needed by step 3. Lem-sbc-geometrically-reduced-dominant-descent still requires a quasi-compact map, zero structure-sheaf kernel and geometrically reduced composite to a field. Step 4 has exactly these three from steps 2 and 3; the public helper in GeometricallyReducedDominantDescent.lean also states this interface. Neither dependency statement has changed from the retained citations. I checked all five saved step/node quotations against the current or proposed statements, with no missing pair and no changed quote.

I also reread the definition statements used by the parent and children. The geometric-reducedness definition quantifies over all field extensions. Therefore steps 1 and 5 now explicitly justify invariance under the supplied residue-field and fibre isomorphisms: transport a field-extension structure through the inverse residue-field isomorphism, then identify the two pullbacks over that field using the fibre isomorphism. Step 5 takes the nonempty open image under the child's homeomorphism onto an open subset of Y. This is an application of the stated comparison data and definitions, with no additional geometric theorem hidden in the final transfer. Step 2 continues to export quasi-compactness of the open immersions, rather than using mere topological density in step 4.

I reread Stacks 0578 and 0573 (more-morphisms.tex), generic flatness 052A, flat pullback 081I and reduced-image 056B (morphisms.tex), and the dense smooth open 056V (varieties.tex), together with the pointwise smooth criterion 01V9 and reduced-target density 056D. The model child still isolates reduction and generic-flat preparation without assuming generic geometric reducedness; the smooth-open child still stops at schematic generic density and reduced open fibres, so neither restates the parent's conclusion. The empty-source test satisfies all zero-sheaf injections, and the nonreduced irreducible base test needs the child's exact residue-field comparison. The imperfect-field example and nilpotent complement example in the earlier review still exclude respectively replacing geometric reducedness by reducedness or schematic density by topological density. No new statement, source route or Mathlib search question was introduced. I read the retained search log and saved result files; their actual queries/results are reused unchanged. Current whole-blueprint searches for the two construction interfaces again found no match and confirmed lem-trf-local-term-locality as ancestor.

All old proof arguments remain in the retained Coverage section and the same two independently claimable child tasks; both children remain statement-only, with no proof steps or proof dependencies. No step reaches 2000 characters, and the assembly is below 3000. This repair changes the assembly and report in addition to rebasing, and will receive a fresh final dry run and delivery push. No repository/launcher write, git command in the read clone, Lean write or compile was performed.

Live parent SHA-256 read for this repair: 87b3ffd02ae0816c66e061ca060e563b12988fff4f1cae69cba9c20c42a28597. Assembly lengths after repair: [428, 430, 329, 493, 481]; total 2161 characters.

The first final dry run on 2026-10-23 stopped at a new same-tag candidate, lem-trf-smooth-fibre-affine-ring-at-prime (01V9). I opened its full current statement and source reference: its premise is an already-smooth fibre neighbourhood, and its conclusion is smoothness of k -> A tensor_R k at the corresponding kernel prime. It supplies none of the generic-density, global smooth-open or fibre-finiteness interface. I added the required pairwise distinction under Not duplicates. The node remains a valid finer input of the pointwise criterion already allocated to the smooth-open task, so no parent citation or mathematical statement changed.
