## Worker report

Q43, stage 1 repair, 2026-10-23. Item: lem-sfb-local-surface-maximal-blowup-geometry.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-local-surface-maximal-blowup-geometry.json: unchanged statement and statement dependencies; four-step assembly of 1704 characters in place of the nine-step proof.
- dag/nodes/sec-six-functors-basics/lem-sfb-two-parameter-blowup-atlas.json: statement, unsplit, no Mathlib match; atlas, Cartier equations and Noetherianity over a Noetherian base with a two-term regular sequence in both orders.
- dag/nodes/sec-six-functors-basics/lem-sfb-two-parameter-exceptional-fibre-gluing.json: statement, unsplit, no Mathlib match; exact fibre chart maps, reciprocal-coordinate overlap, projective-line gluing and regularity when the quotient by the pair is a field.
- dag/nodes/sec-six-functors-basics/lem-sfb-local-surface-chart-local-rings.json: statement, unsplit, no Mathlib match; the two cases for prime localizations of the hypersurface chart, including the quotient isomorphism and the dimension-two refinement.
- citations.json: a verbatim statement quotation for each assembly-step citation.
- report.md: this report, preservation of the old arguments, duplicate comparisons and signed review.

Three new statement-only nodes, zero Mathlib leaves. All three have empty proof and proof_deps, null proof_origin, complete statements, definition dependencies, source tags/labels, and actual search records. Search outputs, searches.jsonl, the baseline JSON and preparation scripts are sandbox support, not proposed repository files. No Lean, compiler, Lake or repository git command was used. The sandbox initially contained only dispatcher markers; there was no prior item, report or search log to recover. The repository item was therefore copied and saved unchanged as baseline-item.json before repair. Existing provenance, searches, Lean records and review metadata were preserved in the item copy.

### Attachments

None. Exact blueprint-id and concept searches under lean/WeilConjectures found supporting blowup constructions and principalization, but not this theorem or any of the three new statements. Sheaf.AlgebraicGeometry.LocalSurfaceMaximalBlowupGeometry.localSurfaceMaximalBlowupGeometry, lines 180--197, still has sorry. Its docstring contains the old nine-step proof. The theorem is not an attachment. The generic global surface sibling depends on this item and cannot be used to discharge it.

### WANTED

None. All mathematical sources used here are present in literature/stacks-project/.

### What was wrong and what changed

The released stage-1 repair note of 2026-10-22 explicitly reopens the reviewed item with keep_plan true. Its only numbered mathematical request is to spread the 6020-character proof into at least two comparable statement-only tasks, keep every old argument, keep the item statement, and leave an assembly of at most 3000 characters. This repair adds three tasks, with statement lengths 1386, 1389 and 1491 characters. Their argument loads are old steps 1--3 (about 2017 characters), 4--5 (1519 characters), and 6--9 (about 2484 characters). Parameter selection stays in assembly step 1. These are coordinate and local-ring calculations with their own hypotheses, not three copies of the global conclusion. No statement dispute was found and the original statement is byte-identical.

The nearest blueprint ancestor remains null, as tools/blueprint_refs.py ancestor reports. The item keeps its precise inherited from.place and via chain; each new node adds the item at the front of that via chain and pinpoints its old proof steps. I read the current main-20261015 direct-images proof (3), under sec-six-functors-basics/sk-thm-sf-ctf-stability: the local surface calculation serves its alteration-route descendants. Nothing at chapter or unit level is changed. The unit record is historical sk-thm-sf-ctf-stability, and this item is not its key statement.

### What remains unfinished

The three new arguments are intentionally unsplit and ready for independent workers. Their complete intended arguments and original supporting-node citations are preserved below. No Lean completion is claimed.

## Review by Q43

I read resolve.tex, Tag 0AGQ (resolve-lemma-blowup), including its Rees algebra and exceptional-fibre identification, and Tag 0AGR (resolve-lemma-blowup-regular), including the local equation and regular quotient argument. The original item's hypotheses match these: regular local A of dimension two, arbitrary residue field, reduced closed-point center. I also read more-algebra.tex Tag 0BIQ (lemma-blowup-regular-sequence), and algebra.tex 00FN (lemma-Noetherian-permanence), 00NU (lemma-regular-mod-x), 0AFS (lemma-localization-of-regular-local-is-regular), 00OP (lemma-dim-affine-space), and 00KW (lemma-one-equation). The chart version is the already reviewed route, retained rather than replaced by the associated-graded proof of 0AGQ. No SGA source is used.

New atlas statement: its base need not be local or regular; both orders of the pair are explicitly required regular. This permits two applications of the existing 0BIQ presentation theorem. I opened that node and the chart-cover, chart-ring, global blowup, global glue-data and local-model definitions. The statement of 0BIQ supplies the algebra presentation and ratio correspondence but does not state a scheme atlas, Cartier equations or global Noetherianity; those are the remaining argument assigned here. Noetherianity of A is explicit, so the old finite-type algebra and two-affine-cover argument is valid. The actual extended ideal defines the base-change subscheme, and a subalgebra of A_x has injective multiplication by the unit x, with no need to infer that A is a domain. I preserved the homogeneous chart maps to support the next task.

New fibre statement: the quotient k=A/(x,y) is explicitly assumed a field, while regular localness or dimension two of A is unnecessary for this calculation. The quotient chart rings and their scheme-theoretic overlap, rather than only the set of points, are part of the conclusion. I read the projective-space standard-chart node in full: its clauses (a)--(c) supply the cover, polynomial rings and ratios, with exactly two homogeneous coordinates. Thus the inverse-coordinate identifications glue with their inverses to an isomorphism over k. I read lem-sc-p1-polynomial-regular and the affine-open stalk-localization node; they provide all prime localizations, not only closed or rational points. Local Noetherianity on the two polynomial charts gives the regular-scheme criterion. This is the old gluing argument isolated as a real comparison, not a proof sketch inserted in the new statement.

New local-ring statement: it concerns an explicitly defined ring C=A[z]/(gz-h), independently of any blowup construction. Both ordered pairs are quantified. Its exceptional and complementary cases preserve every calculation in old steps 6--9. The regular-parameter theorem and chart presentation identify C with the subalgebra chart and give injectivity of g; finite-type Noetherianity and Noetherian localization apply. For g in p, localization preserves this injectivity by the fraction zero criterion, and quotienting fractions gives R/gR = k[z]_(p/(g)). Its quotient is nonzero because g is in the maximal ideal. I opened the regular-sequence-quotient lifting node: its statement requires a Noetherian local ring, a regular sequence in the maximal ideal, and regular quotient, exactly supplied here by the singleton g. For g outside p, the coefficient map and z -> h/g identify C_g with A_g and the stalk with A_r; I opened the regular-local-localization node and verified it applies without excellence. Finally I opened both the polynomial-ring maximal-localization dimension node and the nonzerodivisor quotient dimension node. Their statements give dimension one for every maximal ideal of k[z] and the equality dim R = dim(R/gR)+1. The maximality condition is explicit, so no assertion of dimension two at the generic point is introduced.

Assembly step 1 cites the definition of regular local ring, the full regular-parameter theorem and the new atlas statement. The definition supplies two maximal-ideal generators and Noetherianity, the parameter theorem supplies both regular orderings, and the atlas statement expressly supplies the same actual blowup and Cartier base-change subscheme. All hypotheses of the atlas are therefore checked before application.

Assembly step 2 cites the new fibre statement with I=m. Its field hypothesis is the actual residue field A/m, not a chosen coefficient field. Its conclusion explicitly contains the chart identifications, gluing isomorphism and regular local rings used in this step. No claim is extracted from an unstated proof of the new node.

Assembly step 3 cites the affine-open stalk-localization statement, the new chart local-ring statement, and the regular-scheme definition. The first gives C_p for the point in either atlas chart. The second is applicable to both orderings of the parameters and states regularity at every prime. The definition gives the locally-Noetherian plus regular-stalk criterion; local Noetherianity was established in step 1. Thus regularity away from E is checked as well as regularity on E, without relying on the global sibling that depends on this item.

Assembly step 4 cites the new chart local-ring statement. A closed singleton in E stays closed in its intersection with an affine fibre chart; a closed point of Spec k[z] corresponds by the definition of the Zariski topology to a maximal ideal. The new node states the quotient isomorphism and dimension-two conclusion for exactly that condition. Step 3 already gave regular localness. Nothing requires residue-field rationality.

I checked delivery-errors B--E against these statements and every assembly citation. The new nodes have no proof steps or hidden proof sketches, introduce their own objects and explicitly list definitions. Their statements are not the entire item and their proof dependencies do not point to the item. The generic chart-presentation node is retained as a supporting tool for the future atlas proof, not duplicated. Each assembly citation has a full verbatim quotation in citations.json. All four assembly steps are below 2000 characters and their total is below 3000. The original nine arguments are reproduced verbatim in the preservation section, so even their elementary fraction manipulations are retained for the next workers.

Small cases: A=k[[x,y]] gives the ordinary two charts. Mixed characteristic A=Z_p[[y]] with x=p needs no coefficient-field section and satisfies the same equations. For k=R, a point of the exceptional affine line defined by z^2+1 is closed but not rational; its quotient local dimension is one and its ambient local dimension two. At the generic point p=(g), the quotient is k(z), dimension zero, so the ambient local dimension is one and is correctly excluded from the dimension-two assertion. Off E, g is a unit and the localization is exactly A_r. For the two general regular-pair nodes, A=k[x,y,w] and I=(x,y) tests the atlas without the field hypothesis, whereas A=k[x,y] tests the fibre node without localness; the latter fibre is P^1_k. Zero rings and pairs with a unit are excluded by the nonzero-final-quotient condition of a regular sequence. Swapping x,y preserves all hypotheses and conclusions. No perfection, algebraic closedness, excellence or completeness has been inserted.

The repairs made during this self-review were to state the new atlas for a general Noetherian regular pair (so it does not merely repeat a clause about this surface), to include all scheme-theoretic overlap maps in the fibre node, and to make maximality and the two localization cases explicit in the chart-ring node. I retained the old proof in full below and copied full cited statements into citations.json to keep the exact hypotheses visible. The server check_dag and review_split probes returned PASS/OK; the complete delivery dry run follows and is authoritative for the proposed new nodes.

## Mathlib searches and duplicate search

I ran msearch.py for each named new node: leanfinder, loogle, grep, leansearch, and a second leanfinder phrasing, with each node's own statement in mind. Every service answered. All query strings and raw outputs are in the new node records and sandbox files. No search was invented. Additional grep calls searched the AlgebraicGeometry subtree for exceptional/blowup terms (zero hits), and the RegularLocalRing subtree for the possible polynomial-localization match. I read Mathlib/RingTheory/RegularLocalRing/Polynomial.lean:35--68: Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal is about A[z]_p, not its hypersurface quotient. I read ReesAlgebra.lean and ProjectiveSpectrum/Basic.lean:256,321,336 and Scheme.lean:847: general Rees finiteness, Proj covers, overlaps and projIsoSpec do not supply these exact blowup-ring/fibre comparisons by one-line specialization. They remain building blocks. No new leaf is claimed.

Whole-DAG searches used the source tags, two-chart blowup, regular-sequence, exceptional fibre, explicit A[t]/(xt-y) and chart-local-ring terms. Whole-blueprint searches used blowup, 0BIQ, 0AGQ, 0AGR, xt-y, two-parameter, hypersurface, regular local surface, exceptional fibre and regular sequence. There is no imported blueprint theorem stating a new node. All source-tag neighbours were opened at their statement fields; the comparisons below identify the shared tool versus the actual new argument. The dropped per duplicate is not used or modified. Existing broad global surface lemmas either require extra excellence/ample hypotheses or depend on the present item; they cannot replace these coordinate tasks.

## Preserved arguments and assignment to the new nodes

This section deliberately transcribes every old proof step, with its existing citations, so the re-split spreads the work without losing it. These are future-worker proof materials in the report; the new nodes themselves are statement-only. The parameter-choice opening of old step 1 remains in assembly step 1; its two-chart construction joins steps 2--3 in the atlas task. Old steps 4--5 belong to the fibre task. Old steps 6--9 belong to the chart local-ring task; replacing a stalk by C_p is the affine-open identification retained in assembly step 3. The proof route and all subsidiary arguments are unchanged.

### Old step 1, assigned to lem-sfb-two-parameter-blowup-atlas

Use the singleton affine cover of $S=\operatorname{Spec}A$ in the global blowup construction; its sole local model is the affine blowup of $\mathfrak m$. By the definition of regular local ring, choose $x,y$ generating $\mathfrak m$. The regular-system-of-parameters theorem makes both $(x,y)$ and $(y,x)$ regular sequences. The affine blowup chart cover and the regular-sequence chart-presentation theorem give an open cover of $Y$ by
$$U_x=\operatorname{Spec}C_x,\quad C_x=A[\mathfrak m/x]\cong A[t]/(xt-y),\qquad U_y=\operatorname{Spec}C_y,\quad C_y=A[\mathfrak m/y]\cong A[u]/(yu-x).$$
Here $t$ is the ratio $y/x$ and $u$ is $x/y$ under the chart identifications. No excellence or algebraically closed residue field is assumed.

Existing supporting statements: def-nagata-global-blowup, def-nagata-global-blowup-glue-data, def-nagata-global-blowup-local-model, def-weil-regular-scheme, lem-weil-pbc-regular-local-generators-regular-sequence, prop-nagata-affine-blowup-chart-cover, lem-trf-blowup-chart-regular-sequence-presentation.

Source: literature/stacks-project/resolve.tex, Tag 0AGQ (lemma-blowup), choice of parameters; more-algebra.tex Tag 0BIQ (lemma-blowup-regular-sequence), the two affine charts.

### Old step 2, assigned to lem-sfb-two-parameter-blowup-atlas

On $U_x$ the extended maximal ideal is $(x,y)C_x=(x)$ since $y=xt$; on $U_y$ it is $(y)$ since $x=yu$. By the definition of the chart ring, $C_x$ is a subalgebra of $A_x$. Multiplication by $x$ on $C_x$ is injective: an equality $xc=0$ remains true in $A_x$, where $x$ is a unit, hence $c=0$ in that subalgebra. The same argument applies to $y$ on $C_y$. The scheme-theoretic inverse image of the closed point is locally defined by the extended ideal: for either chart $C$, $C\otimes_A k=C/\mathfrak m C$. Consequently $E$ is locally cut out by these nonzerodivisors, which is precisely the effective Cartier condition.

Existing supporting statements: def-nagata-blowup-chart-ring, def-nagata-effective-cartier-ideal, def-weil-pbc-localization-at-prime.

Source: literature/stacks-project/resolve.tex, Tag 0AGQ (lemma-blowup), E is the closed subscheme defined by the extended maximal ideal; chart verification of the effective Cartier condition.

### Old step 3, assigned to lem-sfb-two-parameter-blowup-atlas

The ring $A$ is Noetherian by regular localness. Each of $C_x,C_y$ is a quotient of a one-variable polynomial algebra over $A$, so the finite-type-algebra Noetherian theorem makes both Noetherian. Thus the two-chart cover makes $Y$ locally Noetherian. It also makes $Y$ quasi-compact: each affine spectrum is quasi-compact, since a covering by basic opens $D(f_i)$ means that the $f_i$ generate the unit ideal, and an expression $1=\sum_{i\in F}a_if_i$ uses finitely many indices. Any open cover refines to basic opens on each chart, giving finite subcovers on the two charts, and their union is finite. Hence $Y$ is Noetherian (locally Noetherian and quasi-compact).

Existing supporting statements: def-weil-regular-scheme, lem-weil-pbc-finite-type-algebra-noetherian, pqf-def-locnoeth, def-weil-affine-spectrum, lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact.

Source: literature/stacks-project/resolve.tex, Noetherianity in the setup of Tags 0AGQ and 0AGR, from the two finite-type affine charts; algebra.tex Tag 00FN (lemma-Noetherian-permanence).

### Old step 4, assigned to lem-sfb-two-parameter-exceptional-fibre-gluing

The fibre rings on the two charts are
$$C_x/(x)=A[t]/(x,y)=k[t],\qquad C_y/(y)=A[u]/(x,y)=k[u].$$
The chart map sends $t$ to $(yT)/(xT)$ in the degree-zero homogeneous localization of the Rees algebra, and sends $u$ to $(xT)/(yT)$. In the $x$-chart the $y$-chart is therefore exactly the basic open where $t$ is invertible, and conversely it is the open where $u$ is invertible in the $y$-chart. On this intersection the two ratios multiply to $1$. Reducing modulo the extended maximal ideal, the overlap is $\operatorname{Spec}k[t,t^{-1}]$ with transition $u=t^{-1}$. These are ring identities in the homogeneous localizations, so the computation concerns the scheme-theoretic fibre, including its structure sheaf.

Existing supporting statements: def-nagata-affine-blowup-chart-map, def-nagata-affine-proj.

Source: literature/stacks-project/resolve.tex, Tag 0AGQ (lemma-blowup), exceptional-fibre calculation, expressed in the two homogeneous-localization charts.

### Old step 5, assigned to lem-sfb-two-parameter-exceptional-fibre-gluing

Apply the projective-space standard-chart theorem with base $\operatorname{Spec}k$ and two homogeneous coordinates $T_0,T_1$. Its charts have rings $k[T_1/T_0]$ and $k[T_0/T_1]$; their intersection is where the displayed coordinate is invertible, because each homogeneous coordinate is a free generator of $\mathcal O(1)$ on its own chart. The products of these ratios are $1$. Sending $t$ to $T_1/T_0$ and $u$ to $T_0/T_1$ therefore gives chart isomorphisms agreeing on the overlap computed in step 4. They glue, as do their inverses, to an isomorphism $E\cong\mathbf P^1_k$. Moreover $k[t]$ and $k[u]$ are regular rings by the polynomial-regularity lemma. The affine-open stalk-localization theorem identifies every local ring of $E$ with a prime localization of one of them, hence it is regular local.

Existing supporting statements: lem-weil-pbc-projective-space-standard-charts, lem-sc-p1-polynomial-regular, lem-weil-pbc-affine-open-stalk-localization, def-weil-regular-scheme.

Source: literature/stacks-project/resolve.tex, Tag 0AGQ (lemma-blowup), identification of the exceptional divisor; Tag 0AGR (lemma-blowup-regular), regularity of its projective-line local rings; algebra.tex Tag 00OP.

### Old step 6, assigned to lem-sfb-local-surface-chart-local-rings

Let $q\in E$ be any point, choose a chart $C=C_x$ or $C_y$ containing it, and write $g=x$ or $y$ respectively. The affine-open stalk theorem identifies $R=\mathcal O_{Y,q}$ with $C_{\mathfrak p}$, where $g\in\mathfrak p$. The localization-Noetherian theorem makes $R$ Noetherian. The element $g/1$ is still a nonzerodivisor: if $(g/1)(a/s)=0$, some $v\notin\mathfrak p$ kills $ga$ in $C$, so $g(va)=0$ and hence $va=0$ by step 2; thus $a/s=0$. Quotienting the fractions gives
$$R/gR\cong(C/(g))_{\mathfrak p/(g)}\cong\mathcal O_{E,q}.$$
Indeed both sides have representatives $a/s$ with $s\notin\mathfrak p$, and setting $g=0$ imposes exactly the ideal $gR$.

Existing supporting statements: lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-noetherian, def-weil-pbc-localization-at-prime.

Source: literature/stacks-project/resolve.tex, Tag 0AGR (lemma-blowup-regular), the local equation g and the quotient local ring of E.

### Old step 7, assigned to lem-sfb-local-surface-chart-local-rings

For the ring $R$ of step 6, $g$ lies in its maximal ideal, is a nonzerodivisor, and $R/gR$ is regular local by step 5. The singleton sequence $(g)$ is regular: multiplication is injective and its quotient is nonzero because $(g)$ lies in the maximal ideal. Apply regularity lifting from a regular-sequence quotient with $r=1$. It proves that every $\mathcal O_{Y,q}$ with $q\in E$ is regular local, including the generic point of $E$.

Existing supporting statements: def-weil-pbc-regular-sequence, lem-exc-regular-local-lift-regular-sequence-quotient.

Source: literature/stacks-project/resolve.tex, Tag 0AGR (lemma-blowup-regular), applying algebra.tex Tag 00NU (lemma-regular-mod-x).

### Old step 8, assigned to lem-sfb-local-surface-chart-local-rings

On $U_x\setminus E$ the chart ring is $(C_x)_x=A[t,x^{-1}]/(xt-y)\cong A_x$, with mutually inverse maps given by $t\mapsto y/x$ and the coefficient map. On $U_y\setminus E$ it is similarly $A_y$. A prime $\mathfrak p$ of $C_x$ avoiding $x$ thus corresponds to a prime $\mathfrak r$ of $A$ avoiding $x$, and the same fractions identify $(C_x)_{\mathfrak p}$ with $(A_x)_{\mathfrak rA_x}=A_{\mathfrak r}$. The $y$-chart is identical with $x,y$ interchanged. The regular-local-localization theorem applied to $A$ makes these rings regular local. Together with step 7 this proves regularity at every point of $Y$; since $Y$ is locally Noetherian by step 3, the local-ring characterization of regular schemes proves that $Y$ is regular.

Existing supporting statements: lem-weil-pbc-regular-local-localization, lem-weil-pbc-affine-open-stalk-localization, def-weil-pbc-localization-at-prime, def-weil-regular-scheme.

Source: literature/stacks-project/resolve.tex, Tag 0AGR (lemma-blowup-regular), regularity away from E via the chart complement; algebra.tex Tag 0AFS (lemma-localization-of-regular-local-is-regular).

### Old step 9, assigned to lem-sfb-local-surface-chart-local-rings

Finally let $q$ be closed in $E$. Its intersection with a chart is closed in $\operatorname{Spec}k[t]$ or $\operatorname{Spec}k[u]$, so its prime there is a maximal ideal $\mathfrak n$. The maximal-localization dimension theorem with one variable gives $\dim\mathcal O_{E,q}=\dim k[t]_{\mathfrak n}=1$ (using $u$ on the other chart). Step 6 supplies the Noetherian local ring $R=\mathcal O_{Y,q}$, the nonzerodivisor $g$ in its maximal ideal, and $R/gR\cong\mathcal O_{E,q}$. The nonzerodivisor quotient dimension formula now gives $\dim R=\dim(R/gR)+1=2$. Its regular localness was already proved in step 7. No rationality of the closed point over $k$ is used.

Existing supporting statements: lem-weil-pbc-polynomial-ring-maximal-localization-dimension, lem-weil-pbc-dimension-quotient-nonzerodivisor.

Source: literature/stacks-project/resolve.tex, Tag 0AGR (lemma-blowup-regular), closed-point refinement of the local calculation; algebra.tex Tags 00OP (lemma-dim-affine-space) and 00KW (lemma-one-equation).

## Not duplicates

The human re-split order explicitly asks for new independent subarguments. The atlas, fibre gluing and prime-local-ring computations divide the old argument, and none restates the entire item. The new atlas covers more general bases and no regularity conclusion about its ambient scheme; the fibre node records the coordinate comparison without the ambient regularity/dimension theorem; the local-ring node is a ring theorem with no blowup or projective-line conclusion. Comparisons with every shared-tag neighbour follow.

lem-sfb-local-surface-chart-local-rings vs def-sfb-surface-point-blowup-data: that node defines point-blowup fibre data and tower conventions but proves none of these chart, gluing or regular-local-ring assertions.

lem-sfb-local-surface-chart-local-rings vs lem-exc-regular-local-lift-regular-sequence-quotient: that node is the regular-quotient lifting tool used within the new local-ring task, but it does not establish the hypersurface chart equations, injectivity, quotient-localization comparison, complementary localization or closed-point dimension.

lem-sfb-local-surface-chart-local-rings vs lem-per-local-surface-maximal-blowup-geometry: this is the dropped whole-theorem per duplicate; the new node isolates only one coordinate/local-algebra argument and does not cite the dropped duplicate.

lem-sfb-local-surface-chart-local-rings vs lem-per-regular-point-blowup-acyclic: that dropped global point-blowup theorem includes higher direct-image vanishing and does not state the new coordinate/local-algebra interface.

lem-sfb-local-surface-chart-local-rings vs lem-per-surface-point-blowup-geometry: that dropped global statement assumes excellence, dimension two globally and an ample sheaf; the general-pair atlas/fibre and arbitrary regular-local-ring calculation have none of those assumptions.

lem-sfb-local-surface-chart-local-rings vs lem-per-surface-tower-discard-regular-centers: that dropped theorem contracts stages of a normal excellent surface tower, rather than computing these charts or their local rings.

lem-sfb-local-surface-chart-local-rings vs lem-pur-smooth-codimension-one-cartier: the existing statement concerns “A smooth pair with local dimension drop one is Cartier”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sbc-depth-two-punctured-principal-slice-connected: the existing statement concerns “Connected depth-two puncture with nonempty principal slice”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sbc-regular-integral-divisor-boundary: the existing statement concerns “Regular codimension-two boundary away from an integral divisor generic point”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sbc-root-algebra-regular-at-root: the existing statement concerns “Root-algebra localizations along the root divisor are regular”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sc-effective-cartier-affine-dimension-drop: the existing statement concerns “Dimension drop for a principal Cartier subscheme of an affine variety”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sc-p1-polynomial-noetherian: the existing statement concerns “A one-variable polynomial ring over a field is Noetherian”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sc-principal-quotient-dimension-full-height: the existing statement concerns “Principal quotient dimension at a prime of full height”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sc-tsen: the existing statement concerns “Tsen's theorem”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-dvr-binomial-local-geometry: that node treats DVR binomials xy-pi^e and their singularity at the origin, rather than the parameter-ratio chart A[z]/(gz-h) over arbitrary regular local A.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-dvr-nodal-chart-blowup-calculus: that node assumes a nodal surface over a DVR and gives three charts for its singular-point blowup; the new nodes concern a regular two-term pair or regular local surface, with two charts.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-henselian-parameter-root-domain-tower: the existing statement concerns “Domains in henselian parameter-root towers and their filtered colimits”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-henselian-parameter-root-regularity: the existing statement concerns “Henselian regular parameter-root algebra with residue field and parameter basis”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-local-surface-maximal-blowup-geometry: the old whole surface-blowup theorem is being re-split by explicit human instruction; the new node is one proper coordinate/local-algebra subargument, with the other two required for assembly, not a replacement for the whole theorem.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-regular-hypersurface-initial-form: that node identifies tangent cones of a quotient of a supplied regular local ring and its order criterion; it does not prove regularity of all the parameter-ratio chart localizations or identify their quotients and complementary localizations.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-regular-point-blowup-geometry: that global point-blowup theorem depends on the present item, so using it here would be circular; it does not state the new coordinate interfaces.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-regular-trait-modification-graph-tower: that node constructs domination of a projective modification by a point-blowup tower over a DVR, not the coordinate algebra/fibre gluing statements here.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-smooth-trait-curve-local-properties: the existing statement concerns “Local properties of a smooth relative curve over a trait”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-surface-rational-map-point-resolution: that node resolves a rational map by a tower of point blowups, not one chart calculation.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-trait-point-tower-rational-components: that node controls geometric components in whole point-blowup towers, not the coordinate and local algebra underlying one regular chart.

lem-sfb-local-surface-chart-local-rings vs lem-sfb-transverse-local-root-family-regular: the existing statement concerns “Regularity of all transverse local partial-root presentations”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-trf-extended-hilbert-local-upper-bound: the existing statement concerns “Pointwise local upper bound for extended Taylor Hilbert functions”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-trf-fg-commutative-monoid-finite-presentation: the existing statement concerns “Finite presentations of finitely generated commutative monoids”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-trf-finite-residue-tower-local-geometry: the existing statement concerns “Closed points and Noetherian local models in a finite-residue tower”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-trf-local-module-arrow-noetherian-descent: the existing statement concerns “Simultaneous Noetherian local approximation of a morphism of finitely presented modules”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-trf-local-tower-collapse-noetherian: the existing statement concerns “Noetherian collapse of a supplied local ring tower diagram”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-trf-power-series-cohen-hypersurface-normality: the existing statement concerns “Normal ambient power-series rings and Cohen hypersurfaces”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-colimit-eventually-flat: the existing statement concerns “A flat colimit of finite modules over Noetherian local stages is flat at some stage”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra: the existing statement concerns “A quasi-finite cover of affine n-space has dimension at most n”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-dimension-quotient-nonzerodivisor: that node supplies the last dimension equality for an already supplied local nonzerodivisor; it does not construct or prove regular the chart local rings.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-fibre-ring-noetherian: the existing statement concerns “Fibre rings of a Noetherian algebra are Noetherian”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-finite-algebra-noetherian: the existing statement concerns “A module-finite algebra over a Noetherian ring is Noetherian”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-finite-gl-dim-regular-local: the existing statement concerns “A Noetherian local ring of finite global dimension is regular (Serre)”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-finite-type-algebra-noetherian: that node supplies a Noetherianity input; it does not construct the charts or prove their Cartier, gluing, regularity or dimension interfaces.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-flat-local-ring-maps: the existing statement concerns “A flat ring map induces flat local maps of local rings”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-flat-polynomial-append-fibre-regular-sequence: the existing statement concerns “Appending closed-fibre regular coordinates preserves flatness”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-flat-polynomial-append-tensor-fibre: the existing statement concerns “Flatness of the polynomial-append tensor fibre”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-flat-regular-fibre-parameter-selection: the existing statement concerns “Select flat polynomial parameters in a regular closed fibre”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-geometrically-regular-smooth-ascent: the existing statement concerns “Geometric regularity ascends along smooth ring maps”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-global-complete-intersection-equidimensional: the existing statement concerns “A global complete intersection has the expected dimension at every point”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: the existing statement concerns “The equations of a global complete intersection form a regular sequence at every prime”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-graded-finiteness-cohomology: the existing statement concerns “Cohomology of a finite type graded module over f^*B~ is a finite B-module”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-localization-noetherian: that node supplies Noetherianity of a supplied localization, not the coordinate/local-ring identifications and remaining assertions.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-localization-of-regular-ring: the existing statement concerns “A localization of a regular ring is regular”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-noetherian-height-quotient-bound: the existing statement concerns “Height drops by at most the number of equations (Krull)”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-p1-field-dimension-one: the existing statement concerns “The projective line over a field has dimension at most one”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-polynomial-append-closed-fibre-parameters: the existing statement concerns “Regular parameters of the polynomial-append closed source fibre”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference: the existing statement concerns “Dimension at a point of a quotient of a polynomial ring over a field: n minus the difference of heights”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-polynomial-quotient-dimension-lower-bound: the existing statement concerns “Dimension lower bound for a polynomial quotient over a field”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-polynomial-ring-maximal-localization-dimension: that node supplies only the polynomial-quotient dimension input, not the fibre gluing or the ambient hypersurface localization theorem.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-polynomial-ring-origin-regular-local: the existing statement concerns “The polynomial ring over a field localized at the origin is regular local of dimension d”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-rees-algebra-noetherian: the existing statement concerns “The Rees algebra of an ideal of a Noetherian ring is Noetherian”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-regular-local-localization: that node preserves regularity when localizing a ring already known regular local; it does not establish regularity of the new hypersurface chart or its exceptional local dimension.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-regular-sequence-dimension-at-point: the existing statement concerns “Dimension at a point cut out by a local regular sequence”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-weil-pbc-surjective-image-noetherian: the existing statement concerns “A ring receiving a surjection from a Noetherian ring is Noetherian”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-local-surface-chart-local-rings vs lem-zl-bertini-finite-cover-irreducible-system: the existing statement concerns “General divisors irreducible simultaneously on a finite etale cover”; it supplies neither the all prime local rings of A[z]/(gz-h) for a regular local surface nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs def-sfb-surface-point-blowup-data: that node defines point-blowup fibre data and tower conventions but proves none of these chart, gluing or regular-local-ring assertions.

lem-sfb-two-parameter-blowup-atlas vs lem-per-local-surface-maximal-blowup-geometry: this is the dropped whole-theorem per duplicate; the new node isolates only one coordinate/local-algebra argument and does not cite the dropped duplicate.

lem-sfb-two-parameter-blowup-atlas vs lem-per-regular-point-blowup-acyclic: that dropped global point-blowup theorem includes higher direct-image vanishing and does not state the new coordinate/local-algebra interface.

lem-sfb-two-parameter-blowup-atlas vs lem-per-surface-point-blowup-geometry: that dropped global statement assumes excellence, dimension two globally and an ample sheaf; the general-pair atlas/fibre and arbitrary regular-local-ring calculation have none of those assumptions.

lem-sfb-two-parameter-blowup-atlas vs lem-sc-p1-polynomial-noetherian: the existing statement concerns “A one-variable polynomial ring over a field is Noetherian”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-sfb-dvr-binomial-local-geometry: that node treats DVR binomials xy-pi^e and their singularity at the origin, rather than the parameter-ratio chart A[z]/(gz-h) over arbitrary regular local A.

lem-sfb-two-parameter-blowup-atlas vs lem-sfb-dvr-nodal-chart-blowup-calculus: that node assumes a nodal surface over a DVR and gives three charts for its singular-point blowup; the new nodes concern a regular two-term pair or regular local surface, with two charts.

lem-sfb-two-parameter-blowup-atlas vs lem-sfb-henselian-parameter-root-regularity: the existing statement concerns “Henselian regular parameter-root algebra with residue field and parameter basis”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-sfb-local-surface-maximal-blowup-geometry: the old whole surface-blowup theorem is being re-split by explicit human instruction; the new node is one proper coordinate/local-algebra subargument, with the other two required for assembly, not a replacement for the whole theorem.

lem-sfb-two-parameter-blowup-atlas vs lem-sfb-point-blowup-exceptional-conormal: that node concerns global integral regular surfaces and conormal bundles; it does not supply these general regular-pair chart maps, scheme gluing comparison, or independent algebraic hypersurface-localization theorem.

lem-sfb-two-parameter-blowup-atlas vs lem-sfb-point-blowup-fibre-defects: that node treats multiplicities, inseparable exceptional curves and defects for a flat trait surface, rather than the coordinate interfaces in the new statement.

lem-sfb-two-parameter-blowup-atlas vs lem-sfb-regular-point-blowup-geometry: that global point-blowup theorem depends on the present item, so using it here would be circular; it does not state the new coordinate interfaces.

lem-sfb-two-parameter-blowup-atlas vs lem-sfb-trait-point-tower-rational-components: that node controls geometric components in whole point-blowup towers, not the coordinate and local algebra underlying one regular chart.

lem-sfb-two-parameter-blowup-atlas vs lem-trf-blowup-chart-regular-sequence-presentation: 0BIQ gives a single algebra presentation for an arbitrary regular sequence, but does not state the two-chart scheme cover and global Cartier/Noetherian claims, the fibre/projective-space gluing, or the prime-local-ring regularity and dimension calculation.

lem-sfb-two-parameter-blowup-atlas vs lem-trf-chart-coordinate-nonzerodivisors: that node concerns injectivity after additional coordinate quotients in a regular-parameter chart, not the full atlas, fibre gluing or all-prime local-ring calculation.

lem-sfb-two-parameter-blowup-atlas vs lem-trf-extended-hilbert-local-upper-bound: the existing statement concerns “Pointwise local upper bound for extended Taylor Hilbert functions”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-trf-fg-commutative-monoid-finite-presentation: the existing statement concerns “Finite presentations of finitely generated commutative monoids”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-trf-finite-residue-tower-local-geometry: the existing statement concerns “Closed points and Noetherian local models in a finite-residue tower”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-trf-koszul-relations-quotient-torsionfree: that node proves saturation from a syzygy hypothesis in a supplied ring; it does not construct the geometric atlas/fibre gluing or establish the chart local-ring conclusions.

lem-sfb-two-parameter-blowup-atlas vs lem-trf-local-module-arrow-noetherian-descent: the existing statement concerns “Simultaneous Noetherian local approximation of a morphism of finitely presented modules”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-trf-local-tower-collapse-noetherian: the existing statement concerns “Noetherian collapse of a supplied local ring tower diagram”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-trf-polynomial-regular-sequence-syzygies: that node states preservation of regular sequences under polynomial extension and generation of first syzygies, rather than the geometric atlas, exceptional-fibre gluing or hypersurface-localization calculation.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-colimit-eventually-flat: the existing statement concerns “A flat colimit of finite modules over Noetherian local stages is flat at some stage”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-fibre-ring-noetherian: the existing statement concerns “Fibre rings of a Noetherian algebra are Noetherian”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-finite-algebra-noetherian: the existing statement concerns “A module-finite algebra over a Noetherian ring is Noetherian”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-finite-type-algebra-noetherian: that node supplies a Noetherianity input; it does not construct the charts or prove their Cartier, gluing, regularity or dimension interfaces.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-flat-local-ring-maps: the existing statement concerns “A flat ring map induces flat local maps of local rings”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-geometrically-regular-smooth-ascent: the existing statement concerns “Geometric regularity ascends along smooth ring maps”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-graded-finiteness-cohomology: the existing statement concerns “Cohomology of a finite type graded module over f^*B~ is a finite B-module”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-localization-noetherian: that node supplies Noetherianity of a supplied localization, not the coordinate/local-ring identifications and remaining assertions.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-localization-of-regular-ring: the existing statement concerns “A localization of a regular ring is regular”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-rees-algebra-noetherian: the existing statement concerns “The Rees algebra of an ideal of a Noetherian ring is Noetherian”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-blowup-atlas vs lem-weil-pbc-surjective-image-noetherian: the existing statement concerns “A ring receiving a surjection from a Noetherian ring is Noetherian”; it supplies neither the two-chart atlas and Cartier equations of a regular-pair blowup nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-exceptional-fibre-gluing vs def-sfb-surface-point-blowup-data: that node defines point-blowup fibre data and tower conventions but proves none of these chart, gluing or regular-local-ring assertions.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-per-local-surface-maximal-blowup-geometry: this is the dropped whole-theorem per duplicate; the new node isolates only one coordinate/local-algebra argument and does not cite the dropped duplicate.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-per-regular-point-blowup-acyclic: that dropped global point-blowup theorem includes higher direct-image vanishing and does not state the new coordinate/local-algebra interface.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-per-surface-point-blowup-geometry: that dropped global statement assumes excellence, dimension two globally and an ample sheaf; the general-pair atlas/fibre and arbitrary regular-local-ring calculation have none of those assumptions.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-sfb-dvr-nodal-chart-blowup-calculus: that node assumes a nodal surface over a DVR and gives three charts for its singular-point blowup; the new nodes concern a regular two-term pair or regular local surface, with two charts.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-sfb-local-surface-maximal-blowup-geometry: the old whole surface-blowup theorem is being re-split by explicit human instruction; the new node is one proper coordinate/local-algebra subargument, with the other two required for assembly, not a replacement for the whole theorem.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-sfb-point-blowup-exceptional-conormal: that node concerns global integral regular surfaces and conormal bundles; it does not supply these general regular-pair chart maps, scheme gluing comparison, or independent algebraic hypersurface-localization theorem.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-sfb-point-blowup-fibre-defects: that node treats multiplicities, inseparable exceptional curves and defects for a flat trait surface, rather than the coordinate interfaces in the new statement.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-sfb-regular-point-blowup-geometry: that global point-blowup theorem depends on the present item, so using it here would be circular; it does not state the new coordinate interfaces.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-sfb-trait-point-tower-rational-components: that node controls geometric components in whole point-blowup towers, not the coordinate and local algebra underlying one regular chart.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-trf-blowup-chart-regular-sequence-presentation: 0BIQ gives a single algebra presentation for an arbitrary regular sequence, but does not state the two-chart scheme cover and global Cartier/Noetherian claims, the fibre/projective-space gluing, or the prime-local-ring regularity and dimension calculation.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-trf-chart-coordinate-nonzerodivisors: that node concerns injectivity after additional coordinate quotients in a regular-parameter chart, not the full atlas, fibre gluing or all-prime local-ring calculation.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-trf-koszul-relations-quotient-torsionfree: that node proves saturation from a syzygy hypothesis in a supplied ring; it does not construct the geometric atlas/fibre gluing or establish the chart local-ring conclusions.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-trf-polynomial-regular-sequence-syzygies: that node states preservation of regular sequences under polynomial extension and generation of first syzygies, rather than the geometric atlas, exceptional-fibre gluing or hypersurface-localization calculation.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra: the existing statement concerns “A quasi-finite cover of affine n-space has dimension at most n”; it supplies neither the explicit exceptional-fibre gluing to the projective line nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-flat-polynomial-append-fibre-regular-sequence: the existing statement concerns “Appending closed-fibre regular coordinates preserves flatness”; it supplies neither the explicit exceptional-fibre gluing to the projective line nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-flat-polynomial-append-tensor-fibre: the existing statement concerns “Flatness of the polynomial-append tensor fibre”; it supplies neither the explicit exceptional-fibre gluing to the projective line nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-flat-regular-fibre-parameter-selection: the existing statement concerns “Select flat polynomial parameters in a regular closed fibre”; it supplies neither the explicit exceptional-fibre gluing to the projective line nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-global-complete-intersection-equidimensional: the existing statement concerns “A global complete intersection has the expected dimension at every point”; it supplies neither the explicit exceptional-fibre gluing to the projective line nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-p1-field-dimension-one: the existing statement concerns “The projective line over a field has dimension at most one”; it supplies neither the explicit exceptional-fibre gluing to the projective line nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-polynomial-append-closed-fibre-parameters: the existing statement concerns “Regular parameters of the polynomial-append closed source fibre”; it supplies neither the explicit exceptional-fibre gluing to the projective line nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference: the existing statement concerns “Dimension at a point of a quotient of a polynomial ring over a field: n minus the difference of heights”; it supplies neither the explicit exceptional-fibre gluing to the projective line nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-polynomial-quotient-dimension-lower-bound: the existing statement concerns “Dimension lower bound for a polynomial quotient over a field”; it supplies neither the explicit exceptional-fibre gluing to the projective line nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-polynomial-ring-maximal-localization-dimension: that node supplies only the polynomial-quotient dimension input, not the fibre gluing or the ambient hypersurface localization theorem.

lem-sfb-two-parameter-exceptional-fibre-gluing vs lem-weil-pbc-polynomial-ring-origin-regular-local: the existing statement concerns “The polynomial ring over a field localized at the origin is regular local of dimension d”; it supplies neither the explicit exceptional-fibre gluing to the projective line nor all its asserted coordinate maps and hypotheses. Sharing a general commutative-algebra source tag is not equality of statements.

