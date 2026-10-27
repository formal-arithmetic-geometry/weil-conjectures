# Q152 repair: lem-trf-etale-component-coordinate-identification

## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-component-coordinate-identification.json: existing statement, split; unchanged statement, five-step assembly.
- dag/nodes/sec-trace-formula/lem-trf-regular-component-etale-stalk-primes.json: statement, unsplit; no Mathlib match; Prime ideals and contractions of regular components in an étale stalk.
- dag/nodes/sec-trace-formula/lem-trf-parameter-product-prime-family-matching.json: statement, unsplit; no Mathlib match; Matching a contracted prime family with regular parameter factors.
- dag/nodes/sec-trace-formula/lem-trf-closed-subscheme-germ-family-spreading.json: statement, unsplit; no Mathlib match; Simultaneous spreading of embedded closed-subscheme germ equalities.
- dag/nodes/sec-trace-formula/lem-trf-flat-integral-target-component-generic.json: statement, unsplit; no Mathlib match; Generic points of components dominate an integral flat target.
- citations.json: a verbatim statement quotation for every node cited in every parent step.
- searches.jsonl: actual logged search commands, retained unchanged.

## Attachments

None. The upstream WeilConjectures tree has no declaration carrying the item's blueprint tag or its full statement. Sheaf/TraceFormula/EtaleComponentCoordinateIdentification.lean:88 states it but ends in sorry at line 129. AlgebraicGeometry.Scheme.Hom.apply_genericPoint_of_flat in WeilConjectures/AlgebraicGeometry/Curve/DivisorPullback.lean:55 is proved, but assumes the entire source integral; it does not state the new arbitrary-source, every-component generic-point assertion. Restricting to a closed component does not preserve flatness, so that helper cannot simply be applied to the component inclusion.

## WANTED

None. ILO/Gabber and the relevant Stacks .tex sources are present and were read locally.

## Returned point and repair

The sole numbered issue is the human's request to spread the 6588-character proof over at least two comparable independent statement-only tasks, retaining the parent statement and a proof of at most 3000 characters. This delivery creates four tasks, with no proof steps or proof dependencies in any of them. The returned steps 1--3 go to regular-component-etale-stalk-primes; 4--6 to parameter-product-prime-family-matching; 7--8 to closed-subscheme-germ-family-spreading; 9 to flat-integral-target-component-generic. These are separate local-geometric, algebraic, finite-presentation, and generic-point arguments. None restates the entire item. The neighbourhood task concerns actual embedded subschemes and simultaneous equalities and intersections; it carries the old finite-generator argument, rather than introducing a node only for a formal equality of finite sums. The elementary finite-union deletion remains explicit in the assembly.

The sandbox initially contained only dispatcher marker files, not a node, report, or search log. I therefore continued from the returned version in the live read clone, preserving its statement, nine-step argument, previous searches, source records, historical review, Lean metadata, and approved tool-use metadata. No repository git commands were run. Historical review fields are retained as historical metadata, not asserted to review this repair. No Lean files or launcher files were changed.

## Repair of the refused landing (2026-10-22)

The new return is a landing-state mismatch: the side project's earlier completion was never promoted to the live queue DAG. I retained the delivered four-task split, full original proof allocation, source citations and actual search log. I compared its parent with the current live node: the statement, statement dependencies, source, blueprint ancestry, Lean metadata, historical reviews and accepted tool-use metadata agree; only the repair-owned proof, proof dependencies, proof origin and split report differ. I rebuilt the sandbox parent from that current live node and overlaid those repair-owned fields. The required delivery command builds its commit on current origin/sheaf-dag, so this delivery promotes the actual re-split rather than an unchanged old branch.

I re-read all current cited assembly statements and every definition used to state the four tasks. All 12 retained citation quotations are still verbatim parts of the current statements; none requires a changed hypothesis or replacement citation. Step 1 still supplies proper prime extensions and exact contractions; step 2 has the covering and minimal-contraction inputs required for the matching lemma; step 3 verifies locally Noetherian before spreading; step 4 uses the explicit ideal-sum conclusion; step 5 applies flatness to the entire pullback over the integral component. The parent statement is unchanged, the assembly is 1968 characters, and the four new tasks remain statement-only. I rechecked r=0, the empty indexing family, empty intersections and disconnected sources. I re-read the named Stacks source lemmas and Gabber VIII 4.2.2(i), 4.2.4 and 4.2.9. No proof change is needed on these current interfaces.

The first repair dry run stopped before preflight because five newer live nodes sharing source tags were not compared in the retained report. I opened all five statements. Their precise distinctions are added under Not duplicates below. No new search question or statement was introduced, so the earlier logged Mathlib searches are reused without alteration.

## Review by Q152

I read the item, its unit sk-i-curve-zero and chapter, the worker contract and delivery-errors B--E, and the three levels of SETUP. The unit/chapter route is unchanged: this is the boundary-coordinate subargument below the recorded local-term-locality ancestor, not a replacement of its trace argument. I read ILO Expose VIII Remark 4.2.2(i) on printed p.118, the definition of snc families on p.119, and the parameter-chart proof of Lemma 4.2.9 on p.121 (PDF pp.124--127). These explain the geometric intent; they do not supply all the expanded algebra, so the parent keeps proof_origin.by=agent.

For the new local-prime task I read Stacks algebra.tex, Tag 07NF (lemma-regular-goes-up), and Tag 00HS (lemma-flat-going-down), and the existing statements for étale base change, étale implies smooth, smooth affine regularity ascent, regular local domains, stalks and closed immersions. Its assumptions are exactly those needed: each component is reduced irreducible and regular; the point lies in the component; étale base change gives a regular local quotient, which is nonzero because it is a local ring at a point. The flat map of quotient domains has zero kernel by going down at zero. Affine component localization gives the distinct minimal primes of I, and topological inverse images give the covering equality, without falsely commuting a reduced union with pullback. This task has no coordinate parameters or neighbourhood conclusion.

For the new parameter-family task I read more-algebra.tex Tag 0AG0, lemma-regular-local-UFD, especially the proof that an element of the maximal ideal outside its square is prime, and the statements of regular-local-cotangent-dimension and regular systems of parameters. Its hypotheses include proper primality of each q_a, distinct minimal contracted p_a, and the closed-set covering; none is inferred without the first task. The full cotangent basis makes the parameter primes incomparable. Covering first identifies every parameter prime with some q_a; contraction and minimality then identify every q_a with that same family. Both directions and uniqueness survive in the new statement. This is a ring-theoretic matching lemma, not a restatement of étale component identification.

For neighbourhood spreading I read coherent.tex Tag 01Y3, lemma-local-isomorphism, and its existing DAG node. The new statement requires equality as ideals in the same stalk, not an abstract module isomorphism. On a Noetherian affine neighbourhood both ideals are finitely generated, so all generator containments in both directions can be cleared on a common principal open. Finite families require a finite product of denominators. Sums of the restricted ideals describe fibre-product intersections. The old two-sided generator calculation is retained verbatim below for its next worker. The hypothesis locally Noetherian is essential to that calculation; it is verified in parent step 3 by the existing locally-finite-type ascent theorem.

For generic-point dominance I read algebra.tex Tag 00HS and the existing flat-morphism-affine-criterion. The target affine ring is a domain because the target is integral. A component generic point is a minimal prime in any affine open containing it, whether or not the whole source is irreducible, reduced or Noetherian. Going down below that prime forces its contraction to be zero. This applies on the entire original W, independently of the coordinate neighbourhood. The new statement deliberately does not require the entire source integral, unlike the existing upstream helper.

Parent citation checks, with each cited statement open: step 1 uses regular-component-etale-stalk-primes for the minimal p_a, proper q_a, contraction and covering clauses; its removal of finitely many closed sets is written out. Step 2 uses parameter-product-prime-family-matching for the full bijection and r=0 clause, and closed-immersion for translation of scheme equality into equality of ideals. Step 3 uses the étale definition for local finite presentation/finite type, pqf-lem-locnoeth-lft for local Noetherianness, pqf-def-locnoeth for its open restriction, and closed-subscheme-germ-family-spreading for simultaneous embedded equalities. Step 4 uses that same task's explicit intersection, empty-selection and empty-factor clauses. Step 5 uses étale-scheme-base-change for the full pullback projection, the étale definition for flatness, integral-scheme for reduced irreducible implies integral, and flat-integral-target-component-generic for the full component-generic-point assertion. citations.json records the actual statement text, not a docstring, proof, definition used as a theorem, or an invented quotation. Every non-elementary fact in this assembly is one of those cited statements; earlier steps supply only the instantiated inputs.

I checked the new statements on X=A^2 with D=V(xy), a single regular component, an empty divisor and r=0, d=0, an empty indexing family, a disconnected étale cover (the global pullback need not be irreducible), and the empty source in the generic-point task. The parameter-family lemma works for F empty exactly when r=0 under its covering hypothesis; properness excludes a prime containing 1. The spreading lemma allows an empty family, unit ideals, zero ideals and empty selections; it asserts scheme equality, not only equality of supports. Generic-point dominance does not assert surjectivity of a nonempty flat morphism. Regularity is retained to exclude multiple local branches of a singular irreducible component. No new statement is disputed and the parent statement is unchanged.

Mathlib searches were run only through the required msearch.py command, with each new node in mind and at least two semantic phrasings. All hits were read. Etale locus, minimal-prime localization, height estimates, affine ideal extensionality, generalizing maps, and generic points under open immersions do not state any complete new node or specialize in one line to it. LocalizedModule.exists_subsingleton_away is a useful ingredient for finite-generator spreading but does not give equality of a finite family of embedded subschemes and their intersection ideals as one specialization. LeanSearch was rate limited for the first two nodes and is recorded unavailable, not no match; their LeanFinder, Loogle and grep searches succeeded. The original item's old searches are preserved. All new nodes are unsplit with empty proofs, not prematurely declared Mathlib leaves.

## Original argument retained and allocation

The following is the entire returned proof, without shortening or blurring. These paragraphs are work guidance in the report, not proof sketches smuggled into the new statement-only nodes. Their source records and citations are retained here to give the next workers the same starting material.

### Returned step 1 -> lem-trf-regular-component-etale-stalk-primes

Discard from $V$ the inverse images of the finitely many $D_a$ missing $x$; these are closed and miss $w$. Put $A=\mathcal O_{X,x}$ and let $I\subset A$ be the ideal of $D$ and $\mathfrak p_a\subset A$ the ideal of $D_a$ for $x\in D_a$. The $\mathfrak p_a$ are exactly the distinct minimal primes over $I$: in an affine neighbourhood, irreducible closed subsets are $V(\mathfrak p)$, and maximality among irreducible subsets of $V(I)$ is minimality of the prime over $I$; localization retains precisely the components containing $x$. Since each $D_a$ is reduced, its defining ideal is this prime, rather than a thickening. The closed-immersion affine description identifies $\mathcal O_{D_a,x}=A/\mathfrak p_a$ and the local pullback at $w$ with $\operatorname{Spec}(R/\mathfrak p_aR)$.

Uses: def-weil-irreducible-components, def-weil-closed-immersion, def-pc-reduced-scheme, def-weil-pbc-localization-at-prime.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose VIII, Remark 4.2.2(i): distinct reduced irreducible boundary components; elementary affine/local translation.

### Returned step 2 -> lem-trf-regular-component-etale-stalk-primes

For each retained $a$, the morphism $E_a=D_a\times_X W\to D_a$ is étale by [lem-weil-pbc-etale-scheme-base-change], hence smooth by [lem-weil-pbc-etale-smooth-zero-dimensional-fibres]. Choose a regular affine neighbourhood of $x$ in $D_a$, and an affine neighbourhood of the point $(x,w)$ in its inverse image. By the affine-local meaning of smoothness in [def-sbc-smooth-morphisms], the induced ring map $C\to B$ is smooth, with $C$ Noetherian regular. By [lem-weil-pbc-regular-ring-smooth-ascent], $B$ is regular. The definition of regularity therefore makes its local ring $R/\mathfrak p_aR$ regular local. By [lem-sc-regular-local-domain] this is a nonzero domain, so $\mathfrak q_a=\mathfrak p_aR$ is a proper prime ideal of $R$.

Uses: lem-weil-pbc-etale-scheme-base-change, lem-weil-pbc-etale-smooth-zero-dimensional-fibres, def-sbc-smooth-morphisms, def-weil-regular-scheme, lem-weil-pbc-regular-ring-smooth-ascent, lem-sc-regular-local-domain.

Source: literature/stacks-project/algebra.tex; Tag 07NF, lemma-regular-goes-up; Morphisms Tags 02GO, lemma-base-change-etale, and 02GK, lemma-etale-smooth-unramified; regular local domains: Tag 00NP, lemma-regular-domain.

### Returned step 3 -> lem-trf-regular-component-etale-stalk-primes

The map $A/\mathfrak p_a\to R/\mathfrak q_a$ is flat: it is the stalk map of the étale morphism $E_a\to D_a$ from Step 2, using [def-weil-etale-morphism] and [def-weil-flat-morphism]. Both rings are domains, the source because it is a local ring of the regular scheme $D_a$, by [lem-sc-regular-local-domain]. Let $\mathfrak k$ be the contraction of the zero prime of $R/\mathfrak q_a$. Apply [lem-sc-flat-going-down] to the primes $(0)\subseteq\mathfrak k$ and the upstairs prime $(0)$. The supplied prime below $(0)$ can only be $(0)$, so $\mathfrak k=(0)$. Thus $\mathfrak q_a\cap A=\mathfrak p_a$. In particular, distinct $a$ give distinct $\mathfrak q_a$.

Uses: def-weil-etale-morphism, def-weil-flat-morphism, lem-sc-regular-local-domain, lem-sc-flat-going-down.

Source: literature/stacks-project/algebra.tex; Tag 00HS, lemma-flat-going-down, applied to the zero prime; Tag 00NP, lemma-regular-domain.

### Returned step 4 -> lem-trf-parameter-product-prime-family-matching

Put $T=t_1\cdots t_r$. By [lem-trf-regular-local-ufd-boundary-factorization], each $t_i$ is prime, so $P_i=(t_i)$ is a proper prime ideal. By [lem-weil-pbc-regular-local-cotangent-dimension], $\mathfrak m_R/\mathfrak m_R^2$ has dimension $d$. The $d$ parameters generate $\mathfrak m_R$, so their images span this $d$-dimensional vector space and form a basis. Consequently $P_i\subseteq P_j$ forces $i=j$: an equation $t_i=ct_j$ gives proportional cotangent classes, impossible for two different basis vectors. Every prime containing $T$ contains some $t_i$. Therefore the $P_i$, $1\le i\le r$, are exactly the minimal primes over $(T)$, and are pairwise incomparable. For $r=0$, $T=1$ and there is no such prime.

Uses: lem-trf-regular-local-ufd-boundary-factorization, lem-weil-pbc-regular-local-cotangent-dimension, def-weil-pbc-regular-system-of-parameters.

Source: literature/stacks-project/more-algebra.tex; Tag 0AG0, lemma-regular-local-UFD, proof opening: parameters are prime; Algebra Tag 00KU, definition-regular-local and preceding cotangent-space discussion.

### Returned step 5 -> lem-trf-parameter-product-prime-family-matching

The underlying set of $D$ is the union of the $D_a$. Taking inverse images in $\operatorname{Spec}R$ gives $V(T)=\bigcup_aV(\mathfrak q_a)$, and each $\mathfrak q_a$ contains $T$. For every $i$, the point $P_i$ therefore belongs to some $V(\mathfrak q_a)$, so $\mathfrak q_a\subseteq P_i$. Since $\mathfrak q_a$ is prime and contains $T$, it contains some $P_j$. The incomparability from Step 4 forces $j=i$, and hence $\mathfrak q_a=P_i$. This uses the inverse image of a finite union of closed sets; it does not presume that pulling back a reduced union is reduced.

Uses: .

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose VIII, Remark 4.2.2(i) and Lemma 4.2.9: elementary comparison of the boundary components in a parameter-product chart.

### Returned step 6 -> lem-trf-parameter-product-prime-family-matching

Conversely fix $a$. Primality and $T\in\mathfrak q_a$ give $P_i\subseteq\mathfrak q_a$ for some $i$. Step 5 gives $b$ with $P_i=\mathfrak q_b$. Contracting to $A$ using Step 3 gives $\mathfrak p_b\subseteq\mathfrak p_a$. Since these are distinct minimal primes over $I$, they must be equal and $b=a$. Thus $\mathfrak q_a=P_i$. Distinct $a$ give distinct primes by Step 3, and distinct $i$ give distinct primes by Step 4; Step 5 supplies all $i$. This is the desired bijection at the local ring. If $r=0$, every retained $a$ would give a proper prime containing $1$, a contradiction, so both indexing sets are empty.

Uses: .

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose VIII, Remark 4.2.2(i): elementary minimal-prime argument identifying individual components.

### Returned step 7 -> lem-trf-closed-subscheme-germ-family-spreading

Shrink $V$ to an affine neighbourhood $\operatorname{Spec}B$ of $w$, with prime $\mathfrak n$ corresponding to $w$. Since $W\to X$ is étale, it is locally of finite presentation and thus locally of finite type; [pqf-lem-locnoeth-lft] makes $W$ locally Noetherian. Thus $B$ is Noetherian. For a retained $a$, let $K_a\subset B$ define $D_a\times_X V$; Step 6 says $(K_a)_{\mathfrak n}=(t_{i(a)})_{\mathfrak n}$. Choose finite generators $k_1,\ldots,k_s$ of $K_a$. For every $j$, localization membership supplies $u_j\notin\mathfrak n$ with $u_jk_j\in(t_{i(a)})$; the reverse membership supplies $u_0\notin\mathfrak n$ with $u_0t_{i(a)}\in K_a$. On $D(u_0\cdots u_s)$ the ideals coincide. Intersect these finitely many principal neighbourhoods for all $a$. This proves equality of the closed subschemes, and preserves the empty pullbacks removed in Step 1.

Uses: def-weil-etale-morphism, pqf-lem-locnoeth-lft, pqf-def-locnoeth, def-weil-closed-immersion, def-weil-pbc-localization-at-prime.

Source: literature/stacks-project/morphisms.tex; Tag 01T6, lemma-finite-type-noetherian, and elementary finite-generator localization argument; closed immersions: Tag 01QO, lemma-closed-immersion; the local spreading principle is also illustrated by Coherent Tag 01Y3.

### Returned step 8 -> lem-trf-closed-subscheme-germ-family-spreading

Scheme-theoretic intersection is a fibre product of the closed immersions. By the fibre-product universal property, pulling it back along $V\to X$ gives the intersection of their pullbacks. On an affine chart the intersection of closed subschemes with ideals $K_a$ has ideal $\sum_aK_a$: both describe maps on which every $K_a$ vanishes. Step 7 therefore gives the ideal $(t_{i(a)}:a\text{ selected})$. If one selected component misses $x$, its pulled-back ideal is the unit ideal, so the intersection is empty. For an empty selection the intersection is $V$ itself, as required.

Uses: def-pc-fibre-product, def-weil-closed-immersion.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose VIII, Remark 4.2.2(i): scheme-theoretic intersections; elementary quotient-ring universal property.

### Returned step 9 -> lem-trf-flat-integral-target-component-generic

Finally let $z$ be the generic point of an irreducible component of $D_a\times_X W$. The projection to $D_a$ is étale by [lem-weil-pbc-etale-scheme-base-change], hence flat by [def-weil-etale-morphism]. Choose an affine open $\operatorname{Spec}C$ of $D_a$ around its image and an affine open $\operatorname{Spec}B$ around $z$ mapping into it. The ring $C$ is a domain because $D_a$ is reduced and irreducible, hence integral by [def-pc-integral-scheme]. The map $C\to B$ is flat by [lem-weil-pbc-flat-morphism-affine-criterion]. The point $z$ corresponds to a minimal prime $Q$ of $B$: a larger irreducible closed subset would contradict that its closure is a component. Put $P=Q\cap C$. Going down [lem-sc-flat-going-down] lifts $(0)\subseteq P$ to a prime $Q_0\subseteq Q$ contracting to zero. Minimality forces $Q_0=Q$, hence $P=(0)$. Thus the image of $z$ is the generic point of this nonempty affine open, and hence the generic point of the irreducible scheme $D_a$. This argument applies on all of $W$, independently of the shrinking used for the coordinate identification.

Uses: lem-weil-pbc-etale-scheme-base-change, def-weil-etale-morphism, def-pc-integral-scheme, lem-weil-pbc-flat-morphism-affine-criterion, lem-sc-flat-going-down, def-weil-irreducible-components.

Source: literature/stacks-project/algebra.tex; Tag 00HS, lemma-flat-going-down, minimal-prime specialization; Morphisms Tag 02GO, lemma-base-change-etale.

## Not duplicates

lem-trf-flat-integral-target-component-generic vs lem-trf-field-extension-residual-generic-components: The retained task treats every flat morphism to any integral scheme and gives minimal-prime contraction on arbitrary affine charts; the existing node only treats projections obtained by a field extension and describes their residual fibres and closed immersions. An arbitrary flat morphism is not such a projection.

lem-trf-flat-integral-target-component-generic vs lem-trf-flat-local-component-dimension-difference: The retained task has no local, field-algebra or finite-type restriction and concerns component generic points of schemes; the existing node assumes a flat local map of local k-algebras essentially of finite type and gives dimension and transcendence-degree identities. Its minimal-prime clause does not cover arbitrary affine flat maps.

lem-trf-flat-integral-target-component-generic vs lem-trf-generic-completed-differential-rank: The retained task applies to arbitrary flat sources over integral targets with no completion or finiteness hypotheses; the existing node concerns differentials and generic ranks for a reduced finite-type algebra over a perfect field and its specified reduced completion.

lem-trf-regular-component-etale-stalk-primes vs lem-sfb-dvr-binomial-local-geometry: The retained task identifies a finite family of component ideals, their prime extensions and contractions in an arbitrary etale stalk; the existing node computes the particular surfaces R[x,y]/(xy-pi^e) over a DVR and their regularity, dimensions and initial forms.

lem-trf-regular-component-etale-stalk-primes vs lem-sfb-finite-etale-formal-monoid-coefficient-lift: The retained task concerns arbitrary regular reduced boundary components under an etale morphism and gives all their local prime contractions and covering; the existing node constructs a finite etale coefficient lift for a complete formal monoid hypersurface. Neither its hypotheses nor its conclusion state this component-family interface.

lem-trf-regular-component-etale-stalk-primes vs lem-sfb-smooth-trait-curve-local-properties: The retained task allows any locally Noetherian ambient scheme and identifies individual component primes and their exact contractions in etale stalks; the existing node assumes a smooth relative curve over a DVR and concludes regularity, normality and local dimension formulas, without component-ideal identification.


lem-trf-flat-integral-target-component-generic vs lem-sfb-finite-scalar-extension-generic-points: The existing node is restricted to the projection of a finite field scalar extension, with finiteness of residue extensions. The new node treats an arbitrary flat morphism to any integral target and explicitly contracts each minimal prime in affine neighbourhoods; a general flat morphism is not such a scalar-extension projection.

lem-trf-flat-integral-target-component-generic vs lem-trf-flat-generic-component-incidence: The existing node lifts a component of a special fibre to a generic-fibre component whose closure contains it, and identifies its incidence in that closure. The new node instead sends every component generic point of the whole arbitrary source to the target generic point and gives its affine contraction-zero statement; that assertion is not a clause of the existing statement.

lem-trf-parameter-product-prime-family-matching vs lem-sfb-alteration-cartier-subboundary: The existing node constructs a regular alteration and a strict normal crossings support for two Cartier ideals. It neither takes a prescribed contracted prime family nor matches that family to parameter primes, which is the new ring-theoretic assertion.

lem-trf-parameter-product-prime-family-matching vs lem-sfb-snc-labelled-root-algebra-geometry: The existing node describes finite free parameter-root algebras, their regularity and geometric branches after shrinking a normal crossings chart. The new node treats a ring homomorphism and a prescribed family of proper primes with distinct minimal contractions; those matching data and its unique bijection are absent from the existing statement.

lem-trf-parameter-product-prime-family-matching vs lem-trf-parameter-product-closure-kernel: The existing node computes a saturation kernel and a scheme-theoretic closure for a product of parameters, including flat base change. The new node identifies a prescribed contracted prime family from a closed-set covering; it asserts no saturation or closure formula and the existing node supplies no such family matching.

lem-trf-regular-component-etale-stalk-primes vs lem-exc-j0-separable-finite-type-ascent: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely A nonempty regular open ascends for separable fraction fields.

lem-trf-regular-component-etale-stalk-primes vs lem-per-complete-local-branch-approximation: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Two compatible trait approximations of a complete local pair.

lem-trf-regular-component-etale-stalk-primes vs lem-per-completed-invertible-kummer-monoid-extension: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Completed local normal form for invertible Kummer monoid extensions.

lem-trf-regular-component-etale-stalk-primes vs lem-per-finite-etale-formal-monoid-coefficient-lift: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Finite etale local factors lift from formal monoid coefficients.

lem-trf-regular-component-etale-stalk-primes vs lem-per-regular-gysin-calculus: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Gysin purity calculus on regular affine schemes.

lem-trf-regular-component-etale-stalk-primes vs lem-per-regular-lci-geometric-calculus: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Regular-immersion geometry and intrinsic virtual dimension.

lem-trf-regular-component-etale-stalk-primes vs lem-sbc-etale-regular-divisor-base-change: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Regular divisor under etale base change.

lem-trf-regular-component-etale-stalk-primes vs lem-sbc-root-split-cover-cyclic-charts: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Cyclic orbit classification for covers split by one root extension.

lem-trf-regular-component-etale-stalk-primes vs lem-sfb-dvr-nodal-chart-blowup-calculus: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Arithmetic nodal charts and their singular-point blowups.

lem-trf-regular-component-etale-stalk-primes vs lem-trf-etale-component-coordinate-identification: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely the full parent coordinate identification, which combines this argument with three independent tasks.

lem-trf-regular-component-etale-stalk-primes vs lem-weil-pbc-degree-p-extension-regular: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Adjoining an n-th root of an element with unit derivative preserves regularity.

lem-trf-regular-component-etale-stalk-primes vs lem-weil-pbc-finite-type-over-g-ring: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Finite type algebras over G-rings are G-rings.

lem-trf-regular-component-etale-stalk-primes vs lem-weil-pbc-geometric-regularity-separable-extension: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Geometric regularity over a separable algebraic extension.

lem-trf-regular-component-etale-stalk-primes vs lem-weil-pbc-geometrically-regular-finitely-generated-extensions: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Geometric regularity tested on finitely generated field extensions.

lem-trf-regular-component-etale-stalk-primes vs lem-weil-pbc-geometrically-regular-smooth-ascent: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Geometric regularity ascends along smooth ring maps.

lem-trf-regular-component-etale-stalk-primes vs lem-weil-pbc-polynomial-complete-local-formal-fibres: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Formal fibres of a polynomial ring over a complete local ring at a maximal ideal over the closed point.

lem-trf-regular-component-etale-stalk-primes vs lem-weil-pbc-polynomial-complete-local-generic-fibre: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Generic polynomial formal fibres over complete local domains.

lem-trf-regular-component-etale-stalk-primes vs lem-weil-pbc-regular-ring-smooth-ascent: The new node supplies the whole localized component-prime family, regular quotient domains, exact contraction identities and its covering equality; the existing node states a different interface, namely Regularity ascends along smooth ring maps.

lem-trf-parameter-product-prime-family-matching vs lem-per-divisor-purity-strict-local-criterion: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Strict-local complement criterion for regular divisor purity.

lem-trf-parameter-product-prime-family-matching vs lem-per-gabber-prime-to-ell-regular-cover: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Gabber regular pairs cover the prime-to-ell alteration site.

lem-trf-parameter-product-prime-family-matching vs lem-per-noetherian-log-pair-strict-resolution: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Strict boundary resolution of an excellent Noetherian log regular pair.

lem-trf-parameter-product-prime-family-matching vs lem-per-regular-boundary-divisorial-chart: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Divisorial charts of a regular strict normal crossings pair.

lem-trf-parameter-product-prime-family-matching vs lem-per-regular-prime-divisor-local-equations: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Local equations and generic DVR of a prime divisor on a regular scheme.

lem-trf-parameter-product-prime-family-matching vs lem-per-snc-boundary-parameter-criterion: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Local parameter criterion for a strict normal crossings boundary.

lem-trf-parameter-product-prime-family-matching vs lem-per-snc-parameter-root-quotient: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Etale-local parameter-root quotients of invertible-order torsors.

lem-trf-parameter-product-prime-family-matching vs lem-per-strict-local-divisor-low-kummer: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Low-degree Kummer cohomology of a strict-local regular divisor complement.

lem-trf-parameter-product-prime-family-matching vs lem-per-surface-codimension-one-cartier-part: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Codimension-one Cartier part of a subscheme on a regular surface.

lem-trf-parameter-product-prime-family-matching vs lem-sc-smooth-normal: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Smooth schemes are normal.

lem-trf-parameter-product-prime-family-matching vs lem-sfb-nested-open-regular-alteration: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Regular alteration adapted to nested opens and a prescribed finite cover.

lem-trf-parameter-product-prime-family-matching vs lem-sfb-point-blowup-fibre-defects: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Geometric fibre defects in regular surface point blowups.

lem-trf-parameter-product-prime-family-matching vs lem-sfb-snc-boundary-parameter-criterion: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Local parameter criterion for a strict normal crossings boundary.

lem-trf-parameter-product-prime-family-matching vs lem-sfb-snc-tame-root-etale-extension: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states A finite tame cover has an etale model after a simultaneous finite root base change.

lem-trf-parameter-product-prime-family-matching vs lem-trf-etale-component-coordinate-identification: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states the full parent coordinate identification, which combines this argument with three independent tasks.

lem-trf-parameter-product-prime-family-matching vs lem-trf-finite-projective-local-free: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Finitely presented modules locally free at primes are finite projective.

lem-trf-parameter-product-prime-family-matching vs lem-trf-regular-local-regular-ring-ufd: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states The proved source-library regular local UFD theorem.

lem-trf-parameter-product-prime-family-matching vs lem-trf-regular-local-ufd-boundary-factorization: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Boundary-unit factorization in a regular local ring.

lem-trf-parameter-product-prime-family-matching vs lem-trf-snc-divisorial-log-chart: The new node matches an arbitrary prescribed contracted prime family with parameter factors under a covering hypothesis; the existing node instead states Divisorial charts of a smooth strict normal crossings pair.

lem-trf-closed-subscheme-germ-family-spreading vs lem-pc-c3-coherent-generic-local-free-model: The new node gives simultaneous equality of specified embedded closed subschemes near one stalk and all intersection ideals; the existing node instead states A local closed free model at a maximal-ideal-annihilated generic stalk.

lem-trf-closed-subscheme-germ-family-spreading vs lem-trf-etale-component-coordinate-identification: The new node gives simultaneous equality of specified embedded closed subschemes near one stalk and all intersection ideals; the existing node instead states the full parent coordinate identification, which combines this argument with three independent tasks.

lem-trf-closed-subscheme-germ-family-spreading vs lem-trf-implicit-taylor-coordinate-calculus: The new node gives simultaneous equality of specified embedded closed subschemes near one stalk and all intersection ideals; the existing node instead states Implicit transverse coordinates and regular coefficient calculus.

lem-trf-closed-subscheme-germ-family-spreading vs lem-weil-pbc-coherent-generic-point-closed-descent: The new node gives simultaneous equality of specified embedded closed subschemes near one stalk and all intersection ideals; the existing node instead states Let X be a Noetherian scheme, i : Z → X a closed immersion with Z integral and eta its generic point.

lem-trf-closed-subscheme-germ-family-spreading vs lem-weil-pbc-coherent-generic-point-ideal-inclusion: The new node gives simultaneous equality of specified embedded closed subschemes near one stalk and all intersection ideals; the existing node instead states A coherent module killed by the maximal ideal at the generic point of an integral closed subscheme contains a pushforward of ideal sheaves, isomorphically near that point.

lem-trf-closed-subscheme-germ-family-spreading vs lem-weil-pbc-coherent-local-isomorphism: The new node gives simultaneous equality of specified embedded closed subschemes near one stalk and all intersection ideals; the existing node instead states A map of coherent modules injective, surjective or bijective on one stalk is so on a neighbourhood.

lem-trf-closed-subscheme-germ-family-spreading vs lem-weil-pbc-finite-type-local-coefficients: The new node gives simultaneous equality of specified embedded closed subschemes near one stalk and all intersection ideals; the existing node instead states Finite type module sheaves have finite local coefficient expansions.

lem-trf-closed-subscheme-germ-family-spreading vs lem-weil-pbc-module-finite-type-surjective-on-stalk: The new node gives simultaneous equality of specified embedded closed subschemes near one stalk and all intersection ideals; the existing node instead states A map onto a finite type module that is surjective on one stalk is surjective near that point.

lem-trf-flat-integral-target-component-generic vs det-pe-wc-rings-retraction: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Retraction of a faithfully flat ind-étale algebra over a w-contractible ring.

lem-trf-flat-integral-target-component-generic vs lem-pc-dim-base-change: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Dimension is unchanged under base change along field extensions.

lem-trf-flat-integral-target-component-generic vs lem-per-catenary-completion-hyperplane: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Hyperplane reduction of a non-equidimensional completion.

lem-trf-flat-integral-target-component-generic vs lem-per-etale-immediate-component-criterion: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Reduced local closure and strict-local component criterion.

lem-trf-flat-integral-target-component-generic vs lem-per-flat-equidimensional-catenary-descent: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Flat descent of catenarity and equidimensionality.

lem-trf-flat-integral-target-component-generic vs lem-per-henselian-component-dimension: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states One-dimensional components and strict henselization.

lem-trf-flat-integral-target-component-generic vs lem-sbc-flat-base-change-closed-fiber-generalizations: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Generalizations lift in the original closed fibre of a flat base-changed chart.

lem-trf-flat-integral-target-component-generic vs lem-sbc-flat-power-series-chart-generic-image: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Generic closed-fibre image of a flat chart over the changed base.

lem-trf-flat-integral-target-component-generic vs lem-sbc-mv-power-series-quotient-kernel: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Kernel of coefficient reduction modulo a finitely generated ideal.

lem-trf-flat-integral-target-component-generic vs lem-sc-faithfully-flat-local-dimension: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Faithfully flat local maps do not lower Krull dimension.

lem-trf-flat-integral-target-component-generic vs lem-sc-flat-going-down: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Flat ring maps satisfy going down.

lem-trf-flat-integral-target-component-generic vs lem-sfb-common-field-semilinear-induction: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Common normal constants and induction of finite semilinear scheme actions.

lem-trf-flat-integral-target-component-generic vs lem-trf-completed-conormal-determinant-comparison: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Completed algebraic and continuous formal conormal determinants with generic normalization.

lem-trf-flat-integral-target-component-generic vs lem-trf-etale-component-coordinate-identification: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states the full parent coordinate identification, which combines this argument with three independent tasks.

lem-trf-flat-integral-target-component-generic vs lem-trf-etale-normal-domain-finite-factors: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Etale algebras over a normal domain have finitely many normal domain factors.

lem-trf-flat-integral-target-component-generic vs lem-trf-flat-dense-generic-fibre-pure-dimension: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Pure dimension of fibres of a flat family with dense pure-dimensional generic fibre.

lem-trf-flat-integral-target-component-generic vs lem-trf-normalization-completed-product-comparison: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Recover normalization by intersection with normalized completed branches.

lem-trf-flat-integral-target-component-generic vs lem-trf-smooth-local-tangent-cone-extension: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Tangent cone and minimal-prime dimensions of an essentially smooth local extension.

lem-trf-flat-integral-target-component-generic vs lem-weil-pbc-flat-height-formula: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Height formula for flat ring maps of Noetherian rings.

lem-trf-flat-integral-target-component-generic vs lem-weil-pbc-fpqc-descend-flat: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Being flat descends along fpqc coverings (Stacks 02L2).

lem-trf-flat-integral-target-component-generic vs lem-weil-pbc-regularity-rk-goes-up: The new node concerns every generic point of every component of an arbitrary flat source over an integral target, with its affine contraction-zero form; the existing node instead states Serre regularity in codimension ascends along flat maps with regular fibres.

Additional near matches: regular-component-etale-stalk-primes vs lem-sbc-etale-regular-divisor-base-change: that node assumes a principal regular divisor in an already regular affine ambient ring, and gives no arbitrary component-prime contraction family. parameter-product-prime-family-matching vs lem-sfb-snc-boundary-parameter-criterion and lem-per-snc-boundary-parameter-criterion: these are scheme-level snc equivalences, not a ring-map matching for the specified q_a; they neither state the needed contraction hypotheses nor give that finite-family interface. closed-subscheme-germ-family-spreading vs lem-weil-pbc-coherent-local-isomorphism: an abstract coherent-sheaf morphism becoming an isomorphism does not itself state equality of two given embedded ideals; constructing and comparing the finite ideal quotients is the argument assigned here. flat-integral-target-component-generic vs lem-fin-etale-normal-components: finite étale over a normal base and component decomposition is different from arbitrary flat-source component generic-point dominance.

Whole-DAG searches used the exact source tags 07NF, 0AG0, 01Y3 and 00HS and the notions prime contraction, regular étale components, minimal-prime families, ideal equality at a stalk, and flat generic points. Whole-blueprint searches used those tags and 'minimal primes', 'generic points flat', 'regular components', 'generic point', 'parameter', 'localization ideals', 'closed subscheme equality', and 'ideal'. The imported blueprint searches found no matching statement; generic-point and ideal infrastructure results were distinguished by their actual statements. The new blueprint.from fields use the reported nearest ancestor lem-trf-local-term-locality and prepend this item to its original via list.

## Completion and validation

All mathematical repair work is complete. Parent proof length: 1968 characters, with no step exceeding 2000 characters. Four new nodes, zero Mathlib leaves. The delivery dry run and final push are recorded below when completed.

Final dependency audit: I also opened def-sbc-closed-immersion-ideal-sheaf and added it to the spreading task, so its global defining ideals refer to the actual kernel ideal-sheaf interface (whose affine sections are precisely the ideal of the closed immersion). The verbatim quotations in citations.json were updated accordingly. The first dry run exited successfully with preflight passed at 003e4862324; a final dry run checks this dependency addition before pushing.

## Current-base repair verification (2026-10-22, Q152)

The required initial dry run completed successfully at 6f5339f7400. I then reconstructed the delivery parent from the current read-clone node, retaining all current non-repair fields and overlaying only the repaired proof, proof dependencies, proof origin and split report. The parent differs from that current node only in: proof, proof_deps, proof_origin, split_report. The item statement and statement dependencies are exactly unchanged. The delivery tool, rather than any manual repository git operation, prepares the commit on the current server branch.

For this retry I strengthened assembly step 2: it now explicitly checks finiteness of the retained component family, distinct minimal contractions, proper prime extensions, the closed-set covering and the full regular parameter system before applying the ring matching lemma. These inputs are respectively the finite original family, the exact clauses of step 1, its covering combined with IR=(T), and the original hypotheses. Thus this retry includes an actual proof clarification as well as the current-base metadata refresh.

I reopened every current external assembly dependency. The closed-immersion statement supplies the affine quotient/ideal interface in step 2; the etale definition supplies flatness and local finite presentation in steps 3 and 5; the locally-finite-type ascent statement applies because X is locally Noetherian; the locally-Noetherian definition explicitly includes restriction to open subschemes; the etale base-change statement applies to the full pullback projection in step 5; and integral-scheme explicitly equates integral with nonempty reduced irreducible. None of these current statements requires a new hypothesis or a changed citation. All 12 retained quotes were checked against the statements, and their step/node pairs are exactly the uses pairs in the five assembly steps.

Current external assembly statement fingerprints (SHA-256, to make future changed-citation comparisons explicit):

- def-pc-integral-scheme: 04d6f2107cc5c05e0363f302f4274905ccdcc59bab1576aedaa3241ff894fbd5
- def-weil-closed-immersion: 216d86694ce9fe6fd87bf65dbf80c3bf4b45f95edbdf59729ab185c91587ef6c
- def-weil-etale-morphism: f8c6627b2bdc2567a354e93640c1745912371c13b1bc9aac2e10876a466cd040
- lem-weil-pbc-etale-scheme-base-change: 0bb689daa1ac67502f75c6f3c0f33c07b3f0976cd99efc90630eab3d31b056f3
- pqf-def-locnoeth: 207f8547d2648e482d85bbc0e193d362d93e850f063539578498762ce69949c0
- pqf-lem-locnoeth-lft: a19364f7ee40c944d6d18e19eb2e603bf3271018ee019bf4272a5101ab3bf352

I re-read Gabber VIII Remark 4.2.2(i), definition 4.2.4 and Lemma 4.2.9, and the local Stacks statements and proofs at algebra.tex labels lemma-flat-going-down and lemma-regular-goes-up, more-algebra.tex lemma-regular-local-UFD, coherent.tex lemma-local-isomorphism, and morphisms.tex lemma-finite-type-noetherian, lemma-base-change-etale and lemma-etale-smooth-unramified. The statements still support the retained allocation: regular component quotients and contractions; incomparable parameter primes and finite-family matching; finite-generator spreading and sums of ideals; and minimal-prime contraction under flatness. The latter assertion uses the whole source rather than incorrectly assuming a closed component is flat.

I rechecked the empty divisor/r=0 and d=0 cases, the empty spreading family and empty intersection, and disconnected or empty flat sources. Each new task remains statement-only with an empty proof and proof_deps, and is strictly smaller than the full item. The assembly now has 2207 characters; no step exceeds 2000. The statements and search questions have not changed, so the existing search log and Mathlib records are retained without rerunning them. The current dry run checks all same-tag duplicate comparisons; final delivery follows only after it exits successfully.

## Current landing repair, 2026-10-23

The initial required dry run exited before server preflight because six newer live nodes share Tags 00HS or 07NF with the retained tasks. I opened every one of their current statements and added one explicit distinction per pair under Not duplicates. None states either retained task or a generalization applicable under its hypotheses: three concern field-extension residual fibres, finite-type local dimension formulas or a specified completion; the other three concern a DVR binomial surface, formal monoid coefficient lifting or smooth curves over a trait. These comparisons address current-DAG changes; they are not an unchanged re-push.

I compared the retained parent with the current read clone: only proof, proof_deps, proof_origin and split_report differed. I rebuilt the parent from that current live record and overlaid those four repair-owned fields, retaining the entire statement and all other metadata. All six saved external statement SHA-256 fingerprints still match; I nevertheless re-read each statement, all four task statements and their statement-definition dependencies. The 12 quotations remain verbatim, and the step/node pairs still exactly cover the assembly citations. The logged searches were read and retained because neither the statements nor search questions changed. The project declaration at Sheaf/TraceFormula/EtaleComponentCoordinateIdentification.lean still ends in sorry; the proved upstream integral-source generic-point helper does not supply the arbitrary-source component task.

I corrected doubled backslashes in the parent assembly's TeX without altering its argument. The five steps still check every hypothesis: the first gives distinct minimal contractions and proper prime extensions with the covering; the second uses the assumed regular parameter system and full product equality; the third establishes local Noetherianness before applying finite-family spreading; the fourth uses its sum-of-ideals conclusion; the fifth applies the generic-point lemma to the full flat pullback over a nonempty reduced irreducible component. Re-reading Gabber VIII 4.2.2(i), 4.2.4 and 4.2.9 and Stacks 07NF, 00HS, 0AG0 and 01Y3 confirms the previous argument allocation. The empty divisor, r=d=0, empty family, empty intersection and disconnected or empty source checks still apply. No new nodes, new mathematical assertions or new searches were added in this retry.

Current assembly length: 2207 characters; each step is below 2000 characters. Four statement-only tasks, no Mathlib leaves. Final server dry-run result and delivery are recorded only after the commands exit.
