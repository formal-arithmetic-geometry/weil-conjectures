# Worker report: lem-trf-toric-realization-finite-type

## Files written

- Parent: statement unchanged, short assembly of three independently claimable arguments and the elementary finite-disjoint-union step.
- lem-trf-monoscheme-finite-chart-components: statement, unsplit, no complete Mathlib match; finite monoid topology, generic lattices, chart domains and generators, dense open gluing and integral realized components (old Steps 1–4).
- lem-trf-lattice-torus-coordinates-action: statement, unsplit, no complete Mathlib match; basis coordinates, Hopf compatibility, coaction gluing, arbitrary-base Laurent presentation and finite type (old Steps 5–6).
- lem-trf-split-lattice-torus-projection: statement, unsplit, no complete Mathlib match; square-zero unit lifting, section and geometric/reduced-base product (old Steps 7–9).
- citations.json: verbatim statements for every parent proof citation. searches.jsonl: actual search command log. repair.py: sandbox-only generation script.

## Attachments

None. Read lean/Sheaf/AlgebraicGeometry/ToricRealizationFiniteType.lean: AlgebraicGeometry.Monoscheme.toric_realization_finite_type ends with sorry. Searches of lean/WeilConjectures for the tag, monoschemes, toric realization and split tori found no finished statement. Canonical torus group abbreviations do not prove the theorem. The Lean statement and docstring cover the same clauses as the parent; no Lean is edited.

## WANTED

None. The sources below are present and were read locally.

## Returned defect and repair

The return requires spreading 8962 characters of work into at least two comparable statement-only nodes and a parent assembly at most 3000 characters. I created three nodes. Their assigned original argument lengths are 3681, 2170, 2371 characters respectively (measured below by the retained originals); the ten old steps are preserved verbatim below, with sources and dependency lists. Step 10 stays in the parent. Each new node introduces its own objects, asserts intermediate results needed to carry out its assigned argument, and contains no proof or proof-dependency list. No new node restates the full parent. The generic-field formulation changes no argument: all the old computations and the cited domain lemma work over any field. The parent statement is byte-for-byte unchanged.

The sandbox initially contained only dispatcher marker files, no item, report or search log. I therefore copied the current returned parent from the read-only repository; there was no previous sandbox split/report on which to run an initial dry run. The copy preserves every existing search record and all metadata. Only the proof, proof-dependencies and split report are changed. The last repair had verified the connected-component torsion-free condition; the new coordinate node states it explicitly again.

## Not duplicates

lem-trf-monoscheme-finite-chart-components vs def-trf-monoscheme-toric-realization: the existing node defines localization gluing and torus notation; the new node proves finite component topology, generic lattice identifications, dense torus embeddings and integral finite-type realization.
lem-trf-monoscheme-finite-chart-components vs lem-trf-affine-monoid-algebra-normalization: the existing affine ring normalization theorem does not prove the topology of a glued monoscheme, component correspondence, or common dense-open gluing; it is the domain input to the retained argument.
lem-trf-monoscheme-finite-chart-components vs lem-trf-fg-torsionfree-group-free: the latter supplies the basis once finite generation and torsion-freeness are established; it does not give the generic lattice or component geometry.
lem-trf-lattice-torus-coordinates-action vs def-sc-gm-ga: the rank-one group definition does not identify a general lattice torus as a group scheme, glue chart coactions, or provide arbitrary-base finite Laurent presentations.
lem-trf-lattice-torus-coordinates-action vs def-trf-monoscheme-toric-realization: notation for the coaction is not the coordinate comparison, action identities, overlap compatibility or affine product presentation.
lem-trf-split-lattice-torus-projection vs lem-trf-geometrically-reduced-base-change: the existing algebraic tensor-product theorem assumes geometric reducedness, and says nothing about lattice algebras, smoothness or the projection section; the new argument establishes that hypothesis for the torus and applies it. It reuses rather than duplicates Stacks Tag 034N (algebra.tex, lemma-geometrically-reduced-any-reduced-base-change).
lem-trf-split-lattice-torus-projection vs lem-trf-toric-monoid-comparison: the latter's clause (iii) compares smooth monoscheme maps and their realizations, not arbitrary schemes Y or reduced torus products; moreover it is a downstream user, not a substitute for this split.

Whole-DAG statement/title searches for monoscheme, generic lattice, Laurent, split torus and smooth/reduced torus products found only these neighboring notions and results, no existing statement of a new node. Whole-blueprint searches using blueprint_refs.py: toric, Laurent, monoscheme, group algebra, smooth torus, monomial coaction, reduced product, 034N, finite chart. The only nearby blueprint hits are rank-one def-sc-gm-ga, unrelated Laurent reciprocity and lem-wf-affine-product-reduced (algebraically closed base and affine varieties, no smoothness/section or general-field statement). Blueprint ancestry is preserved under lem-trf-local-term-locality; this is its recorded historical alteration branch, not a replacement for the current contracting-correspondence unit route.

## Review by Q30

I read ILO Exposé VIII printed pp.98–104 and 106: Remark 3.1.4 gives finite spectrum and its empty generic prime, 3.1.9 supplies the fineness/torsion-free conventions, Remark 3.1.10(ii) gives the component structure, Proposition 3.2.2 gives localization-compatible realization gluing, and 3.2.4–3.2.5 gives the dense torus and its action without requiring saturation. These justify the source of the first new node. I read the same 3.2.4–3.2.5 for the second node and Lemma 3.2.12(i), whose smoothness calculation is expanded in old Steps 6–7, for the Laurent-coordinate and third-node source. I read algebra.tex at lemma-geometrically-reduced-any-reduced-base-change (Tag 034N), together with the actual existing lemma statement: arbitrary reduced R is permitted and no finite-generation or nonzero hypothesis is needed.

For parent Step 1, I checked the first new statement explicitly includes reduced finite type, integral connected components, common dense torus and finite free generic lattice, under exactly the fine torsion-free finite-cover hypotheses. For Step 2, the second new statement supplies the group-scheme isomorphism, every Hopf operation, actual glued canonical action, finite type of the torus and finite type of its product; the component is nonempty, connected, fine and torsion free and has a finite cover inherited from the parent cover, as required. For Step 3, the third new statement allows the supplied finite basis and any Y, giving smoothness, surjectivity and reducedness under exactly reducedness of Y; setting Y=Spec Q is valid. Step 4 uses only the three actual definition statements for reducedness, finite type and connectedness and explicitly proves the local-ring, finite-cover and clopen-component assertions. citations.json quotes the full verbatim statements, so every clause used can be checked directly, rather than inferred from a cited proof.

I opened all fourteen dependency statements of the old proof. In particular the affine-monoid normalization node explicitly asserts domains (not just normalization), the finitely generated torsion-free group node explicitly gives an integral basis, and the reduced-base-change node explicitly assumes all extension fields and concludes reduced tensor product. The retained proofs verify each hypothesis: chart group completions coincide with the generic stalk, finite chart generators generate the group, torsion-freeness is inherited from stalks, L as a monoid has generators ±b_i, K[L] is a domain over every extension field, and each affine R in reduced Y is reduced. Smoothness uses exactly finite presentation plus the affine square-zero lifting condition stated in def-sbc-smooth-morphisms. It does not infer formal smoothness only from a name or normality from saturation. No off-unit theorem is newly used by the parent.

I checked the B–E error list: no proof or proof sketch is stored in any new-node statement, every object and hypothesis is introduced, TeX is escaped once, all notions have definition dependencies or are written explicitly, all searches recorded are actual msearch.py calls (including their exact query strings), Mathlib fragments are not called whole-node matches, and new nodes are genuine proper portions of the returned work. No cycles arise through the parent: the new statements depend only on existing definitions and have empty proof_deps. The parent has no step over 2000 characters. Small cases checked: empty monoscheme (zero components), zero monoid and rank-zero torus, nonsaturated monoid <2,3> (domain but not asserted normal), groups with nontrivial units, nonseparated chart gluings, empty Y/zero R, reducible reduced Y, and fields of positive characteristic. The statements do not assume saturation, sharpness, separation, irreducibility of Y or characteristic zero.

Search hits read include AddMonoidAlgebra.finiteType_of_fg (RingTheory/FiniteType.lean:435), the domain instance (Algebra/MonoidAlgebra/NoZeroDivisors.lean:131), MonoidAlgebra.domCongr (Algebra/MonoidAlgebra/Basic.lean:311), MonoidAlgebra.instHopfAlgebra (RingTheory/HopfAlgebra/MonoidAlgebra.lean:51), LaurentPolynomial.comul_T and general smooth/reduced scheme primitives. They cover parts of the argument, not one-line specializations of the new statements. Both natural-language phrasings for each node were read, alongside Loogle and local grep hits. No absence claim is based on an unavailable service.

## Preserved argument handoff

The following is the full returned proof, not a shortened replacement. These are handoff notes for workers on the new statement-only nodes, not additional parent proof steps. New node A receives Steps 1–4, B Steps 5–6, C Steps 7–9. All original sources and every original dependency are retained here. The first worker should reuse the existing affine-domain and finite-free-group lemmas; the third should reuse the existing Tag 034N reduced tensor lemma. They must search any further needed sublemma before creating one.

### Returned Step 1 → lem-trf-monoscheme-finite-chart-components

First examine the finite monoid charts in [def-trf-fine-fan-blowup] and [def-trf-monoscheme-toric-realization]. A prime ideal of a monoid generated by $p_1,\ldots,p_n$ is determined by which generators it contains: a sum belongs to the prime ideal exactly when some summand does. Thus its spectrum is finite. The empty prime is contained in every prime, so its point $\eta$ belongs to every nonempty basic open; its stalk inverts all generators and is $P^{\rm gp}$. In a finite affine cover the underlying space of $M$ is therefore finite. For any $x\in M$, all its generalizations lie in any affine chart containing $x$; that chart has the unique generic point just described. It is the unique generic point generalizing $x$ in $M$: any generalization lies in the same chart and specializes from its empty prime. Denote it by $\eta(x)$. On each affine chart $\eta(x)$ is constant. Consequently the sets $M_\eta=\{x:\eta(x)=\eta\}$ are open and closed, cover $M$, and are finite in number. Each is the closure of its point $\eta$, hence irreducible and connected. They are exactly the connected components. Each affine chart lies in just one $M_\eta$.

Uses: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization, def-weil-connected-scheme

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose VIII, Remark 3.1.4(i)--(ii) and Remark 3.1.10(ii), printed pp.98--100; explicit prime-ideal argument.

### Returned Step 2 → lem-trf-monoscheme-finite-chart-components

On a nonempty component choose an affine chart $\operatorname{Spec}_{\rm mon}P$. Its generic stalk is $L=\mathcal M_\eta=P^{\rm gp}$ by Step 1, and the same stalk identifies every other chart's group completion with $L$. Finitely many generators of $P$ generate $P^{\rm gp}$ as a group. Torsion-freeness of the stalk group completion is an assumption on $M$ in [def-trf-monoscheme-toric-realization]. Apply [lem-trf-fg-torsionfree-group-free] to obtain a basis $b_1,\ldots,b_r$ of $L$. This verifies both hypotheses of that node without assuming that $P$ is saturated or sharp.

Uses: def-trf-monoscheme-toric-realization, lem-trf-fg-torsionfree-group-free

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose VIII, 3.1.9 and 3.2.4, printed pp.99,103; finite free generic lattice used also in the proof of Lemma 3.2.12(ii), p.104.

### Returned Step 3 → lem-trf-monoscheme-finite-chart-components

For each chart $P$, apply [lem-trf-affine-monoid-algebra-normalization] with $k=\mathbf Q$. Its hypotheses hold because $P$ is fine and $P^{\rm gp}=L$ is torsion free. In particular $\mathbf Q[P]$ is an integral domain. Hence every localization at a prime is reduced: if $(a/s)^n=0$ in a localization of a domain then $a=0$. The chart realizations cover $X$ by [def-trf-monoscheme-toric-realization], so all local rings of $X$ are reduced, precisely [def-pc-reduced-scheme]. Independently, if $p_1,\ldots,p_n$ generate $P$, their monomials generate $\mathbf Q[P]$ as a $\mathbf Q$-algebra, since $e^{\sum a_i p_i}=\prod(e^{p_i})^{a_i}$. The finite monoid-chart cover gives a finite affine cover of $X$ by these finitely generated algebras. This is finite type by [def-weil-finite-type-morphism].

Uses: lem-trf-affine-monoid-algebra-normalization, def-trf-monoscheme-toric-realization, def-pc-reduced-scheme, def-weil-finite-type-morphism

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose VIII, Proposition 3.2.2, 3.2.4 and Lemma 3.2.12(ii), printed pp.103--104; domain and algebra-generator arguments.

### Returned Step 4 → lem-trf-monoscheme-finite-chart-components

The disjoint clopen decomposition of Step 1 is respected by realization: its gluing uses no overlap between different $M_\eta$, by [def-trf-monoscheme-toric-realization]. Write $X_\eta=\mathbf Q[M_\eta]$. On a chart with generators $p_i$, put $a=\sum_i p_i$ (use $a=0$ if there are none). Inverting $a$ inverts each $p_i$, because $-p_i=-a+\sum_{j\ne i}p_j$; thus $P[a^{-1}]=L$. The ring identification $\mathbf Q[P]_{e^a}=\mathbf Q[L]$ sends $e^p/(e^a)^n$ to $e^{p-na}$, with the inverse given by the same fraction rule. These are the localization maps used in gluing, so every chart of $X_\eta$ contains the same open $T=\operatorname{Spec}\mathbf Q[L]$. It is dense in each chart: the zero prime of the domain $\mathbf Q[P]$ belongs to $D(e^a)$ and to every nonempty open. The zero prime of $\mathbf Q[L]$ likewise makes $T$ irreducible. Every nonempty open of $X_\eta$ therefore meets $T$, and any two such opens meet, since their intersections with $T$ do. Thus $X_\eta$ is irreducible and nonempty. Step 3 makes it reduced, hence integral by [def-pc-integral-scheme]. The finitely many $X_\eta$ are consequently exactly the connected components of $X$.

Uses: def-trf-monoscheme-toric-realization, def-trf-fine-fan-blowup, def-pc-integral-scheme, def-weil-connected-scheme

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose VIII, Proposition 3.2.2 and 3.2.4, printed p.103; dense torus and component argument expanded from Remark 3.1.10(ii).

### Returned Step 5 → lem-trf-lattice-torus-coordinates-action

The basis from Step 2 gives inverse ring maps $\mathbf Q[L]\rightleftarrows\mathbf Q[t_1^{\pm1},\ldots,t_r^{\pm1}]$ by $e^{\sum n_i b_i}\mapsto\prod t_i^{n_i}$ and $t_i\mapsto e^{b_i}$. They preserve products and the unit by the unique integer-coordinate expressions, so [def-weil-affine-spectrum] gives the required scheme isomorphism. The torus coaction, counit and inverse send $e^l$ respectively to $e^l\otimes e^l$, $1$ and $e^{-l}$; in these coordinates they are coordinate multiplication, the tuple $(1,\ldots,1)$ and coordinate inversion. The group identities hold on every $e^l$. Each component is torsion free, since its stalks are stalks of the assumed torsion-free $M$; Step 2 identifies its generic group with the finite free $L$. Thus the torsion-free connected-component hypothesis of [def-trf-monoscheme-toric-realization] holds. The chart action is its specified coaction; its action and unit identities follow on $e^p$ from $e^p\otimes e^p\otimes e^p$ and $e^p$. Localization respects these formulas: when $e^a$ is inverted, its coaction is inverted to $e^{-a}\otimes e^{-a}$. Hence the actions agree on overlaps and give the stated action on $X_\eta$. The displayed scheme isomorphism respects the group operations.

Uses: def-weil-affine-spectrum, def-trf-monoscheme-toric-realization

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose VIII, 3.2.4--3.2.5, printed p.103; group law and coaction on the monomial basis.

### Returned Step 6 → lem-trf-lattice-torus-coordinates-action

Fix any $\mathbf Q$-scheme $Y$ for the moment. Over $V=\operatorname{Spec}R\subseteq Y$, the projection $T\times_{\mathbf Q}Y\to Y$ has algebra $R[t_1^{\pm1},\ldots,t_r^{\pm1}]$, as can be checked by its functor of points using [def-pc-fibre-product] and [def-weil-affine-spectrum]: a map to this affine scheme is a map to $V$ and $r$ units. This algebra has the finite presentation
$$R[t_1,\ldots,t_r,u_1,\ldots,u_r]/(t_i u_i-1\mid1\le i\le r).$$
These affine preimages cover the product. Thus the projection is locally of finite presentation in exactly the sense of [def-sbc-locally-finite-presentation]. If $Y$ is finite type over $\mathbf Q$, take its finite affine cover by finitely generated $\mathbf Q$-algebras as in [def-weil-finite-type-morphism]. Adjoining these $2r$ generators gives a finite such cover of $T\times Y$, so the product is finite type. For $Y=\operatorname{Spec}\mathbf Q$ this also proves finite type of $T$.

Uses: def-pc-fibre-product, def-weil-affine-spectrum, def-sbc-locally-finite-presentation, def-weil-finite-type-morphism

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose VIII, 3.2.4 and Lemma 3.2.12(i), printed pp.103--104; Laurent presentation over an arbitrary base written explicitly.

### Returned Step 7 → lem-trf-split-lattice-torus-projection

For formal smoothness of the same projection take a first order affine thickening $\operatorname{Spec}(B/J)\subset\operatorname{Spec}B$ over $Y$, with $J^2=0$ as in [def-sbc-first-order-thickening]. By Step 5, a map from $\operatorname{Spec}(B/J)$ to $T$ is $r$ units $\bar v_i\in B/J$. Choose lifts $v_i,w_i\in B$ of $\bar v_i$ and their inverses. Then $v_iw_i=1+j_i$, $j_i\in J$, and $v_i$ is a unit with inverse $w_i(1-j_i)$ because $j_i^2=0$. The lifted units give a map $\operatorname{Spec}B\to T$ by [def-weil-affine-spectrum]. Pair it with the prescribed map to $Y$ using [def-pc-fibre-product]; it lifts the given map to $T\times Y$ and lies over $Y$. This is the formal lifting condition in [def-sbc-smooth-morphisms]. Together with Step 6 it proves the projection smooth, also when $Y$ is not affine. Taking $Y=\operatorname{Spec}\mathbf Q$ proves $T$ smooth over $\mathbf Q$.

Uses: def-sbc-first-order-thickening, def-weil-affine-spectrum, def-pc-fibre-product, def-sbc-smooth-morphisms

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose VIII, Lemma 3.2.12(i), printed p.104, the polynomial/Laurent smoothness calculation; explicit first-order unit lifts.

### Returned Step 8 → lem-trf-split-lattice-torus-projection

Evaluation $t_i=1$ is the identity section $\operatorname{Spec}\mathbf Q\to T$ from Step 5. Pairing it with the identity of any $Y$ by [def-pc-fibre-product] gives a section $Y\to T\times Y$ of the projection. Thus the projection is surjective on underlying points: a point $y$ is the image of its image under the section. This includes $r=0$ (the projection is an identity) and $Y=\varnothing$.

Uses: def-pc-fibre-product

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose VIII, 2.3.16--2.3.17 and 3.2.19, printed pp.95,106; the torus projection is smooth and surjective, with its section displayed.

### Returned Step 9 → lem-trf-split-lattice-torus-projection

It remains to check reducedness of the product for reduced $Y$. Put $A=\mathbf Q[L]$. For every extension field $K/\mathbf Q$, the basis map $A\otimes_{\mathbf Q}K\to K[L]$, $e^l\otimes c\mapsto ce^l$, is an isomorphism; its inverse sends $ce^l$ to $e^l\otimes c$. The monoid $L$ is fine and its group completion is torsion free, so [lem-trf-affine-monoid-algebra-normalization] with $P=L$ and $k=K$ says $K[L]$ is a domain, hence reduced. For any affine open $\operatorname{Spec}R$ in the reduced scheme $Y$, $R$ is reduced by [def-pc-reduced-scheme]. Apply [lem-trf-geometrically-reduced-base-change] to $A$ and $R$: it gives reducedness of $R\otimes_{\mathbf Q}A$. The affine product chart of Step 6 is precisely $\operatorname{Spec}(R\otimes_{\mathbf Q}A)$, via $r\otimes e^l\mapsto re^l$. A localization of a reduced ring is reduced: if $(b/s)^n=0$, some denominator $u$ has $ub^n=0$, whence $(ub)^n=0$ and $ub=0$. Therefore every local ring of the product is reduced. These charts cover it, proving reducedness in [def-pc-reduced-scheme]. No irreducibility assumption on $Y$ was used.

Uses: lem-trf-affine-monoid-algebra-normalization, def-pc-reduced-scheme, lem-trf-geometrically-reduced-base-change, def-pc-fibre-product

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose VIII, 3.2.4 and 3.2.19, printed pp.103,106; reducedness of the torus product justified by the existing general reduced tensor-product lemma.

### Returned Step 10 → parent (retained)

Finally let $X=\coprod_{j=1}^s X_j$ be a finite disjoint union of the realizations already treated. Its local ring at a point of $X_j$ is that in $X_j$, so it is reduced by [def-pc-reduced-scheme]. The union of the finitely many finite affine covers supplied by Step 3 is a finite affine cover by finitely generated $\mathbf Q$-algebras, giving finite type by [def-weil-finite-type-morphism]. A connected subset lies in one summand, because the summands are open and closed; hence its connected components are the components of the summands. There are finitely many by Step 4. For an empty monoscheme or an empty disjoint union all these assertions are vacuous, with zero connected components; all the rank-zero formulas above remain valid.

Uses: def-pc-reduced-scheme, def-weil-finite-type-morphism, def-weil-connected-scheme

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Expose VIII, 3.1.3, Remark 3.1.10(ii), and finite-disjoint-union convention in 3.1.26, printed pp.98--100,102.

## Outstanding work

The three new nodes intentionally remain unsplit for separate workers. Their proofs are not claimed finished or in Mathlib. The required dry run and direct push are the remaining delivery actions.
