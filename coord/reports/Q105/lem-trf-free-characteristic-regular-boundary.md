# Repair report: lem-trf-free-characteristic-regular-boundary

## Files written

- dag/nodes/sec-trace-formula/lem-trf-free-characteristic-regular-boundary.json: unchanged statement; four assembly steps, 2538 characters in total.
- dag/nodes/sec-trace-formula/lem-trf-monoidal-local-regularity-criterion.json: statement, unsplit; no complete Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-free-log-chart-ordinary-parameters.json: statement, unsplit; no complete Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-parameter-product-reduced-cartier.json: statement, unsplit; no complete Mathlib match.
- citations.json: verbatim statement excerpts (the full statements) for every cited node of each assembly step.

## Attachments

None. Searched lean/WeilConjectures by the item tag and logarithmic/free-characteristic/parameter concepts. The declaration AlgebraicGeometry.FineSaturatedLogScheme.free_characteristic_regular_boundary in lean/Sheaf/AlgebraicGeometry/FreeCharacteristicRegularBoundary.lean:101 contains sorry, so is not an attachment. Its eleven-paragraph docstring follows the same returned proof. No Lean file was edited and no compiler was invoked.

## WANTED

None: ILO is present and was read. Its VI 1.7 refers to Niziol for the original criterion; the existing proof is an agent expansion from the already present local-algebra nodes, and its proof_origin remains by agent. No unavailable proof is being passed off as a read source.

## What was wrong and what changed

The return requires spreading the 7626-character proof among workers, not shortening its mathematics. The sandbox initially contained only dispatcher marker files, so there was no local node/report/search log to overwrite. I copied the full current repository node, which contains all eleven returned steps, and retained its source, statement, imported/maintainer metadata, citations/search records and route. returned-node.json records that input for this repair's audit. The report appendix preserves all eleven steps verbatim, including their dependency lists. No statement dispute or route change was necessary.

The three new nodes are technical, independently applicable results, not a replacement of the whole item. The local-algebra criterion is about arbitrary local rings with a contracting sharp monoid, not schemes or boundaries. The chart theorem identifies the actual chart coordinates at every stalk, including ordinary parameter extension, and has no boundary/Cartier/density conclusion. The last theorem has no log structure at all and assumes parameter equations; it proves the radical ideal identity, reduced Cartier property and density. Each new node is statement-only (empty proof and proof_deps, null proof_origin, unsplit); future workers can take each without waiting for a proof of the original item.

## Distribution of every returned argument

1. Original step 1 stays in assembly step 1: sharp chart, Noetherian strict local ring, nonunit ideal and log dimension formula.
2. Original steps 2--5 (2755 characters) belong to lem-trf-monoidal-local-regularity-criterion: indecomposables, torsion-freeness, contraction and Nakayama, kernel parameters, rank argument in the group completion, and converse parameter lifts. Its statement exposes the intermediate basis and parameter assertions, not just the final equivalence.
3. Original step 6 stays in assembly step 2: strict-henselization invariance and the local-ring definition of regular schemes.
4. Original steps 7--8 (1648 characters) belong to lem-trf-free-log-chart-ordinary-parameters: unit faces, characteristic N^J, etale strict-local comparison, log regularity on the chart, strict parameters, cotangent scalar extension and Nakayama to obtain ordinary parameters. Chart existence remains an invocation of the existing sharp-chart node in assembly step 2.
5. Original step 9, the first three sentences of step 10, and step 11 belong to lem-trf-parameter-product-reduced-cartier: prime and nondividing parameters, product=intersection and radicality, stalkwise nonzerodivisors and reducedness, the kernel-sheaf check, and the explicit density argument by contraction of the zero prime. The theorem works on a scheme to include this substantial local-to-global argument. All these sentences are retained below without compression.
6. The rest of original step 10 stays in assembly steps 3--4: openness of U by etale openness, uniqueness of reduced pullback, effective Cartier descent and the precise normal crossings definition. Density can then be read off the dense chart opens. This assembly argument is written out; it does not require a new density-of-image lemma.

The parts have comparable proof workloads; no one new node carries the entire original assertion. None of the four new assembly steps exceeds 2000 characters; their combined length is 2538, below the return's 3000-character maximum.

## Searches and Not duplicates

The entire DAG was searched by statement text (not just this unit): monoidal ideal, indecomposable, sharp characteristic, free characteristic, products of distinct parameters and cotangent chart. The blueprint_refs searches were free characteristic, monoidal ideal, product parameters, monoid, parameters, cotangent, log regular and Cartier. No blueprint node states any of the three new propositions. Every new blueprint.from points to lem-trf-local-term-locality through this item and the existing ancestry; same_as is empty.

Each new node has real msearch queries: LeanFinder in two phrasings, Loogle, grep and LeanSearch. Searches and original output are retained in the per-node search-results JSON and searches.jsonl. LeanSearch returned HTTP rate-limit errors and is explicitly unavailable. The chart Loogle query used the unqualified unknown identifier Etale and is explicitly recorded as a query error; the additional valid Loogle search IsRegularLocalRing, IsLocalRing returned only ordinary regular-local definitions and instances, not a logarithmic result. Semantic searches and source grep supplied the actual negative check.

For local algebra, the meaningful hits were AddSubmonoid.closure_addIrreducible (and finiteness) in Mathlib/Algebra/AffineMonoid/Irreducible.lean, whose whole minimal-generator argument I read, and ringKrullDim_add_length_eq_ringKrullDim_of_isRegular. These state individual ingredients and not the contraction/basis/regularity criterion. The sole first grep hit, Flat/Localization.lean:119, concerns regular scalar actions after localization and was read and rejected. For charts, the hits Scheme.mem_basicOpen and ordinary smooth algebra facts do not provide a log structure or ordinary parameter descent. For parameter products, reduced-stalk criteria and Dedekind/regular-sequence facts do not assert radical product equations on arbitrary regular schemes. None of the new nodes is a one-line specialization or a conjunction of complete Mathlib clauses, so all three are unsplit and there are zero Mathlib leaves.

## Not duplicates

- lem-trf-monoidal-local-regularity-criterion vs lem-trf-free-characteristic-regular-boundary: a local ring/monoid proposition with contraction and dimension hypotheses, no scheme, triviality locus or divisor; it isolates returned steps 2--5.
- lem-trf-monoidal-local-regularity-criterion vs lem-trf-log-regular-monoidal-ideal-contraction: the latter only supplies a^{-1}(JA)=J on a sharp log regular stalk; the new theorem assumes that identity for arbitrary A,P and proves bases, cardinalities and parameter lifts.
- lem-trf-monoidal-local-regularity-criterion vs lem-trf-log-chart-face-tor-comparison: Tor base change through face localization does not give any of the regularity criterion's conclusions.
- lem-trf-free-log-chart-ordinary-parameters vs lem-trf-log-regular-sharp-chart: existence of a pointed sharp chart does not compute characteristics on all of W or extend its nonunit coordinates to ordinary parameters.
- lem-trf-free-log-chart-ordinary-parameters vs lem-per-regular-log-smooth-monomial-chart: the latter involves a log smooth morphism and its relative toric chart; the new theorem starts with an arbitrary free chart of an absolute log regular scheme and proves its ordinary local parameter property.
- lem-trf-parameter-product-reduced-cartier vs lem-trf-regular-local-ufd-boundary-factorization: UFD factorization and units after localization do not state the radical product/intersection identity or the scheme-level reduced Cartier and density conclusion. The new theorem does not assert unique factorization of arbitrary elements.
- lem-trf-parameter-product-reduced-cartier vs lem-trf-etale-reduced-cartier-descent: the latter assumes reduced closed pullbacks/effective Cartier conditions for descent; it does not prove parameter equations have these properties.
- lem-trf-parameter-product-reduced-cartier vs def-trf-normal-crossings-divisor: a definition of the parameter criterion does not prove the product's ideal radical or its dense complement.

- lem-trf-parameter-product-reduced-cartier vs lem-trf-parameter-product-closure-kernel: the current DAG node proves a localized closure kernel and its flat base change for an additional distinguished parameter a; it states no radicality, reduced Cartier property or dense complement for the product divisor.
- lem-trf-parameter-product-reduced-cartier vs lem-trf-parameter-product-strict-local-branches: the current DAG node counts minimal primes after strict henselization; it does not give the ordinary scheme-level reduced Cartier and density assertion.
- lem-trf-parameter-product-reduced-cartier vs lem-sfb-snc-boundary-parameter-criterion: the current DAG node is a global Noetherian strict-boundary equivalence with irreducible-component intersection conclusions; the new node is about an arbitrary finite list of global functions on a locally Noetherian regular scheme, allows unit factors point by point, and states the precise product/intersection identity with density, without assuming or asserting global strictness.
- lem-trf-free-log-chart-ordinary-parameters vs lem-trf-monoidal-chart-dense-injective: the current DAG node assumes domains and contraction and proves density and structural-map injectivity, without the freeness or ordinary parameter-extension conclusion.
- lem-trf-free-log-chart-ordinary-parameters vs lem-trf-log-smooth-log-regular: preservation of log regularity under an injective torsion-free chart comparison is not the free chart's characteristic-face computation or parameter extension in each ordinary local ring.

No Stacks tag is assigned to a new node: their source is the read ILO argument and its expansion. Existing Stacks algebra nodes remain available for the future splits; none is duplicated as a statement-only copy.

## Repair of the landing return (2026-10-22)

The return has one point: the earlier side-project completion was not promoted into the live DAG read by the queue. I resumed the retained sandbox, ran the required dry run before editing, and it exited 0 with preflight passed at 64c22d38c29. The delivery command builds its commit on the current server DAG; no manual git operation was run in the shared read clone. This delivery is therefore a fresh delivery on the current DAG, rather than a re-push of the returned head.

I compared returned-node.json with the current read-clone item, field by field: they are identical. The retained sandbox differs from that source item only in proof, proof_deps and split_report. Its three children remain absent from the current DAG. I preserved their statements, original searches and result files, the full eleven-step proof appendix, the existing Lean and maintainer records, and the item statement verbatim. I repeated the current DAG/blueprint duplicate checks without repeating the retained Mathlib searches, whose original results and unavailable-service responses I read.

I reread every currently cited statement, including all three sandbox children: the fs log definition, pointed sharp chart, Noetherian and regular strict-henselization invariance, monoidal ideal contraction, regular-scheme definition, free-chart parameter theorem, parameter-product theorem, etale definition, flat-lfp openness, reduced-Cartier descent, reduced induced closed structure and normal-crossings definition. Their current statements still supply the exact assertions quoted in citations.json; no changed assertion requires a new route or a changed child. Step 1 now explicitly notes that the strict local ring is nonzero and that its monomial ideal is contained in the maximal ideal, checking the local criterion's nonzero quotient hypothesis. Step 4 now explicitly records that charts chosen above every point are jointly surjective, checking the Cartier descent hypothesis. These are concrete hypothesis clarifications to the split, rather than an unchanged re-push. The full assembly remains below 3000 characters, with no step over 2000 characters.

For this repair I reread ILO VI 1.1--1.7, VIII 3.4.1--3.4.4 and VIII 4.1.1--4.1.2. Their statements still give the same regularity/free-characteristic and ordinary etale normal-crossings route. The local criterion tests P=0 and the singular rank-three/four-generator cone, the chart theorem tests disappearing unit coordinates, and the product theorem tests the empty product and the crossing xy versus the excluded repeated factor x squared exactly as in the signed review below. No extra hypotheses were added to the item or children, and no source or statement dispute was found. No Lean source was written and no compiler was run.

Resumed verification after the provider interruption: the initial dry run exited 0 with preflight passed at 3633e606147, built against the current server DAG. The current read-clone item remains field-for-field identical to returned-node.json; the retained repair differs only in proof, proof_deps and split_report. I verified all 18 citation entries against the current statements and checked exact coverage of the four steps. All three child ids remain absent from the read clone, and the released stage-1 re-split order remains present. I retained every logged search and its result, including unavailable LeanSearch and the Loogle identifier error. No cited statement changed, so no mathematical rerouting was needed. In this resumed repair I made the chart-stalk identification explicitly an isomorphism and made the fixed geometric point explicit in the ordinary-local equivalence. The substantive retained repairs checking nonzero local rings and joint surjectivity remain in place. I reread ILO VI pp.69--70 and VIII pp.110,117 and the current cited statements; the signed checks below still apply.

## Review by Q105

I read ILO VI 1.1--1.7 (PDF pp.75--76 = printed pp.69--70), VIII 3.4.1--3.4.4 (PDF p.116 = printed p.110) and VIII 4.1.1--4.1.2 (PDF p.123 = printed p.117). These supply the fs sharp charts, log dimension condition, free-characteristic criterion, monoidal ideal correspondence and the etale normal-crossings meaning. VI 1.7 says normal crossings, and the parameter description in VIII 4.1.2 does not assert distinct global irreducible components. The chapter/unit route in sec-trace-formula/sk-i-curve-zero is retained through the alteration/nearby-duality ancestry. No SGA source is used.

For assembly step 1 I opened def-trf-fs-log-blowup (chart pushout and log-regular dimension condition), lem-trf-log-regular-sharp-chart (fs sharp P and actual affine locally Noetherian pointed etale chart), lem-sc-strict-henselization-noetherian (Noetherian iff), and lem-trf-log-regular-monoidal-ideal-contraction (the exact equality for every ideal, including empty). They supply exactly the four hypotheses of the new local-algebra criterion. A/I is nonzero because all nonzero monomial images lie in the local maximal ideal. Nothing from the proof of a cited node is used.

For assembly step 2 I opened lem-sc-strict-henselization-regular (R regular iff Rsh regular for a Noetherian local ring) and def-weil-regular-scheme (local Noetherian plus regular local rings). Their hypotheses hold from step 1 and the original locally Noetherian assumption. Under freeness the already cited sharp chart may be relabelled N^r. The new chart theorem is stronger than the needed claim about those actual functions; it includes log regularity of the inverse-image structure, W regular, the exact preimage of U, and parameter extension in the ordinary local rings. This corrects no mathematics, but moves the face and cotangent arguments out of the assembly.

For assembly step 3 the new parameter-product theorem applies at every point of each chart using the ordinary parameters supplied by the chart theorem, not just the parameters in a completion. I read def-weil-etale-morphism (flat and locally finite presentation) and lem-weil-pbc-flat-lfp-open (open maps), which justify the union-of-chart-images argument. Density follows by pulling a nonempty open back to a chart over one of its points and meeting dense D(f). No assertion that an arbitrary image of a dense set is dense is smuggled in.

For assembly step 4 I read lem-trf-etale-reduced-cartier-descent, whose statement explicitly gives both reduced pullback and effective Cartier descent, and lem-weil-pbc-reduced-induced-closed-subscheme, whose uniqueness clause identifies the ideal sheaves. Z is closed by step 3 and X is locally Noetherian, so those hypotheses are available. The chart cover is jointly surjective because a pointed chart was chosen at each point. The new product theorem gives a reduced V(f) on the correct support, and the new chart theorem identifies its local generators as distinct parameter entries. def-trf-normal-crossings-divisor states precisely this etale ordinary-local product criterion. In particular the descent node is not a definition silently being used as a theorem.

I also read each existing algebra statement used in the preserved arguments: regular quotient kernel parameters (00NR), regular parameter quotients (00NQ), Nakayama (00DV), the generator dimension bound (00KQ), regular local domain (00NP), strict cotangent base change, and strict-local etale comparison. The new nodes do not claim these as proved; the appendix gives future splitters the argument and these exact usable statements. All non-elementary facts of the shortened parent are cited nodes, with a verbatim quote for each use in citations.json.

Edge cases were tested separately. For P=0, I=0 and the dimension condition reduces to the assumed regularity of A; there are no indecomposables or first parameters. For P=N and A=k[[t]], the basis of I/mI has size one. The singular saturated cone monoid with relation p1+p4=p2+p3 and A=k[[x,y,z,w]]/(xw-yz), with its monomial chart and I the maximal ideal, has four indecomposables and rank three, and is correctly rejected by the regularity criterion. Saturation excludes torsion in Pgp; no claim of that form is made for a nonsaturated monoid. On a free chart some coordinates can be units; only J enters the characteristic and parameter list. If all are units or r=0, f is a unit, V(f) is empty and D(f)=W. On k[x,y], xy gives the reduced crossing while x squared violates the distinct-position hypothesis. Empty schemes and dimension-zero regular local rings force empty parameter sublists and are covered. Global self-intersections are permitted because no branch labelling is descended.

The B--E checklist was applied substantively: new statements introduce their objects and notions; no unsplit node carries a proof; source places are precise; every assembly use was checked against the actual cited statement (C4); no non-elementary assembly fact is only an external reference (C1); the statements do not simply relabel the original clauses; hypotheses, stalks versus ordinary local rings, empty monoid ideals, reduced pullback and joint surjectivity were checked. No cycle is introduced through the children, since they have only definition statement dependencies and empty proof dependencies. Only generic strict-henselization and flat-lfp openness are declared tools in split_report for the maintainer's route review.

## Current-base repair verification (2026-10-23)

The required initial dry run exited 0 at b5c3277e0f3 with preflight passed. The subsequent delivery invocation exited 0 and reported that the existing delivery branch already had exactly the retained content at 97e8a5a655; it therefore pushed nothing. I continued the repair instead of treating that unchanged branch as a fresh delivery.

I compared the current read-clone item with returned-node.json: all fields still agree. The sandbox differs only in proof, proof_deps and split_report, and its three children are still absent from the current read-clone DAG. I reread every cited statement and verified all 18 citation quotes and exact step-use coverage. I read the retained Mathlib result files and searches.jsonl rather than rerunning the same questions; the negative decisions and unavailable-service records are retained. Current blueprint searches for free characteristic, product parameters and monoidal ideal found no matching blueprint nodes. I reread ILO VI 1.1--1.7, VIII 3.4.1--3.4.4 and VIII 4.1.1--4.1.2, and confirmed the existing Sheaf declaration still ends in sorry; no project declaration supplies an attachment.

For the signed review above, I made two further concrete citation/hypothesis clarifications. Step 1 now writes the exact contraction equality for every monoid ideal, explicitly including the empty ideal, matching both the contraction node and the new local-algebra criterion. Step 2 now states first the precise conclusion of strict-henselization invariance, R regular iff A regular, and then composes it with step 1's monoidal criterion; it no longer attributes the composed conclusion to invariance alone. The proof remains four assembly steps, 2538 characters overall, with each step below 2000. The earlier explicit nonzero-ring and jointly-surjective-cover checks remain. No item or child statement changed, no argument or search was removed, and no Lean edit, compiler or manual git command was used.

## What remains unfinished

The three new statement-only nodes await other workers' splits, as explicitly required by the return. This is a stage-1 repair only; the existing Lean sorry remains untouched.

## Preserved returned proof, verbatim

This is the complete previous eleven-step argument, retained as work instructions/evidence, not inserted into any unsplit node's statement or proof field.

### Original step 1

Fix $\bar x$ above $x$. Put $R=\mathcal O_{X,x}$, $A=R^{\mathrm{sh}}$, $P=\overline M_{\bar x}$, $r=\operatorname{rank}_{\mathbf Z}P^{\mathrm{gp}}$, and $I=(\alpha(M_{\bar x}\setminus A^\times))$. The sharp-chart lemma supplies a chart by $P$, and strict henselization is Noetherian since $R$ is. By log regularity, $A/I$ is regular and, writing $s=\dim(A/I)$, we have $\dim A=s+r$. The chart identifies the log stalk with $P\oplus A^\times$, so $I$ is generated by the chart images of $P\setminus\{0\}$.

Uses: def-trf-fs-log-blowup, lem-trf-log-regular-sharp-chart, lem-sc-strict-henselization-noetherian.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI, 1.2 and 1.6, printed pp. 69--70; sharp chart and log regular dimension formula.

### Original step 2

Choose a finite generating set $p_1,\ldots,p_n$ of the sharp integral monoid $P$, minimal under deletion, excluding $0$. Each $p_i$ is indecomposable: if $p_i=q+q'$ with both summands nonzero, expand $q,q'$ in the generators. If the expansion does not use $p_i$ then $p_i$ was redundant. If it uses $p_i$, cancellation gives a sum equal to $0$; sharpness forces every summand to be $0$, leaving exactly one copy of $p_i$, which is incompatible with both $q,q'$ being nonzero. Thus the $p_i$ are exactly the indecomposable nonzero elements, since any nonzero sum with at least two terms is decomposable. Also $P^{\mathrm{gp}}$ is torsion free: if $ng=0$, saturation puts both $g$ and $-g$ in $P$, and sharpness gives $g=0$.

Uses: def-trf-fs-log-blowup, lem-trf-log-regular-sharp-chart.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI, 1.6, P is fs sharp; elementary consequences of finiteness, integrality, saturation and sharpness.

### Original step 3

Write $a_i=a(p_i)\in A$. They generate $I$. None is in the ideal generated by the others: contraction of the monoid ideal $\bigcup_{j\ne i}(p_j+P)$ would give $p_i=p_j+q$, contradicting indecomposability and distinctness. Their images therefore form a basis of $I/\mathfrak m_AI$. Indeed they span, and a linear dependence over the residue field has a nonzero coefficient; deleting the corresponding vector leaves a spanning family, which by Nakayama would generate $I$ and contradict irredundance. Hence $\dim_{\kappa(A)}I/\mathfrak m_AI=n$.

Uses: lem-trf-log-regular-monoidal-ideal-contraction, lem-weil-pbc-nakayama-local-generators.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VIII, Lemma 3.4.3, printed p. 110; apply monoidal ideal contraction, then ordinary Nakayama to the finite ideal I.

### Original step 4

Suppose $A$ is regular, of dimension $d$. Since $A/I$ is regular, the regular-quotient kernel lemma gives parameters $z_1,\ldots,z_d$ with $I=(z_1,\ldots,z_c)$. The parameter quotient theorem gives $s=d-c$; comparing with $d=s+r$ gives $c=r$. The images of $z_1,\ldots,z_c$ form a basis of $I/\mathfrak m_AI$: they span, and their independence follows from independence in $\mathfrak m_A/\mathfrak m_A^2$, since $\mathfrak m_AI\subseteq\mathfrak m_A^2$. Thus step 3 gives $n=c=r$. The generators $p_i$ give a surjection $\mathbf Z^r\to P^{\mathrm{gp}}$. After tensoring with $\mathbf Q$ it is a surjection between vector spaces of dimension $r$, hence injective. Its integral kernel is therefore zero. Since $P$ is integral and generated by these $p_i$, the induced surjection $\mathbf N^r\to P$ is an isomorphism. This includes $r=0$.

Uses: lem-weil-pbc-regular-local-quotient-kernel-parameters, lem-weil-pbc-regular-local-generators-regular-sequence, lem-weil-pbc-nakayama-local-generators, def-weil-pbc-regular-system-of-parameters, lem-weil-pbc-noetherian-local-dimension-le-generators.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI, 1.7, printed p. 70, regular implies free: expand the regular-quotient and monoidal-ideal argument rather than invoking the conclusion as a new lemma.

### Original step 5

Conversely suppose $P\cong\mathbf N^r$ and let $t_1,\ldots,t_r$ be the images of its basis under a sharp chart. Then $I=(t_1,\ldots,t_r)$. Lift a regular system of $s$ parameters of $A/I$ to $b_1,\ldots,b_s\in\mathfrak m_A$. The list $(t_1,\ldots,t_r,b_1,\ldots,b_s)$ generates $\mathfrak m_A$: reduce any element modulo $I$, express it using the $b_j$, and subtract that expression to land in $I$. Its length $r+s$ equals $\dim A$. Consequently $A$ is regular, and this list is a regular system of parameters. The dimension bound for any set of maximal-ideal generators ensures it is minimal. In particular the $t_i$ are distinct members of such a system.

Uses: def-trf-fs-log-blowup, lem-trf-log-regular-sharp-chart, def-weil-regular-scheme, def-weil-pbc-regular-system-of-parameters, lem-weil-pbc-noetherian-local-dimension-le-generators.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI, 1.2, 1.6 and 1.7, printed pp. 69--70, free implies regular: generators and the log regular dimension formula.

### Original step 6

Regularity is unchanged by strict henselization, so steps 4 and 5 give precisely $\mathcal O_{X,x}$ regular if and only if $\overline M_{\bar x}\cong\mathbf N^r$. If this holds everywhere then every ordinary local ring of $X$ is regular. Since $X$ is locally Noetherian, the local-ring characterization of regular schemes gives regularity of $X$.

Uses: lem-sc-strict-henselization-regular, def-weil-regular-scheme.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI, 1.7, printed p. 70; pass between strict local rings and ordinary local rings.

### Original step 7

Under the everywhere-free hypothesis choose at each point a sharp chart $\mathbf N^r\to M|_W$ on an affine etale neighbourhood as in step 1, and write $t_i$ for its structural functions. The triviality locus in $W$ is exactly $D(f)$ with $f=\prod_{i=1}^r t_i$: the associated log structure is trivial precisely when every basis image is invertible. At any geometric point of $W$, a product of basis images is a unit exactly when each factor in its support is a unit. Thus its characteristic is $\mathbf N^J$, where $J$ indexes the nonunit $t_i$ at that point. Strict local rings of a pointed etale neighbourhood identify with those of the base, so log regularity pulls back to $W$. Applying step 5 at this point shows that these nonunit $t_i$ extend to parameters in the strict local ring. The chart neighbourhoods are locally Noetherian by the sharp-chart lemma.

Uses: lem-trf-log-regular-sharp-chart, def-trf-fs-log-blowup, lem-sc-strict-henselization-comparison.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI, 1.6--1.7, printed p. 70; free charts describe the triviality locus and all their characteristic stalks.

### Original step 8

Let $B=\mathcal O_{W,w}$ and $A=B^{\mathrm{sh}}$ at a point of such a chart. By strict-henselization invariance, $B$ is regular. The canonical cotangent-space base-change isomorphism shows that the classes of the nonunit $t_i$ are linearly independent in $\mathfrak m_B/\mathfrak m_B^2$, since they are independent after extending scalars to the separable residue closure. Extend them to a basis of that cotangent space and lift the additional basis vectors to $B$. Nakayama says that this list generates $\mathfrak m_B$; its size is $\dim B$ by regularity (minimality follows from the dimension bound). It is therefore a regular system of parameters of $B$. This proves the claimed parameter assertion in ordinary local rings on an actual etale chart, not just in a formal completion.

Uses: lem-sc-strict-henselization-regular, lem-sc-strict-henselization-cotangent-dimension, lem-weil-pbc-nakayama-local-generators, lem-weil-pbc-noetherian-local-dimension-le-generators, def-weil-pbc-regular-system-of-parameters.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI, 1.7, printed p. 70; ordinary-local form of the parameter equations, using the cotangent-space comparison for strict henselization.

### Original step 9

In $B$, each nonunit $t_i$ is prime: permute a full parameter system to put it first; the parameter quotient theorem makes $B/(t_i)$ regular local, hence a domain. Different such $t_i$ do not divide one another: divisibility by a unit coefficient would make their cotangent classes dependent, and divisibility by a nonunit coefficient would put one in $\mathfrak m_B^2$. Since $B$ is a domain, their product is a non-zero-divisor. Moreover $(\prod_{i\in J}t_i)=\bigcap_{i\in J}(t_i)$: successively use primality and nondivisibility to divide an element of the intersection by each factor. The intersection is radical, so the product defines a reduced subscheme. Unit factors in $f$ do not change its ideal. For $J=\varnothing$, $f$ is a unit and the closed subscheme is empty.

Uses: lem-weil-pbc-regular-local-generators-regular-sequence, lem-sc-regular-local-domain, def-weil-pbc-regular-system-of-parameters.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI, 1.7, printed p. 70; spell out reducedness and the non-zero-divisor property of the normal crossings equation.

### Original step 10

Thus on each chart $W$ the closed subscheme $V(f)$ is reduced and is an effective Cartier divisor. Indeed its quotient local rings are reduced by step 9, and multiplication by $f$ is injective on all local rings; equivalently its kernel sheaf vanishes. Its support is $W\setminus U$. Etale maps are flat and locally of finite presentation, hence open by the flat-lfp openness theorem. Since $U$ is the union of the open images of the chart opens $D(f)$, it is open in $X$, so $Z=X\setminus U$ is closed. The etale reduced-Cartier descent lemma identifies $V(f)$ with $Z_{\mathrm{red}}\times_XW$ and descends the effective Cartier property to $D=Z_{\mathrm{red}}$. The equations in step 8 are products of distinct members of parameter systems, as required for a normal crossings divisor. No assertion of distinct global irreducible components is used.

Uses: lem-trf-etale-reduced-cartier-descent, lem-weil-pbc-reduced-induced-closed-subscheme, def-nagata-effective-cartier-ideal, def-weil-etale-morphism, lem-weil-pbc-flat-lfp-open, def-pc-reduced-scheme.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI, 1.7, printed p. 70, and VIII, 3.4.4 and 4.1.1, printed pp. 110 and 117; descend the reduced local parameter equations.

### Original step 11

Finally $U$ is dense. Otherwise a nonempty open $V$ lies in $D$. Shrink to a nonempty affine open $\operatorname{Spec}C\subseteq V$ on which the Cartier ideal is $(g)$, with $g$ a non-zero-divisor. Choose a point corresponding to a prime $\mathfrak p$ of $C$. Its local ring $B=C_{\mathfrak p}$ is regular, hence a nonzero domain. The element $g/1$ is nonzero, because multiplication by it is injective in this nonzero ring. The inverse image of the prime $(0)\subset B$ is therefore a prime of $C$ not containing $g$. This gives a point of $\operatorname{Spec}C$ outside $D$, contradicting $\operatorname{Spec}C\subseteq V\subseteq D$. The empty scheme and empty boundary cause no exception; for $r=0$ the chart equation is the empty product $1$.

Uses: def-nagata-effective-cartier-ideal, def-weil-regular-scheme, lem-sc-regular-local-domain.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI, 1.4 and 1.7, printed pp. 69--70; elementary density argument from the Cartier local equations.
