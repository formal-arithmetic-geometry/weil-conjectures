## Worker report

Files written: the item `dag/nodes/sec-six-functors-basics/lem-sfb-flat-graded-tail-proj.json` (statement unchanged, short assembly), plus the following statement-only nodes, all `unsplit`, no Mathlib match:

- lem-sfb-polynomial-quotient-proj-presentation: projective presentation, finite presentation and affine coordinate charts (former steps 1--2).
- lem-sfb-locally-free-tail-chart-flatness: affine sections, the explicit high-degree colimit universal property, and flatness of its chart ring (former steps 3--5).
- lem-sfb-polynomial-quotient-proj-cartesian: tensor-quotient equations and compatibility of the specified closed embedding under arbitrary base change (former step 6).

Attachments: none. Searched `lean/WeilConjectures/` by the item tag, graded-tail terminology and relevant polynomial-quotient/localization terminology. There is no finished matching declaration. Read `lean/Sheaf/AlgebraicGeometry/FlatGradedTailProj.lean`: both main family and field declarations end in `sorry`, so neither is an attachment. No Lean was written or compiled.

WANTED: none for this repair: all Stacks passages actually used are locally available. No SGA route used.

The sandbox initially contained only dispatcher marker files, despite the brief's expectation of retained work. Copied the current item, whose reviewed proof is exactly the returned eight-step argument (length 7013). `returned-item.json` retains that version. There was no old report or searches.jsonl to overwrite. The item's historical searches, citations embodied in its former steps, source and Lean metadata are retained. The repair changes the granularity, not the statement or route. All new statements introduce their own objects, do not assume the graded-tail/Hilbert polynomial conclusion, and can be assigned independently. Their proof fields and proof dependencies are empty; the following argument inventory is for the workers who will split them, not a second-level split in this delivery.

No unfinished part of the requested stage-1 repair remains. The new nodes are deliberately unsplit for parallel work, as the return requires.

## Returned arguments and allocation

### lem-sfb-polynomial-quotient-proj-presentation

Former step 1, preserved in full:

Apply the surjective graded-map clause of prop-nagata-relative-proj-functoriality to $\mathcal O_U[x_0,\ldots,x_n]\twoheadrightarrow\mathcal B$. The relative projective-space definition identifies its source Proj with $\mathbf P^n_U$, so this gives the required closed immersion $i:Z\hookrightarrow\mathbf P^n_U$ over $U$. This clause does not require that $\mathcal B_0=\mathcal O_U$; degree-zero equations in $J$ are allowed. Over an affine base open $V=\operatorname{Spec}R$, relative Proj restricts to $\operatorname{Proj}B$, where $B=\Gamma(V,\mathcal B)$ is, degree by degree by the affine cokernel clause of lem-weil-pbc-quasi-coherent-module-cokernel-image, the graded quotient of $R[x_0,\ldots,x_n]$. The images of the $x_i$ generate $B_+$ as an ideal. Thus the standard-open result gives the finite cover by $D_+(x_i)=\operatorname{Spec}C_i$, with $C_i=B_{(x_i),0}$, including empty charts.

Uses: prop-nagata-relative-proj-functoriality, def-nagata-relative-projective-space, def-nagata-relative-proj, prop-nagata-proj-standard-open, lem-weil-pbc-quasi-coherent-module-cokernel-image.

Former step 2, preserved in full:

The projective-space identification in def-nagata-projective-space-base-change identifies the relative-Proj model with the projective space used by def-kun-projective. Thus the embedding $i$ makes $Z\to U$ projective in the finite-projective-space convention. Hence it is proper by lem-kun-projective-implies-proper. By the definition of proper, it is separated and of finite type, hence quasi-compact and locally of finite type. Since $U$ is locally Noetherian, pqf-lem-lft-fp-locnoeth gives local finite presentation. Its diagonal is a closed immersion by separatedness; by lem-weil-pbc-closed-immersion-proper that diagonal is proper, hence of finite type and therefore quasi-compact. The definition of quasi-separatedness now gives that $Z\to U$ is quasi-separated. It is locally of finite presentation, quasi-compact and quasi-separated, so it is finitely presented as asserted.

Uses: def-kun-projective, lem-kun-projective-implies-proper, def-weil-proper-morphism, def-weil-finite-type-morphism, pqf-lem-lft-fp-locnoeth, lem-weil-pbc-closed-immersion-proper, def-weil-quasi-separated-morphism, def-sbc-locally-finite-presentation, def-nagata-projective-space-base-change.

### lem-sfb-locally-free-tail-chart-flatness

Former step 3, preserved in full:

Fix an affine $V=\operatorname{Spec}R\subseteq U$ and the graded ring $B$ of step 1. For each integer $d\geq m$, the hypothesis says that $\mathcal B_d$ is finite locally free (its rank $P(d)$ is a finite nonnegative integer). Apply lem-pc-finite-flat-affine-sections-projective to this sheaf and $V$. It gives that $B_d=\Gamma(V,\mathcal B_d)$ is projective over $R$. By lem-weil-pbc-projective-module-flat it is flat. This is applied separately for every $d$; there is no need for one affine trivialization of all the infinitely many sheaves.

Uses: lem-pc-finite-flat-affine-sections-projective, lem-weil-pbc-projective-module-flat.

Former step 4, preserved in full:

For a fixed $i$, use the directed set of integers $d\geq m$ with transition $B_d\to B_{d+1}$ given by multiplication by $x_i$. The maps $B_d\to C_i$, $b\mapsto b/x_i^d$, form a cocone. Here is its colimit universal property directly from the fraction definition. Given a compatible family of $R$-linear maps $h_d:B_d\to M$, send a fraction $b/x_i^d$ to $h_D(x_i^{D-d}b)$ for any $D\geq\max(d,m)$. Compatibility makes this independent of $D$. If $b/x_i^d=c/x_i^e$, the ordinary localization relation gives $x_i^q(x_i^e b-x_i^d c)=0$ for some $q\geq0$. Multiplying further if necessary gives equality of the two numerators at a common degree $D\geq m$; compatibility of the $h_d$ therefore makes the displayed rule independent of the fraction representative. Addition and scalar multiplication are computed at a common degree, so the rule is linear. Every fraction has a representative of degree at least $m$, giving uniqueness. Thus $C_i$ with this cocone is the colimit in $R$-modules. This uses no cancellation of $x_i$ and remains valid if $x_i$ is zero or nilpotent.

Uses: def-nagata-homogeneous-localization-degree-zero, def-weil-ring-localization-away.

Former step 5, preserved in full:

The index set in step 4 is small, nonempty and directed, and all its modules are flat by step 3. The filtered-colimit-flatness theorem therefore makes every $C_i$ a flat $R$-module. By lem-weil-pbc-flat-ring-map-iff-flat-affine the chart morphism $\operatorname{Spec}C_i\to\operatorname{Spec}R$ is flat. The charts cover $Z$ as $V$ ranges over affine base opens. For a point in such a chart, the local rings of the open subschemes are the same as the local rings of $Z$ and $U$, and their local structural map is the map of $Z\to U$. Hence the stalk definition of flatness gives flatness of $Z\to U$ at every point.

Uses: lem-weil-pbc-filtered-colimit-flat-modules, lem-weil-pbc-flat-ring-map-iff-flat-affine, def-weil-flat-morphism.

### lem-sfb-polynomial-quotient-proj-cartesian

Former step 6, preserved in full:

For any $g:T\to U$, apply lemma-nagata-relative-proj-base-change-arbitrary to $\mathcal B$ to identify $\operatorname{Proj}_T(g^*\mathcal B)$ with $Z\times_UT$. The affine module comparison lem-weil-pbc-tilde-pullback-base-change, applied degreewise, identifies coefficient pullback with tensor product. In particular the polynomial algebra pulls back coefficientwise to $\mathcal O_T[x_0,\ldots,x_n]$. On affine tests corresponding to $R\to R'$, there is an isomorphism $R'\otimes_R(R[x]/J_V)\cong R'[x]/(\operatorname{image}J_V)$: maps from either algebra to an $R'$-algebra are exactly choices of images of the variables annihilating all the polynomials in $J_V$. Thus these quotient algebras and their chart equations agree. The closed-immersion clause of prop-nagata-relative-proj-functoriality identifies their Proj as the closed subscheme of $\mathbf P^n_T$ cut out by those equations. On charts both the Proj base-change map and the base change of $i$ take $b/x_i^d$ to its coefficientwise image; consequently they give the same embedding, not just isomorphic abstract schemes. No flatness of $g$, nor injection of $g^*J$ into the pulled-back polynomial algebra, is asserted or needed: the ideal of equations is its image.

Uses: lemma-nagata-relative-proj-base-change-arbitrary, prop-nagata-relative-proj-functoriality, def-pc-module-pullback, def-nagata-homogeneous-localization-degree-zero, lem-weil-pbc-tilde-pullback-base-change.

The affine-to-global final portion of former step 5 remains explicitly in item step 2. The field comparison and geometric-fibre argument of former steps 7--8 remain verbatim in item steps 4--5, with only references to earlier step numbers adjusted. In particular none of the quotient identification, finite-presentation chain, projectivity of separate degree pieces, fraction universal property, filtered-colimit argument, tensor-quotient calculation, embedding compatibility, unsaturated field comparison, or rank/polynomial uniqueness argument has been dropped.

## Review by Q41

I read the chapter and unit records and retained the projective Hilbert-scheme prerequisite in the inherited alteration/direct-image route. The ancestor command returns None; I have not invented a blueprint ancestor. The new from.place entries specify the inherited proof location and the exact former steps they serve, with the item added to via. I searched the whole DAG by the relevant words and source tags and used blueprint_refs.py search across all chapters. Existing abstract Proj base change, homogeneous scalar extension and quotient twisting comparison remain existing tools; they do not state the three interfaces assembled here.

Sources read for the item: Constructions 01M7 (lemma-proj-sheaves, chart sections), 01O3 (lemma-relative-proj-base-change, arbitrary morphism and its chart construction), 07ZK (lemma-surjective-generated-degree-1-map-relative-proj); Algebra 05UT (lemma-colimit-flat); Morphisms 01WC (lemma-locally-projective-proper), 01TX (lemma-noetherian-finite-type-finite-presentation), 01U5 (lemma-flat-characterize); Coherent 0AG7 (lemma-recover-tail-graded-module), and Varieties 08AE (lemma-hilbert-polynomial-H0). These sources match the hypotheses: generated in degree one for the polynomial source, arbitrary degree-zero quotient, arbitrary base change, and a locally Noetherian base only for the finite-presentation argument. The field comparison uses the polynomial ring as S and its quotient as a finite graded S-module, so it includes the zero quotient without a false A_0=k assumption.

For the presentation node I read the same 07ZK/01M7 and 01WC/01TX passages, and checked the cited existing functoriality, standard-open, affine cokernel and projectivity statements. Its extra assertion is the entire quotient-to-finite-presentation/chart identification, not merely a repeated closed immersion assertion. The coordinate images generate the irrelevant ideal, so the n+1 specified charts cover; degree-zero relations change B_0 but do not affect this. Its finite-presentation argument keeps properness, finite type, the locally Noetherian upgrade, and the quasi-compact separated diagonal. This is a separate geometry task with no local-free tail or Hilbert polynomial input.

For the chart-flatness node I read Algebra 00JM (homogeneous localization), 05UT, the affine-sections/projective statement and the fraction definition. The node states both the universal property and its explicit extension formula; it does not simply assert the item's flat morphism conclusion. For each degree, finite locally free sections are projective separately; no common simultaneous trivialization is assumed. The index set is the small nonempty directed tail of N. In the saved argument equality of fractions is killed by a power of f, so it never cancels a possibly nilpotent coordinate. Filtered-colimit flatness applies over R, not over the full graded ring. Its statement therefore supplies exactly the algebraic part needed by item step 2.

For the cartesian node I read 01O3 and the existing statements lemma-nagata-relative-proj-base-change-arbitrary, lem-nagata-homogeneous-localization-scalar-extension, lem-nagata-affine-proj-scalar-extension, prop-nagata-relative-proj-functoriality, and lem-sfb-graded-proj-quotient-twist-comparison. Abstract base change alone does not state that the base-changed quotient map has exactly the image equations or that both prescribed embeddings agree. This node includes those comparisons and the degreewise tensor formula. The quotient universal property in the saved argument gives the isomorphism on affine tests; both chart maps send b/x_j^d to its coefficientwise image, which pins down the same embedding. The ideal is the image, never an asserted injection of g^*J. This is independent of locally Noetherian or tail-flat hypotheses.

Item step 1 uses precisely the new presentation statement: embedding, finite presentation, and the affine cover/components. Step 2 uses the new chart-flatness statement, then the iff statement of lem-weil-pbc-flat-ring-map-iff-flat-affine and the stalk definition def-weil-flat-morphism. On a chart the local structural maps are the same as in Z and U, giving the final local-to-global inference. Step 3 uses precisely the new cartesian/image-ideal statement. Step 4 reads the actual statements of lem-trf-standard-graded-hilbert-function and lem-sfb-projective-coordinate-ring-euler-polynomial: the first gives eventual polynomial dimensions for the finite module S/I; the second gives equality with Euler characteristic for unsaturated ideals. Their common tail gives the field clause, without changing either object's grading. Step 5 reads the geometric-fibre, tensor-pullback, and finite-locally-free definitions; it uses previous steps 3--4. Tensoring an individual frame gives P(d) vectors, then polynomial uniqueness is elementary. The quotes in citations.json are verbatim full statements of these cited nodes. No step uses an uncited theorem from the proof of another node. Only the generic Hilbert-function tool from another unit remains in the item's new proof; its use is declared.

Small-case tests: J=(1) gives the zero algebra, empty charts, an empty flat family and P=0. A degree-zero ideal (a) permits B_0=R/(a); the new presentation/base-change nodes allow this without claiming R-flatness absent the tail hypothesis. For a nilpotent coordinate, e.g. k[x_0]/(x_0^2), the tail system is eventually zero and the localization colimit is zero; all fraction formulas still hold. For n=0,J=0 the one chart is Spec R and each graded piece is R. For J=0 in any dimension the usual ranks binomial(n+d,n) are recovered. Nonflat base change R=Z to F_p with degree-zero J=(p) gives F_p[x] and image ideal zero, illustrating why g^*J need not inject. Unsaturated irrelevant-primary ideals have a finite graded tail of zeros and empty Proj; the saved field argument handles this. Empty bases and empty affine opens are harmless. No hypothesis was strengthened or conclusion weakened.

Return repaired: extracted three nontrivial work units (former argument sizes 1783, 2228, and 1230), of comparable size rather than moving the whole theorem into one. Every new node is statement-only with no proof dependencies. Each has actual LeanSearch, Loogle, LeanFinder and grep records and a second semantic phrasing. Semantic search candidates concern ordinary affine Proj properness, homogeneous fraction definitions or chart intersections; reading the local sources showed none supplies these relative comparisons in one specialization. The first cartesian Loogle pattern used an unknown identifier; its diagnostic is retained, and a corrected pattern was run with zero hits. No search has been fabricated. B1--B10 checked: self-contained TeX, all definition interfaces included or notions written inline, source labels/tags correct, no duplicate statement, no Mathlib match. C1--C8 checked against the actual cited statements; no cycle introduced because new nodes have no proof dependencies and their definition dependencies do not depend on the item. D1--D5 checked: the new nodes separate geometry, module-colimit algebra and naturality, rather than restating the target under its tail/rank assumptions. E1--E7 checked on the cases above. There is no new statement dispute. The five assembly steps are each below 2000 characters, and their total is 2761 characters (below 3000).

### Repair of the landing refusal (2026-10-22)

The returned entry says that the approved side-project completion was not promoted to the live queue DAG. I compared all top-level fields of returned-item.json with the current read repository: they are identical, including the eight-step proof, statement, statement dependencies, blueprint route, Lean record and reviews. The sandbox differs from that base only in proof, proof_deps and split_report; it retains the intended three-node re-split rather than resubmitting the old completed side proof. The released stage-1 repair note still requires at least two statement-only nodes and an assembly of at most 3000 characters. I retain all three work units, the original arguments below, the historical searches and their actual log results, and the unchanged target statement. Delivery is rebuilt on the current DAG by deliver.py, rather than re-pushing an earlier commit.

I re-read every currently cited statement: the presentation and tail-chart statements supply exactly assembly steps 1 and 2; the affine flatness iff and stalk-flatness definition finish step 2; the cartesian quotient statement supplies step 3. The current Hilbert-function and coordinate-ring/Euler statements still apply to S=k[x] and M=S/I, including unsaturated and unit ideals, in step 4. The geometric-fibre, tensor-pullback and finite-free-frame definitions give step 5 with the earlier base-change result. Every citations.json quote remains verbatim in the current statement. No cited statement needs changing in the assembly. Local free frames are taken separately in each degree, and the flatness argument uses the nonempty small tail; there is no common-frame or regular-coordinate assumption. I re-read the Stacks passages listed above to check the geometric, flat-colimit and Hilbert-polynomial hypotheses.

The first required dry run identified one newly present same-tag candidate, lem-trf-free-projective-bundle-base-change-space (01O3). I read its full statement: it gives the free symmetric-algebra/projective-space comparison, with compatible base restrictions, but no quotient image ideal or cartesian embedded quotient square. The new cartesian node is therefore not its special case. I added this exact pair and distinction under Not duplicates. Its general projective-space comparison can be used when that new node is later split; it does not discharge this independent quotient-naturality argument. I also repeated the project Lean tag/concept attachment search and found no matching completed declaration. No existing proof, citation, search, statement or Lean record was discarded in this repair.

## Not duplicates

lem-sfb-polynomial-quotient-proj-cartesian vs lem-trf-free-projective-bundle-base-change-space: the existing statement identifies the relative Proj of the symmetric algebra of a trivial free sheaf with base-change projective space and pins its polynomial charts; it does not treat a homogeneous quotient ideal, tensor pullback of its equations along an arbitrary morphism, or the cartesian square of the specified closed embeddings. The new statement supplies these quotient and embedding comparisons for arbitrary J, without flatness or finite generation assumptions.

lem-sfb-polynomial-quotient-proj-presentation vs def-sbc-locally-finite-presentation: the existing node concerns Morphisms locally of finite presentation; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs def-sc-degree-zero-module-fractions: the existing node concerns Equal-degree fractions in a localized module; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs def-sc-p1-proj-chart-isomorphism: the existing node concerns Chart comparison for the projective line; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs def-weil-pbc-proj-twisting-sheaf: the existing node concerns The sheaf of a graded module on Proj and the twisting sheaves O(d); it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-chow-closed-model: the existing node concerns Closed model of a quasi-compact immersion; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-kun-projective-implies-proper: the existing node concerns Projective morphisms are proper; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-pc-cartier-criterion: the existing node concerns The Cartier criterion on smooth one-dimensional fibres; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-finite-pi-away-fractions: the existing node concerns Finite localization coordinates preserve shifted equal-degree fractions; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-away-degreezero-exact: the existing node concerns Exactness on degree-zero away-localized charts; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-away-degreezero-exact-pair: the existing node concerns Exact pairs on equal-degree away fractions; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-away-degreezero-lift: the existing node concerns Lifting equal-degree fractions through a graded localized map; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-fixed-chart-map: the existing node concerns A map of fixed associated sheaves from chart data; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-graded-chain-maps-exact: the existing node concerns Exact maps between fixed associated sheaves of a graded chain; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-graded-module-chart-data: the existing node concerns Associated-sheaf chart data for an integer-graded polynomial module; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-homogeneous-basis-coordinates: the existing node concerns Homogeneous vectors have shifted homogeneous basis coordinates; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-homogeneous-basis-proj-coproduct: the existing node concerns Homogeneous basis comparison on polynomial Proj; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-homogeneous-basis-sheaf-twists: the existing node concerns Associated sheaves of homogeneous bases are finite sums of twists; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-proj-tilde-functorial: the existing node concerns Functoriality of the associated sheaf on Proj; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-proj-twist-glued-comparison: the existing node concerns Comparison of a Proj twist with any prescribed glued twist; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-proj-twist-inverse-transport: the existing node concerns Transport of one Proj twist along any chart comparison; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-proj-twist-transported-data: the existing node concerns Standard twist data on the transported polynomial Proj twist; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-projective-space-twist-data: the existing node concerns Standard generators for the integral-model projective-line twist; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-section-action-laws: the existing node concerns Action laws for the direct sum of twisted sections; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-p1-sheafify-graded-chain: the existing node concerns Exact associated-sheaf chains transported to the projective line; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-basic-open-localization-detection: the existing node concerns Detection of equality in A_f at homogeneous primes; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-finite-twist-coproduct-fractions: the existing node concerns Fraction charts of finite coproducts of twists over a graded ring; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-graded-chart-comparison: the existing node concerns A graded linear equivalence compares Proj sheaves supplied by fraction charts; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-single-twist-basic-open-fractions: the existing node concerns Homogeneous fraction charts for an individual Proj twist; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-twist-degree-detection: the existing node concerns Detection of the degree of an ordinary fraction at homogeneous primes; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-twist-finite-local-representatives: the existing node concerns Finite principal representatives of a twist section; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-twist-finite-localization-data: the existing node concerns Finite principal-localization data of a locally homogeneous twist section; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-twist-fraction-descent: the existing node concerns Descent of a twist section to a homogeneous basic-open fraction; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-twist-fraction-realization: the existing node concerns Realization of a shifted homogeneous fraction as a twist section; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-twist-local-clearing: the existing node concerns Local cleared fractions for twist sections on a Proj chart; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-twist-local-overlap-compatibility: the existing node concerns Overlap compatibility of finite twist representatives; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sc-proj-twist-local-overlap-pointwise: the existing node concerns Pointwise overlap equality for twist representatives; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sfb-flat-graded-tail-proj: the item also proves tail flatness and Hilbert polynomials; the new node has no rank/tail hypotheses and isolates only the projective presentation and chart geometry.

lem-sfb-polynomial-quotient-proj-presentation vs lem-sfb-proj-graded-sheafification-exact: the existing node concerns Exactness of associated graded-module sheaves on Proj; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-trf-finite-locally-free-composition: the existing node concerns Composition of finite locally free morphisms; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-trf-projective-bundle-proper: the existing node concerns Projective-bundle morphisms are proper; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-finite-separable-base-refinement: the existing node concerns Finite separable base refinement; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-chart-restriction-is-localized: the existing node concerns Restriction from a principal chart is localized; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-chart-basis-comparison: the existing node concerns Compatible principal-open section equivalences from homogeneous-chart localization comparisons; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-core: the existing node concerns Normalized sectionwise fixed-chart comparisons; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-generators: the existing node concerns Whole-chart sections generate principal-open sections; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-chart-gluing: the existing node concerns Finite gluing of graded-module charts; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-chart-principal-localization: the existing node concerns ProjGradedModuleChartPrincipalLocalization; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-chart-quasicoherent: the existing node concerns Quasi-coherence from graded-module chart identifications; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-chart-tilde-comparison: the existing node concerns Affine tilde comparison for one positive homogeneous graded-module chart; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-sheaf-exists: the existing node concerns The sheaf of modules on Proj(S) attached to a graded module exists; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-sheaf-extension: the existing node concerns Graded-module sheaf on Proj: Extension; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-sheaf-global-sections: the existing node concerns Graded-module sheaf on Proj: GlobalSections; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-graded-module-sheaf-stalks: the existing node concerns Graded-module sheaf on Proj: Stalks; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-proj-structure-sheaf-standard-sections: the existing node concerns Sections and stalks of the structure sheaf of Proj on standard opens; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-projective-space-twisting-sheaf-charts: the existing node concerns The twisting sheaf O(1) on P^n_Z on the standard charts; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs lem-weil-pbc-qcqs-morphism-permanence: the existing node concerns Quasi-compactness and quasi-separatedness of morphisms between qcqs schemes; finite presentation is stable under base change; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs new-canonical-eval: the existing node concerns Canonical evaluation on a localized module; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-polynomial-quotient-proj-presentation vs new-finite-values: the existing node concerns Finite representatives realize section values; it does not supply the whole homogeneous sheaf quotient identification, finite-presentation conclusion and covering coordinate charts over every locally Noetherian base.

lem-sfb-locally-free-tail-chart-flatness vs def-sc-degree-zero-module-fractions: the existing node concerns Equal-degree fractions in a localized module; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs def-weil-pbc-associated-graded-ring: the existing node concerns Associated graded ring of an ideal; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs def-weil-pbc-proj-twisting-sheaf: the existing node concerns The sheaf of a graded module on Proj and the twisting sheaves O(d); it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs lem-coef-exponential-dependent-product-representation: the existing node concerns The exponential pullback represents maps over an object; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs lem-sc-finite-pi-away-fractions: the existing node concerns Finite localization coordinates preserve shifted equal-degree fractions; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs lem-sc-p1-away-degreezero-exact: the existing node concerns Exactness on degree-zero away-localized charts; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs lem-sc-p1-away-degreezero-exact-pair: the existing node concerns Exact pairs on equal-degree away fractions; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs lem-sc-p1-away-degreezero-lift: the existing node concerns Lifting equal-degree fractions through a graded localized map; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs lem-weil-pbc-filtered-colimit-flat-modules: the existing node concerns Filtered colimits of flat modules are flat; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs lem-weil-pbc-flat-colimit-presentation-same-universe: the existing node concerns Flatness from a same-universe filtered colimit presentation; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs lem-weil-pbc-flat-ring-map-iff-ind-flat: the existing node concerns A ring map is flat if and only if it is ind-flat; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-locally-free-tail-chart-flatness vs lem-weil-pbc-henselization-flat-quotients: the existing node concerns The henselization of a pair is flat with the same quotients by powers of the ideal; it does not identify degree-zero homogeneous localization with the colimit of the finite locally free high-degree sections and give the explicit extension formula.

lem-sfb-polynomial-quotient-proj-cartesian vs def-nagata-graded-algebra-pullback-data: the existing node concerns Coefficientwise pullback data for a quasi-coherent graded algebra; it does not state the quotient image-ideal equality together with compatibility of the fixed polynomial closed embedding on arbitrary base change.

lem-sfb-polynomial-quotient-proj-cartesian vs def-pur-projective-bundle-tautological-data: the existing node concerns Normalized projective-bundle realization and chart data; it does not state the quotient image-ideal equality together with compatibility of the fixed polynomial closed embedding on arbitrary base change.

lem-sfb-polynomial-quotient-proj-cartesian vs def-sfb-projective-coordinate-hilbert-polynomial: the existing node concerns Coordinate Hilbert polynomial and canonical geometric-fibre embeddings; it does not state the quotient image-ideal equality together with compatibility of the fixed polynomial closed embedding on arbitrary base change.

lem-sfb-polynomial-quotient-proj-cartesian vs lem-per-conormal-presentation-proj-base-change: the existing node concerns Nil-immersion comparison for Proj of a conormal presentation; it does not state the quotient image-ideal equality together with compatibility of the fixed polynomial closed embedding on arbitrary base change.

lem-sfb-polynomial-quotient-proj-cartesian vs lem-pur-projective-bundle-base-change-coherence: the existing node concerns Coherence of projective-bundle coefficient base change; it does not state the quotient image-ideal equality together with compatibility of the fixed polynomial closed embedding on arbitrary base change.

lem-sfb-polynomial-quotient-proj-cartesian vs lem-pur-projective-bundle-tautological-geometry: the existing node concerns Finite locally free projective bundles and tautological base change; it does not state the quotient image-ideal equality together with compatibility of the fixed polynomial closed embedding on arbitrary base change.

lem-sfb-polynomial-quotient-proj-cartesian vs lem-weil-pbc-ample-very-ample-immersion-affine-base: the existing node concerns An ample invertible module over an affine base: a power is the pullback of O(1) along an immersion into projective space; it does not state the quotient image-ideal equality together with compatibility of the fixed polynomial closed embedding on arbitrary base change.

lem-sfb-polynomial-quotient-proj-cartesian vs lem-weil-pbc-projective-space-proj-separated: the existing node concerns Projective space over a ring is separated over the ring; it does not state the quotient image-ideal equality together with compatibility of the fixed polynomial closed embedding on arbitrary base change.

## Validation

The required deliver.py --no-push will run the server preflight, check_dag and review_split. No local DAG/preflight check or compiler is invoked. The final push uses the same delivery command after the dry run exits OK.

### Current-DAG retry verification (2026-10-22T13:11:52+00:00)

The retained repair was not regenerated from the old eight-step proof. I compared the saved returned item with the current repository again: every field is identical. The repair still changes proof, proof_deps and split_report only, with three new unsplit nodes. There is therefore no changed statement to adapt, and no newer live dependency invalidates an assembly step. I re-read all ten cited statements and verified that citations.json covers every step/node pair exactly. The first dry run exited successfully with OK (not pushed), candidate df20ca0a612; a final dry run follows the refreshed review record.

Statement SHA-256 values at this review (for reproducing the current-dependency comparison):

- def-amb-finite-locally-free-module: 2eed8ea68d4d5e88290ff5ac5168007683ad5f9a9ba6f9b99016e407a332cdb3
- def-pc-module-pullback: 080d21bf883db34b76d0d6df957f9747d7127e5e3d7f281ee3d5d093d5cc3f83
- def-weil-flat-morphism: 650c52d56f263fc12deea8ae792628509100f4554244ac2c23150d264ea0a681
- def-weil-geometric-fibre: 5b3f3adf0d3923a9a7c40659f72ad015a1858317e1b5a860ad9c0e8025f5acd3
- lem-sfb-locally-free-tail-chart-flatness: e8b52b1006cceebf5f7cb181f8d0bd9d01d7ebeac48b17224ca7a803293368bc
- lem-sfb-polynomial-quotient-proj-cartesian: eff9bbb2f96ab622cb12ad1866e0cf43fdd6fe253edc60266c873bd602b396eb
- lem-sfb-polynomial-quotient-proj-presentation: c8706b21d26ba2bef96bc3dcd493e68cde78e44322cba93a70400597fad69333
- lem-sfb-projective-coordinate-ring-euler-polynomial: 034da3fa5a51f66e6042ecfc30aee03ae30e9dba49fe583e17e5e2bee9ecbb51
- lem-trf-standard-graded-hilbert-function: 1892c02502bab976d2e043bd0e667d247ef992360f652d1443570f7726c4adae
- lem-weil-pbc-flat-ring-map-iff-flat-affine: 1134454d6ccf683968a1179779938d7e3041c60692bca6fcb6e23207bdd35aa7

I also re-read the source statements and the 01O3 and 0AG7 proofs. The base-change source omits some gluing details; the retained cartesian node exposes that work through its fraction-coordinate compatibility, rather than treating it as automatic. The 0AG7 comparison applies to the finite polynomial-ring module S/I, and the existing coordinate-ring/Euler node supplies the unsaturated-ideal conclusion; no recovery theorem is being applied to a nonstandard zero algebra. The new chart-flatness node retains the equality-of-fractions argument needed for zero and nilpotent coordinates. All previous searches and their results remain intact.


### Landing-refusal rebase review (2026-10-23)

I repeated the returned-head/current-DAG comparison for this retry. The saved returned-item.json and current repository item are identical in every top-level field. All ten assembly citation statements have the same SHA-256 values recorded in the preceding review; I read them again, and every quote in citations.json is still verbatim with exactly one entry per step/node pair. Thus there is no changed cited statement requiring a mathematical adjustment. The released stage-1 repair order remains active. I retain the approved three independent statement-only nodes and the 2761-character assembly rather than substituting the old eight-step side completion. The delivery tool rebuilds this repair on its freshly fetched current DAG; the first dry run of this retry exited OK at 855a41875f2. This refreshed report and split_report record the current rebase audit, and the final dry run will cover their exact contents.

For steps 1--3 I checked the specified presentation, flat chart rings, and image-ideal/cartesian statements against the hypotheses in the item: a polynomial quotient over a locally Noetherian base, degreewise finite local freeness, and an arbitrary coefficient morphism respectively. I re-read the actual Stacks statements/proofs at 07ZK, 01O3, 01TX and 05UT: neither flat base change nor injective pullback of J is required. For step 4 I re-read 0AG7 and 08AE together with the existing Hilbert-function and coordinate-ring/Euler statements; the finite module is S/I over S=k[x], so the unit and unsaturated ideals are included. Step 5 uses the already established arbitrary base change and a separate finite free frame in each degree; eventual equality of rational polynomials finishes it. The fraction-colimit formula still works when a coordinate is zero or nilpotent, and the zero quotient gives the empty family with polynomial zero. No new statement dispute arose, no source or argument was discarded, and no assembly step exceeds 2000 characters.

The logged Mathlib searches were read and reused because neither the three new statements nor their search questions changed. The current project source search again found no matching declaration under WeilConjectures; the two corresponding Sheaf declarations still end in sorry. I changed only the sandbox review record and split_report for this rebase retry, preserving all mathematical statements, arguments, searches, citations and Lean metadata. The required server preflight, rather than a local git operation or an unchanged stale push, produces the rebased delivery commit.
