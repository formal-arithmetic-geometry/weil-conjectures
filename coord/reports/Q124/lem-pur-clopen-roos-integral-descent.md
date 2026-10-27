## Worker report

Repaired the 2026-10-22 re-split return for Q124. The sandbox initially contained only dispatcher markers, not a delivered node or report. I copied the current read-only repository item, whose ten proof texts have exactly the returned lengths (649, 593, 973, 883, 868, 827, 1013, 1090, 1178, 562), and continued that accepted mathematical argument. I did not reconstruct or weaken its statement. The item statement and statement dependencies are unchanged. The existing source, citations, Mathlib search records, Lean record and review metadata were retained. No repository or launcher file was written and no git command, compiler, Lake or build tool was run by the worker.

Files written under dag/nodes/sec-smooth-purity/:

- lem-pur-clopen-roos-integral-descent.json: item, four assembly steps, 1792 proof-text characters.
- lem-pur-clopen-strict-tower-roos-equivalence.json: statement, unsplit, no Mathlib match; owns original steps 1-4 and the zero-category assertions of step 10.
- lem-pur-clopen-augmented-integral-descent.json: statement, unsplit, no Mathlib match; owns original steps 5-7 and the empty-bound assertion of step 10.
- lem-pur-clopen-completed-operation-towers.json: statement, unsplit, no Mathlib match; owns original steps 8-9 and their empty-partition cases from step 10.

The new statements are 2679, 3219 and 3361 characters: three comparable work items, each a proper part of the returned proof. Each introduces its own schemes, cover, coefficients, categories, maps and bounds. None has proof steps, proof dependencies or a proof sketch inside its statement. Each can be assigned independently; the exact original argument for its future worker is retained below. The split is specifically the human-requested spreading of an already accepted long proof, rather than a claim that newly renaming its clauses proves them. The parent assembles these independently stated results and the pre-existing unbounded restriction equivalence.

Attachments: none. I searched lean/WeilConjectures/ for the exact blueprint tag, Roos/clopen notions and finiteClopen theorem names. No finished project declaration states this item. lean/Sheaf/Paper/ClopenRoosIntegralDescent.lean has the relevant declarations, but its strict-tower, cone, triangle, reduction, membership, tensor and scalar-extension proofs contain sorry. Those statements are useful cross-checks, not attachments.

WANTED: none. Both the Stacks source and Bhatt--Scholze PDF are present.

What was wrong: the returned proof carries 8636 characters of real mathematical work in one item. It is now distributed into three unsplit nodes, with four short assembly steps in the item. There is no statement dispute or mathematical correction. Nothing remains unfinished in this one-level split; the three new proofs are deliberately left for future stage-1 workers.

## Sources and search record

For the item and strict-tower node I read literature/stacks-project/derived.tex, Tag 08TC, label derived-definition-derived-limit, and Tag 07KC, label derived-lemma-products. The definition records the distinguished triangle and the subsequent lemma gives termwise representatives of derived products under exact countable products. They do not by themselves assert the clopen equivalence: that part remains an explicitly agent-written application of the existing module-gluing and derived-tensor-calculus statements. I also read the current main-20261015 def-pur-section-invariant.md, final invertibility assertion, and the unit sk-def-purity-conv and chapter sec-smooth-purity records. The blueprint sentence only motivates the expanded finite-clopen passage; no purity route or unit statement is changed.

For the augmented integral node I read Bhatt--Scholze, Proposition 3.5.1(1) and Definition 3.5.2 on printed p. 24, with the actual completed ring and natural quotient map. I opened def-weil-integral-reduction-tower and def-weil-derived-complete: their c_n=[gamma_n][q]^{-1}, quotient transitions and specified first map c are the ones retained. I read def-weil-derived-complete-integral-detailed and def-weil-finite-tor-amplitude to check that the intervals must be independent of the positive reduction level, not just bounds at each level separately. The fixed-interval detection used in its handoff is exactly the statement of lem-pur-clopen-finite-constructibility-bounds, not an appeal to its proof.

For the completed-operation node I read Bhatt--Scholze Definition 3.4.10 and Lemma 3.4.12(4) on printed p. 22 and Proposition 3.5.1(3) on printed p. 24. I read the full statements of def-pur-integral-derived-operations and def-weil-integral-scalar-extension: both use the explicit strict quotient towers, Res_n and actual coefficient projections. The source motivates completed operations; the displayed clopen comparisons are the agent application. Scalar extension uses rho_m=iota_m pi_m^E into A_{L,m}, not an identification of E and L quotient rings. Ramification is allowed. The derived-category isomorphisms are stated in the new node in addition to the strict chain-level maps; this is not a substitution of cohomology-group isomorphisms for derived objects.

Before creating the nodes I searched the whole DAG by clopen/Roos, integral restriction/gluing, augmentation, coefficient-extension and completed-operation terms and by the shared Stacks tags; searched the imported blueprint using tools/blueprint_refs.py search for Roos, clopen, completed tensor, integral scalar, strict tower and quotient augmentation; and searched the read-only project source. The nearest blueprint ancestor is def-pur-section-invariant. All three nodes record its final invertibility assertion and the precise old proof steps, via this item and lem-pur-finite-clopen-derived-decomposition. No imported blueprint node states one of the new statements exactly.

All new nodes have actual msearch.py records: LeanFinder twice with different phrasings, Loogle, Mathlib grep, and LeanSearch. Complete service outputs are retained in the sandbox and in mathlib_searches; searches.jsonl is the command-generated log. The strict-tower node's Loogle hits are mappingCone API only; the second semantic phrasing finds sheaf limits and coherent-topology facts. The augmented node's first phrasing finds finite topological partitions and box integrals; the second finds bounded representatives and K-injective facts. The broad grep also found box-integral partitions, so I made an additional CategoryTheory grep, which returned no hits. None states adic clopen descent. The operations node finds ordinary AdicCompletion tensor formulas, restriction composition, and sheaf limits. I opened the Mathlib MappingCone, sheaf Limits and AdicCompletion/AsTensorProduct sources: none is an exact match or one-line specialization for these strict derived clopen comparisons. LeanSearch was rate-limited for the first two nodes and is recorded as unavailable; it succeeded for the third, whose hits were read. No unavailable result is classified as absence.

## Review by Q124

I reviewed every numbered request in the re-split return. The item statement remains verbatim; the old argument is not shortened into an unsupported sketch. Original steps 1-4 are assigned to the first new node, steps 5-7 to the second, steps 8-9 to the third, with step 10's zero categories, vacuous conditions and chosen interval distributed across all three. The complete old texts, with their original cited statements, follow below so that future workers can recover every construction. The parent is under 3000 characters and the delivery adds three unsplit, statement-only nodes of comparable size, not one proxy for the whole item. There is no remaining non-elementary assembly step over 2000 characters.

Assembly step 1 uses lem-pur-clopen-strict-tower-roos-equivalence. I opened its entire new statement: it asserts the strict-tower equivalence, identifies the sectionwise product gluing functor on objects and maps, pins the product comparison to its projections, specifies both signed cone coordinates and the connecting map, states an isomorphism in the derived category, and detects distinguished specified triangles in both directions. Thus the assembly is taking its statement rather than a construction hidden in a proof. Its arbitrary commutative ring sheaf R specializes to the completed coefficient sheaf without any additional exactness assumption: pro-etale exact countable products are already part of the original argument, supplied in its handoff by lem-weil-proetale-countable-products-exact.

Assembly step 2 uses lem-pur-clopen-augmented-integral-descent. I checked the new statement against the original reduction definitions and all three original steps: the comparison is on the actual gamma_n and tau_n and sends [q]^{-1} to [r_i q]^{-1}; it is not just an isomorphism of source and target objects. The bijection of connecting maps keeps the prescribed c fixed. It gives both integral membership equivalences, same-interval support/Tor tests at every positive level, finite minima/maxima and any common larger bounds. Its assumptions are exactly the finite-type finite-field setting of the item. K-flat flat-term resolutions exist in the cited coefficient setup; the new assertion explicitly treats arbitrary K and natural derived comparisons, not only a previously selected model. In the retained argument, the module-gluing statement supplies the coefficient projections and unit, the derived-tensor-calculus statement supplies K-flat restriction and the tensor comparison, and finite-constructibility-bounds supplies precisely fixed-interval detection.

Assembly step 3 uses only lem-pur-finite-product-derived-tensor-calculus together with the result just obtained in step 2. I reread its full statement: the unbounded equivalence has restriction as forward functor and direct-sum zero insertion as inverse, with natural identities and joint isomorphism detection. Step 2 identifies exactly the objects of the full integral subcategories. Restricting the same functors, unit and counit is then elementary; no new existence, exactness or tensor theorem is being hidden in this step.

Assembly step 4 uses lem-pur-clopen-completed-operation-towers and, for the empty partition, the first two new statements. I checked that the operation node includes derived-category isomorphisms as well as strict towers; gives the transition formula in both tensor factors; retains Res_n as a functor to completed-ring modules; states preservation of coefficient units; and specifies the L-coefficient tower action through pi_m^L separately from rho_m on the E side. Its naturality and resolution independence are conclusions, so the parent does not borrow a future proof. Its empty assertions and the first two nodes supply zero maps and the optional [0,0] interval. No cone functor on an arbitrary triangulated category is assumed.

For the new nodes I checked B1-B9: empty proof lists, self-contained TeX statements, referenced definition nodes actually defining the notions, correct sources/places, exact logged queries and actual verdicts, blueprint ancestry and no silent use of a definition as a theorem. Sources are agent applications when appropriate. C1/C4 were checked by opening the complete statements of all 13 original dependencies; their precise uses are retained with the verbatim old steps below. The new nodes do not carry proof dependencies prematurely. The citations.json entries for the parent quote actual substrings of the new statements or the unbounded-equivalence statement, and were checked by substring membership. The source route contains no prohibited reference.

Small cases: for a one-piece identity cover every section, product coordinate, gamma, tau and tensor generator is unchanged; a constant identity-transition tower gives the same v=1-s and the same signed cone differential on each component. Empty pieces give zero factors, and an empty covering index forces X empty; then all positive reductions and completed operations are zero and every interval works, so [0,0] is valid without taking min or max of an empty set. With component bounds [-2,0] and [1,3], the global interval [-2,3] works uniformly in n, and the converse restricts that same interval. No infinite-component minimum/maximum or infinite direct-sum argument is used. For ramified E subset L, the actual map rho_m exists because varpi_E^m O_L is contained in varpi_L^m O_L, so no equality of ideals or unramifiedness is used. For a strict map f, the Roos comparison acts diagonally on both summands, retaining projections and signed connecting maps. All indexing categories are countable towers on the fixed small-site presentation; no large colimit is introduced.

## Not duplicates

lem-pur-clopen-strict-tower-roos-equivalence vs def-weil-pbc-common-stage-cones: the existing definition concerns cone triangles in a common coefficient-field stage of the rationalized pair category; it does not compare module sheaves on a finite clopen cover or strict towers.

lem-pur-clopen-strict-tower-roos-equivalence vs def-weil-pbc-derived-inverse-limit: the existing definition specifies a sequential Roos derived limit in one fixed coefficient category; it does not construct a clopen equivalence of strict towers or its projection-normalized comparison.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-weil-derived-countable-products-core: the existing statement gives a universal property of localized termwise products in one abelian category with CountableAB4Star; it has no clopen sites, strict-tower equivalence, cone comparison or triangle reflection.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-weil-derived-countable-products-existence: the existing statement asserts existence of derived countable products under the core hypotheses, with no restriction/gluing or strict cone comparison.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-weil-derived-countable-products-properties: the existing statement gives the localized termwise-product property and homology preservation of products, but no comparison across component sites or reflection of specified triangles.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-pur-clopen-roos-integral-descent: the item additionally includes augmented integral reductions, completeness, uniform constructibility/Tor conditions, completed tensor and scalar extension; the new node isolates only the strict-tower equivalence and its specified Roos triangle argument (old steps 1-4). This proper-part extraction is explicitly required by the re-split return.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-pe-roos-cone-calculus: the existing statement concerns cones and shifts of maps inside one module category; it provides no finite-clopen restriction/gluing equivalence or reflection of specified triangles across a product category.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-sbc-roos-coordinates-derived-limit: the existing statement constructs a derived-limit triangle from signed coordinates in one category; it does not compare restriction/gluing of strict towers across a finite clopen cover.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-pc-milnor-projection-factorization: the existing statement is surjectivity of a cohomology-to-inverse-limit projection for abelian groups, not a restriction equivalence on towers of module sheaves.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-pc-milnor-boundary-factorization: the existing statement is the Milnor boundary injection and naturality on cohomology of abelian-group towers, with no clopen tower gluing or derived triangle reflection.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-pc-abelian-groups-exact-products: the existing statement only gives exactness of products in Ab; the new node constructs and compares strict towers on distinct pro-etale component sites.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-sfb-finite-proper-classical-amplitude: the existing statement concerns proper direct image, classical cohomological amplitude and preservation of products, not restriction/gluing on clopen components or strict-tower equivalence.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-formal-closed-pullback-derived-products: the existing statement is product preservation for closed inverse image of condensed module objects in a separated setting; the new statement is about ordinary module sheaves for arbitrary R on a finite clopen cover, including strict towers and Roos triangles.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-sfb-augmented-scalar-roos-resolution: the existing statement restricts scalars between two rings on the same site and normalizes augmented Roos resolutions; the new node restricts schemes to different component sites and proves a strict-tower equivalence and reflection of specified triangles.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-sfb-left-complete-heart-upper-bound: the existing statement propagates an upper bound from a heart using left completeness; it gives no clopen restriction/gluing comparison.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-weil-derived-limit-existence: the existing statement gives existence of abstract or tower-resolution derived limits; it does not identify sectionwise clopen gluing or compare its strict cone maps and specified triangles.

lem-pur-clopen-strict-tower-roos-equivalence vs def-weil-category-product: the existing statement defines a product and its universal property; it proves no clopen or Roos comparison.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-pur-roos-additive-comparison: the existing generic result assumes invertibility of the canonical product comparison and supplies cone functoriality; the new node constructs the finite-clopen tower equivalence, identifies its sectionwise product maps and reflects specified derived triangles. That generic result is a reusable ingredient, not the whole new statement.

lem-pur-clopen-strict-tower-roos-equivalence vs lem-cbc-exact-product-functor-strict-limit: the existing result assumes one exact product-preserving functor and compares total derived limits; it does not construct a clopen strict-tower equivalence or its inverse gluing, and does not state reflection of all specified triangles by the product equivalence.

lem-pur-clopen-augmented-integral-descent vs lem-sf-clopen-derived-compatibility: the existing result assumes normalized clopen restriction data and preserves completeness in one direction and local residue Tor intervals. The new statement gives a finite-cover converse by gluing the connecting map with the fixed first map, and simultaneous integral constructibility and bounds uniform at every positive coefficient level.

lem-pur-clopen-augmented-integral-descent vs lem-pur-clopen-finite-constructibility-bounds: the existing result treats one finite coefficient ring. The new result concerns augmented reductions of an integral object, derived completeness and one pair of intervals uniform over the whole quotient tower. The existing finite result is used in the preserved step 7 argument rather than recreated as a node.

lem-pur-clopen-augmented-integral-descent vs lem-sf-clopen-lisse-complete-localization: the existing result constructs a partition of a weakly contractible affine, with lisse-trivialization and one-direction restriction. The new statement assumes a given arbitrary finite clopen cover and detects integral completeness and simultaneous uniform bounds in both directions; no affine or weak-contractibility assumption.

lem-pur-clopen-augmented-integral-descent vs lem-pur-clopen-roos-integral-descent: the new statement isolates the resolution augmentation, completeness and uniform bounds in old steps 5-7; it contains no equivalence of arbitrary strict towers, no general Roos chain comparison and no completed tensor or L-scalar-extension comparison.

lem-pur-clopen-completed-operation-towers vs lem-sf-open-tensor-quotient-augmentation: the existing statement is a projection formula involving open extension by zero, constructible inputs and a specified tensor quotient augmentation. The new statement restricts arbitrary inputs to clopen components, and also treats coefficient extension to L and its actual quotient maps.

lem-pur-clopen-completed-operation-towers vs lem-pur-finite-product-derived-tensor-calculus: the existing result gives ordinary and derived tensor/change-of-rings comparisons, K-flat restriction and the ambient equivalence. The new result identifies full strict reduction towers before taking the explicit Roos completed operations, including coefficient units and ramified integral scalar-extension towers.

lem-pur-clopen-completed-operation-towers vs lem-pur-clopen-roos-integral-descent: the new statement is just the completed-operation work in old steps 8-9, with specified strict tensor and scalar tower maps. It proves none of the arbitrary strict-tower equivalence, specified-triangle reflection, integral membership or uniform bounds of the item.

## Original arguments retained for the new-node workers

The following are verbatim proof-step texts from the returned repository item, including its exact cited-node lists. They are handoff material in this report, not proof lists in the unsplit new nodes.

### Original step 1 → lem-pur-clopen-strict-tower-roos-equivalence

Apply [lem-pur-clopen-ringed-module-gluing] with $R=\widehat{\mathcal O}_{E,X}$. Its exact restriction/gluing equivalence identifies the coefficient rings, their quotient projections and all coefficient transitions. Apply the two functors degreewise and at each tower level; give the glued tower transition $G((t_{i,n})_i)$ and a glued tower morphism $G((f_{i,n})_i)$. The chain-map and transition-compatibility equations hold because they hold in every component and the module equivalence is faithful. Its natural unit and counit commute with these maps by naturality, so they give inverse equivalences on strict towers, including their morphisms.

Uses: lem-pur-clopen-ringed-module-gluing.

### Original step 2 → lem-pur-clopen-strict-tower-roos-equivalence

Countable products are sectionwise by [lem-weil-proetale-countable-products-exact]. For $U\to X_i$, its pullback to $X_j$ is empty for $j\ne i$, while its pullback to $X_i$ is $U$. Thus restriction identifies $(\prod_n C_n)^m(U)$ with $\prod_n(r_iC_n)^m(U)$, with the same projections and differential. Conversely the product reindexing $\prod_n\prod_i F_{i,n}(U\times_X X_i)\cong\prod_i\prod_n F_{i,n}(U\times_X X_i)$ identifies products under gluing. Each reindexing is the identity on its $(i,n)$ coordinate; hence it preserves restriction maps, module actions and every product projection.

Uses: lem-weil-proetale-countable-products-exact, lem-pur-clopen-ringed-module-gluing.

### Original step 3 → lem-pur-clopen-strict-tower-roos-equivalence

Put $P_C=\prod_nC_n$ and $v_C=1-s_C$. The $n$th projection of $r_iv_C$ is $r_i\operatorname{pr}_n-r_it_n\,r_i\operatorname{pr}_{n+1}$, so under step 2 it is exactly the $n$th projection of $v_{r_iC}$. Use the explicit model [def-weil-strict-roos-model]: in degree $m$ its shifted cone is $P_C^{m-1}\oplus P_C^m$ with $d(y,x)=(-dy-v_Cx,dx)$. Apply the product comparisons of step 2 separately to $y$ and $x$. Additivity of restriction and the displayed equality for $v$ make this a chain isomorphism with inverse the two inverse product comparisons. A strict tower map $f$ acts diagonally by $(\prod_nf_n,\prod_nf_n)$, so both orders of composing the comparisons have the same two coordinates. The cone projection to $P_C$ is $(y,x)\mapsto x$ and the connecting map $P_C\to\operatorname{Cone}(v_C)[-1][1]$ is $z\mapsto(-z,0)$ with this Roos-triangle convention. These formulas commute with restriction, retaining every level projection. This is strict-complex functoriality.

Uses: def-weil-strict-roos-model, lem-pur-clopen-ringed-module-gluing.

### Original step 4 → lem-pur-clopen-strict-tower-roos-equivalence

The exact countable products supplied by [lem-weil-proetale-countable-products-exact] meet the hypothesis of [lem-weil-derived-limit-products-core], on $X$ and on each $X_i$. Therefore the termwise product cones of step 2 represent the actual products in the derived categories. The triangulated restriction equivalence of [lem-pur-finite-product-derived-tensor-calculus] sends distinguished triangles to the component distinguished triangles. Applying it to the triangle in [def-weil-derived-limit], with the same product projections, sends $1-s$ to $1-s$ by step 3 and retains both triangle maps. Conversely a tuple of such distinguished Roos triangles is a distinguished triangle in the product triangulated category, and its inverse image is distinguished under the inverse equivalence. Thus the derived-limit property with its specified triangle is preserved in both directions.

Uses: lem-weil-proetale-countable-products-exact, lem-weil-derived-limit-products-core, lem-pur-finite-product-derived-tensor-calculus, def-weil-derived-limit.

### Original step 5 → lem-pur-clopen-augmented-integral-descent

Represent $K$ by $q:P\to K$ as in [def-weil-integral-reduction-tower]. The K-flatness and flat-term assertions in [lem-pur-finite-product-derived-tensor-calculus] show that $r_iP\to r_iK$ is an admissible resolution. Its termwise change-of-rings comparison identifies $r_i(P\otimes_R(A_{E,n})_X)$ with $r_iP\otimes_{R_i}(A_{E,n})_{X_i}$. On tensors it sends $p\otimes a$ to $r_ip\otimes r_ia$. Consequently it sends $\gamma_n(p)=p\otimes1$ to the component $\gamma_n$, and $\tau_n(p\otimes a)=p\otimes\rho_n(a)$ to the component $\tau_n$, because the coefficient identifications preserve $1$ and $\rho_n$. Exact restriction also sends $[q]^{-1}$ to $[r_iq]^{-1}$. Hence the actual $c_n=[\gamma_n][q]^{-1}$, not merely their source and target objects, and the transitions $t_n=[\tau_n]$ are identified. This proves the required reduction comparison on objects and maps.

Uses: def-weil-integral-reduction-tower, lem-pur-finite-product-derived-tensor-calculus, lem-pur-clopen-ringed-module-gluing.

### Original step 6 → lem-pur-clopen-augmented-integral-descent

In [def-weil-derived-complete] the first triangle map is the fixed $c=(c_n)_n$. Step 5 and the product projections identify $r_ic$ with $(c_{i,n})_n$. If $K$ is complete, step 4 restricts its witnessing distinguished triangle to the required one on each component. Conversely choose the witnessing connecting map $\delta_i$ for each complete $r_iK$. The full and faithful derived equivalence of [lem-pur-finite-product-derived-tensor-calculus] gives a unique morphism $\delta:\prod_nK_n\to K[1]$ corresponding to this tuple, using the product and shift identifications. The triangle with maps $c,1-s,\delta$ corresponds to the tuple of the witnessing distinguished triangles, so is distinguished by that equivalence. This proves completeness without changing $c$ or choosing a functorial cone in the bare triangulated category.

Uses: def-weil-derived-complete, lem-pur-finite-product-derived-tensor-calculus.

### Original step 7 → lem-pur-clopen-augmented-integral-descent

For every $n\ge1$, step 5 identifies the restriction of the $n$th reduction with the $n$th component reduction. Apply [lem-pur-clopen-finite-constructibility-bounds] to these finite coefficients: constructibility and cohomological vanishing in a fixed interval are detected componentwise, as is Tor amplitude in a fixed interval. By [def-weil-derived-complete-integral-detailed], the integral constructible condition is exactly completeness, constructibility of all reductions, and one cohomological interval independent of $n$. If component $i$ has interval $[a_i,b_i]$ independent of $n$, choose $a=\min_i a_i$, $b=\max_i b_i$; this interval works on $X$ for every $n$. Any larger common interval also works. The same argument with the Tor intervals $[u_i,v_i]$ and [def-weil-finite-tor-amplitude] proves the integral $ctf$ assertion. Restricting global intervals gives the converse. The derived equivalence therefore restricts to both full subcategories: its inverse glues tuples that satisfy these conditions.

Uses: lem-pur-clopen-finite-constructibility-bounds, def-weil-derived-complete-integral-detailed, def-weil-finite-tor-amplitude.

### Original step 8 → lem-pur-clopen-completed-operation-towers

For the completed tensor of [def-pur-integral-derived-operations], choose its K-flat flat-term resolutions $P,Q$. By [lem-pur-finite-product-derived-tensor-calculus] their restrictions are such resolutions on every component, and its termwise tensor comparison identifies the reduction-level complex $P_n\otimes_{A_{E,n}}Q_n$ with the tensor of the two component reductions. On pure tensors the transition is $(p\otimes a)\otimes(q\otimes b)\mapsto(p\otimes\rho_n a)\otimes(q\otimes\rho_n b)$; restriction gives exactly this formula on $X_i$. Thus this is an isomorphism of strict towers, including all transitions and maps. Apply the natural strict-cone comparison of step 3 to obtain the completed tensor comparison; the well-defined operation of the cited definition makes it independent of the resolutions. The coefficient unit restricts to the coefficient unit since $r_iR=R_i$ with its section $1$ by [lem-pur-clopen-ringed-module-gluing]; its finite quotient units and all transitions are preserved as well. This proves preservation of the completed tensor and its coefficient units.

Uses: def-pur-integral-derived-operations, lem-pur-finite-product-derived-tensor-calculus, lem-pur-clopen-ringed-module-gluing.

### Original step 9 → lem-pur-clopen-completed-operation-towers

For $E\subset L$, use exactly the maps $\rho_m:\widehat{\mathcal O}_{E,X}\to(A_{L,m})_X$ and complexes $P_{L,m}=P\otimes_{\widehat{\mathcal O}_{E,X}}(A_{L,m})_X$ in [def-weil-integral-scalar-extension]. The coefficient identifications of [lem-pur-clopen-ringed-module-gluing] for $E$ and $L$ preserve quotient projections and the maps induced by the constant coefficient inclusion. The derived extension-of-scalars and termwise tensor comparisons of [lem-pur-finite-product-derived-tensor-calculus] consequently identify $r_iP_{L,m}$ with $(r_iP)_{L,m}$. Their pure-tensor formula sends $p\otimes a$ to $r_ip\otimes r_ia$, so commutes with the map $p\mapsto p\otimes1$ at every level and with each transition $p\otimes a\mapsto p\otimes\bar a$. Restriction of scalars here merely reads the same complex via the corresponding coefficient projection, so these comparisons also identify the strict towers of $\widehat{\mathcal O}_{L}$-modules. Step 3 for the $L$-coefficient ring gives the scalar-extension comparison. Its diagonal formula on strict tower maps, together with the well-defined scalar-extension functor in the cited definition, gives naturality on derived morphisms.

Uses: def-weil-integral-scalar-extension, lem-pur-clopen-ringed-module-gluing, lem-pur-finite-product-derived-tensor-calculus.

### Original step 10 → all three new nodes (zero categories, zero reductions/bounds, zero operations respectively)

If $I=\varnothing$, the covering hypothesis forces $X=\varnothing$. By [lem-pur-clopen-ringed-module-gluing] its module category is zero, as are its complex and derived categories. All towers, maps and Roos triangles are the zero ones. The zero object has every cohomological and Tor interval, so take $[0,0]$ when no component supplies bounds. Empty individual components contribute only zero factors and may be omitted. Thus all comparisons, completeness conditions, full-subcategory equivalences and uniform-bound assertions above include the empty partition.

Uses: lem-pur-clopen-ringed-module-gluing.

## Validation

The remote check_dag exited 0: "check_dag OK: no finding introduced by the sandbox or on its nodes". The first deliver.py --no-push rejected missing report comparisons for five additional 07KC nodes; I opened all five complete statements and added their precise differences. The repaired deliver.py --no-push exited 0 at f0e37cc8010: "preflight passed", with an OK (not pushed) receipt. The push runs the same required preflight again. Local consistency checks confirmed an unchanged item statement and statement dependencies, three unsplit nodes with empty proof lists, existing definition ids, verbatim citation quotes and verbatim preservation of all ten old proof texts. No local validator or compiler was run.
