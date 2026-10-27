# Repair report: lem-pur-system-clopen-tensor-compatibility

1. Files written:
   - dag/nodes/sec-smooth-purity/lem-pur-system-clopen-tensor-compatibility.json: unchanged statement and statement dependencies, three-step assembly.
   - lem-pur-system-tensor-presentation-identification: statement, unsplit; no Mathlib match.
   - lem-pur-system-clopen-mate-identification: statement, unsplit; no Mathlib match.
2. Attachments: none. The upstream notion/tag searches found no exact finished declaration; lean/Sheaf/Paper/SystemClopenTensorCompatibility.lean ends its theorem with sorry.
3. WANTED: none.
4. Returned fault: the 3011-character four-step proof did not spread work. The released repair note overrides its historical reviewed status. The sandbox initially contained only dispatcher brief markers, no node, report or search log, so the current read-only live node is the retained returned proof. No repository or launcher file was changed, no git command or compiler was run.
5. Unfinished: the two extracted nodes deliberately have statements only, empty proof/dependencies and status unsplit.

## Argument preservation

The tensor-presentation node carries old Step 1's identification of strict quotient transitions, ordinary unbounded system categories, exact pullbacks, derived direct images, units/counits and tensor; old Step 3's projection transpose, canonical open tensor comparisons and canonical pullback-square compositor. It states the concrete reindexing from positive levels to the zero-based vertical sequence site; it does not infer equality from evaluation.

The clopen-mate node carries old Step 2's precise B_C,b,q,s, identity/zero component projector, open-unit normalization of beta, final open/pullback compositors, equality of a with intrinsic alpha and the full unit-alpha-counit formula for gamma. Old Step 1's geometric specialization is explicit in this node. Old Step 4 is retained in assembly Step 3, with the full equation, endpoints, arbitrary unbounded inputs, before-evaluation equality and no inversion claim. Neither new node states the tensor-interchange equation. Both can be assigned independently: neither depends on the other or on the parent.

## Sources and duplicate searches

Read the current chapter and unit route, the main-20261015 prop-pur-adic-reconstruction-trace-coherence proof, and Stacks more-etale.tex lemma-shriek-proper-and-open (0F7B), sites-modules.tex lemma-j-shriek-and-tensor (0E8I), sites-cohomology.tex equation-projection-formula-map (0B56). The Stacks passages specify ordinary arrows; the comparison lemmas are agent-formulated, not asserted to be Stacks theorems about systems. SGA is unused. The unchanged parent already marks its proof agent-written.

Searched the whole DAG for clopen and system normalization/identification keywords and these source tags; searched the whole blueprint with blueprint_refs.py for clopen, semilinear tensor and proper open, and checked the ancestor. No blueprint node supplies either concrete comparison theorem. General system constructions, scalar restriction to constant towers, levelwise evaluation, and proper/open pasting are different assertions. Read all parent citations in full: lem-sf-proper-open-projection-mate, lem-coef-semilinear-derived-sections, lem-cbc-strict-tower-proper-open-calculus, lem-sf-open-tensor-normalization and def-pur-system-tensor-mate-arrows.

The new nodes each have two distinct semantic search phrasings, a valid Loogle name query, a Mathlib source grep and LeanSearch; all ran with msearch.py and are in searches.jsonl. Read the returned signatures. Inspected Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:45-64 and CategoryTheory/Adjunction/Mates.lean:70-108: these provide ordinary adjunctions and arbitrary mates, not identification of the concrete unbounded system constructions with their tensor and geometric comparisons. Other hits concerned seminorms, condensed monoidal structures, free sheaves, profinite projections or Dold-Kan. Neither node is a Mathlib leaf.

## Review by Q107

I read delivery-errors B through E and checked the repair against them. The two statements introduce their coefficient tower, sites, system objects, categories and all maps, with definition-node references and actual comparison formulas. They are statement-only, not proof sketches. The splitting is explicitly authorized by the human's repair instruction even though the old presentation marked several normalization arguments elementary: the extracted tasks are simultaneous comparisons of canonical derived presentations, rather than one equality between uninterpreted maps. No individual conclusion clause of the parent is moved out, and no new node asserts the parent interchange identity.

Step 1 uses exactly the tensor-presentation node: its comparison equivalence and operation comparisons preserve units, counits, tensor mu, projection pi, open delta and pullback compositors. This discharges the coefficient-category and arrow-normalization hypotheses of the old theorem. Step 2 uses exactly the clopen-mate node: its statement gives the same fibre product and clopen map, beta, a, and complete proper-mate gamma formula for precisely the assumed proper/quasi-compact-open square. Step 3 uses the full statement of lem-sf-proper-open-projection-mate: its final clause explicitly holds on strict semilinear quotient systems before evaluation, uses the clopen composite, and has the displayed identity with the same endpoints for arbitrary inputs. Thus no citation supplies less than the step claims. citations.json copies those actual statement paragraphs verbatim.

Checked characteristic inequality, n>=1 and the n-1 reindexing, absence of coefficient flatness, absence of a cartesian-square requirement, arbitrary unbounded H,Q and simultaneous system equality throughout. For the tensor node tested zero objects, identity morphisms, identity opens and the nonflat quotient tower Z/l^(n+1) to Z/l^n: no scalar-extension exactness or normalized-system restriction is assumed. For the clopen node tested a cartesian square (s identity, projector identity), an empty A (projector and mates zero), and a proper/open square with B_C=A disjoint union Z (projector identity on A and zero on Z); this last case retains the essential noncartesian complement rather than replacing a by a base-change isomorphism. The mate need not be inverted. The new dependency lists cite only existing construction/comparison nodes and do not reach the parent; the server DAG check will verify acyclicity.

The parent statement and statement dependencies remain byte-for-byte equal as JSON values to the live node. Historical maintainer fields and searches are retained. The old proof is preserved below to make the redistribution reviewable; no argument has been erased or blurred. No assembly step exceeds 2000 characters, and the sum is below 3000.

## Retained returned argument

Old Step 1: Work throughout in the simultaneous system categories of [lem-coef-semilinear-derived-sections]. With $R=\mathcal O_E$ and $A_{E,n}=R/\varpi_E^n$, its objects $M_{n+1}\to\operatorname{Res}_{n+1,n}M_n$ are precisely the strict semilinear systems in the statement. Thus the system version of [lem-sf-proper-open-projection-mate] uses the same $D(\mathscr S_W)$, exact system pullbacks, derived system direct images, adjunction units and counits, and system tensor. Take its four schemes to be our $A,B,C,D$, its top open $k$ to be $k_1$, and its right proper map $p$ to be $p_1$. Its geometric hypotheses are all supplied: $k_1,i$ are quasi-compact opens, $r,p_1$ are proper, and $p_1k_1=ir$. In particular its square, like ours, need not be cartesian.

Old Step 2: Check the normalization of the proper/open arrow. The fibre product and induced map in [lem-sf-proper-open-projection-mate] are exactly $B_C,b,q,s$. Its $\pi_s$ and our $\rho_s$ are the component projection of [lem-cbc-strict-tower-proper-open-calculus], identity on $s(A)$ and zero on the complementary component. Its $\beta$ and our open-base-change comparison have the same open-unit normalization of [lem-sf-open-tensor-normalization]. Consequently its $\alpha$ is exactly our $a$, including the identifications $b_!s_!\cong k_{1!}$ and $P_sP_q\cong P_r$. The system clause of the projection-mate node explicitly uses this same clopen-projection composite on the ringed diagram sites. Its mate is therefore our $\gamma$: both are the composite $R_{p_1}(k_{1!}\varepsilon_r)\,R_{p_1}(aR_r)\,\eta_{p_1}i_!R_r$. This identifies actual system transformations, without comparing finite evaluations.

Old Step 3: The projection-mate node's $\pi_{u;M,N}$ is the counit-defined map, namely the adjunct of $(\varepsilon_{u,M}\otimes1)\mu_u$, and hence is our $\pi_{u;M,N}$. Its $\delta_i,\delta_k$ are the canonical open tensor maps of [lem-sf-open-tensor-normalization], so with $k=k_1$ they are our $\delta_i,\delta_{k_1}$. The normalization node explicitly includes the ringed diagram topoi of strict coefficient systems. All these identifications use the canonical pullback comparison $P_{k_1}P_{p_1}\cong P_rP_i$ induced by the same equality $p_1k_1=ir$. Thus there is no change of coefficient category, tensor product or comparison map in applying the cited identity.

Old Step 4: Apply the final, system clause of [lem-sf-proper-open-projection-mate] to $M=H$ and $N=Q$. By Steps 1--3 its displayed identity becomes
$$\gamma_{H\otimes^LP_rP_iQ}\,i_!(\pi_{r;H,P_iQ})\,\delta_{i;R_rH,Q}
=R_{p_1}(\delta_{k_1;H,P_{p_1}Q})\,\pi_{p_1;k_{1!}H,Q}\,(\gamma_H\otimes1_Q).$$
Its source and target are exactly $i_!R_rH\otimes^LQ$ and $R_{p_1}k_{1!}(H\otimes^LP_rP_iQ)$, with the pullback identification checked in Step 3. The system clause expressly states equality before evaluation; it applies to arbitrary unbounded inputs and imposes no Tor or boundedness condition. Thus it proves the required equality in $D(\mathscr S_D)$ itself. No projection morphism or proper/open comparison is inverted.

## Not duplicates

lem-pur-system-tensor-presentation-identification vs lem-sf-etale-generic-immersion-projection: the existing node concerns Projection formula for an immersion extension by zero; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-open-reduction-adjunction-transport: the existing node concerns Open restriction and adjunction transport through actual completion units; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-semilinear-slice-scalar-generators: the existing node concerns Strict semilinear scalar comparison on extension generators; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-comparison-open-tensor-coherence: the existing node concerns Etale/pro-etale comparison respects the canonical open tensor map; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sf-open-reduction-coefficient-mate: the existing node concerns Finite coefficient reduction and the open scalar mate; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-open-tensor-support: the existing node concerns Derived tensor preserves open support in either factor; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sf-open-semilinear-tensor-model-data: the existing node concerns Simultaneous semilinear open tensor model data; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-open-pullback-support: the existing node concerns Derived pullback preserves open support; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-open-tensor-normalization: the existing node concerns Open-extension unit normalization for derived tensor and base change; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-integral-open-reduction-comparison: the existing node concerns Strict reduction and normalized realization of completed open extension; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-canonical-open-restriction-model: the existing node concerns Canonical open restriction on augmented quotient models; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-open-tensor-support-aux: the existing node concerns The open tensor projection transpose is invertible; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-open-tensor-quotient-augmentation: the existing node concerns Open reduction towers and the strict augmented tensor square; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-open-semilinear-tensor-model: the existing node concerns Simultaneous semilinear open tensor comparison on flat K-flat models; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-ringed-slice-tensor-generators: the existing node concerns Generator-normalized tensor comparison for a ringed-site slice; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-tensor-square-mate-transfer: the existing node concerns Mixed tensor-action squares transfer to counit-defined projection mates; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sf-integral-open-reduction-comparison-data: the existing node concerns Normalized integral open tensor and reduction comparison data; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sfb-ringed-projection-tensor-composition: the existing node concerns Tensor and composition coherence of ringed-topos projection maps; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sfb-internal-scalar-mate-projection: the existing node concerns Restriction of an internal coefficient mate is the specified projection map; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sfb-module-projection-section-arrows: the existing node concerns Canonical module projection mate and section comparisons; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sfb-ringed-projection-canonical-normalization: the existing node concerns Identity and composition normalization of ringed projection mates; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sfb-quotient-system-projection-lift: the existing node concerns Coefficient-system lift of the augmented ambient projection mate; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sfb-module-section-projection-arrow: the existing node concerns Canonical section projection arrow; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sfb-proetale-projection-exchange-maps: the existing node concerns Canonical projection and exchange maps on internal pro-etale modules; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sfb-ringed-projection-tensor-associativity: the existing node concerns Canonical tensor constraints and associativity for one projection mate; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sfb-integral-quotient-projection-comparison: the existing node concerns Reduction of the actual unbounded integral projection morphism; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sfb-ringed-kunneth-factorizations: the existing node concerns Two factorizations of the ringed-topos external product comparison; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sfb-module-projection-section-inverse: the existing node concerns Conditional inverse section projection composite; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sfb-ringed-projection-first-shift: the existing node concerns The ringed projection mate commutes with shifts in its direct-image input; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sfb-module-projection-section-composites: the existing node concerns Unit-normalized forward section projection composite; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sfb-ringed-projection-section-specialization: the existing node concerns Symmetry-ordered section specialization of the canonical projection mate; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-ringed-projection-mate-exact: the existing node concerns Exactness data for the ringed-topos projection mate; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-weil-pbc-projection-formula-map: the existing node concerns Projection-formula map; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-completed-target-augmentation-normalization: the existing node concerns Target projection and derived-limit comparison preserve the actual pullback completion unit; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-augmented-diagram-projection-mate: the existing node concerns Projection mate for an augmented coefficient diagram before taking inverse limit; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-formal-exact-projection-mate: the existing node concerns Formal exact projection mate for specified shift and unit data; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-ringed-projection-restriction: the existing node concerns Localization comparisons for the ringed projection mate; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-weil-pbc-four-arrows: the existing node concerns Four finite-level arrows; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-quotient-diagram-scalar-projection: the existing node concerns Strict quotient balancing preserves the diagram projection formula; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-weil-pbc-four-corners: the existing node concerns Four finite-level corners; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-signed-projection-resolution-normalization: the existing node concerns Normalized signed totalization on chosen finite-projective resolutions; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-weil-pbc-ringed-projection-restriction-data: the existing node concerns Normalized ringed projection and slice comparison data; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-finite-level-rectangle: the existing node concerns Finite-level exchange rectangle; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-ringed-slice-extension-tensor: the existing node concerns Tensor projection formula for extension by zero on a ringed-site slice; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-ringed-projection-tensor-comparison: the existing node concerns Descent and signed shifts of the normalized pro-etale tensor comparison; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-tensor-arrow-mate-right-unit: the existing node concerns Right-action evaluation of the tensor mate of an arbitrary arrow; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs new-ringed-slice-extension-tensor-hom-data: the existing node concerns Hom-equivalence data for ringed-slice tensor extension; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-tensor-arrow-mate-naturality-shifts: the existing node concerns Naturality and shifts of the tensor mate of an arbitrary arrow; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-ringed-projection-global-model: the existing node concerns Existence of the canonically normalized global projection package; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-ringed-projection-local-model: the existing node concerns Localization of a normalized global projection package; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-free-sheaf-flat: the existing node concerns The sheafified free presheaf on a representable with flat coefficients is flat (j_{X!} of a constant flat sheaf is flat); this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-derived-adjunction-shift: the existing node concerns Canonical derived ringed-topos adjunction is shift-compatible; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-weil-pbc-continuous-extension-scalar-change: the existing node concerns Ordinary scalar change commutes with continuous extension by zero; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-cbc-slice-tensor-generator-coherence: the existing node concerns Generator-normalized slice tensor isomorphisms and their strict coefficient coherence; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-asd-proper-finite-coefficient-extension-core: the existing node concerns Unbounded proper coefficient comparison and restricted projection identity; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-compact-support-proper-image-tower: the existing node concerns The proper-image reduction tower of open extension equals the compact-support tower; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-system-clopen-tensor-compatibility: the parent asserts the tensor-interchange equation; this child only identifies its category/tensor factors.

lem-pur-system-tensor-presentation-identification vs lem-pur-compact-support-scalar-projection-identification: the existing node concerns Identification of scalar projection squares through completion; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-ringed-open-total-tensor-kflat: the existing node concerns Total-tensor and K-flat representative comparison for ringed slice extension; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sp-constant-quotient-projection: the existing node concerns The canonical single-quotient reduction projection; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sp-constant-perfect-quotient-projection: the existing node concerns Perfect projection for one constant quotient; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-pur-adic-site-strict-quotient-interface: the existing node concerns Small-site adic strict quotient interface and canonical normalizations; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sp-canonical-open-scalar-tensor-models: the existing node concerns Canonical scalar tensor models compatible with open inverse image; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-finite-projection-action-laws: the existing node concerns Tensor-action and open-counit identities for finite-level projection maps; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sf-localized-strict-tensor-comparison-data: the existing node concerns Normalized cochain computation data for localized strict tensor towers; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-projection-formula-coefficient-coherence: the existing node concerns Unit and coefficient associativity of compact-support projection maps; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-fix-proetale-scalar-mate-normalization: the existing node concerns Pro-etale scalar mate restricts to the specified projection arrow; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sp-open-coefficient-adjunction-data: the existing node concerns Intrinsic open coefficient adjunction data; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-asd-open-projection-exchange: the existing node concerns Ordinary etale open tensor comparison commutes with base change; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sf-cbc-constant-perfect-projection-models: the existing node concerns Constant finite-projective models and evaluated diagram projections; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sp-open-scalar-tensor-data: the existing node concerns Open scalar tensor normalization data; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-composite-relative-tensor-action: the existing node concerns Composition preserves relative tensor-action identities; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-composite-left-projection-action: the existing node concerns Pasting two forward left-coefficient tensor actions; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-kun-constant-projection-morphism: the existing node concerns Canonical constant-coefficient derived projection morphism; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-compact-support-strict-scalar-mate: the existing node concerns Finite scalar proper/open mate on strict reduction towers; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-unit-adjunct-tensor-action: the existing node concerns Tensor action and counit equations for a unit-defined left-adjoint projection; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-pur-system-tensor-mate-arrows: that node defines a universal presentation and its arrows; this child identifies those concrete arrows with the separately stated simultaneous system constructions.

lem-pur-system-tensor-presentation-identification vs lem-sf-cbc-localized-strict-tensor-descent: the existing node concerns K-flat normalized descent of localized extension tensor comparisons to strict coefficient towers; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sp-open-projection-scalar-comparison: the existing node concerns Scalar restriction of the normalized open projection; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-quotient-diagram-projection-evaluation: the existing node concerns Finite-coefficient evaluation of the quotient-diagram projection mate; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-fix-proper-etale-origin-scalar-data: the existing node concerns Canonical scalar, tensor and direct-image comparisons at etale origins; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sp-open-scalar-coefficient-coherence: the existing node concerns Coefficient coherence of scalar pullback; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sf-localized-strict-tensor-linear-evaluation-data: the existing node concerns Normalized coefficient-linear evaluation of localized strict tensor descent; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-cbc-rational-compact-support-coefficient-coherence: the existing node concerns Coherent coefficient comparisons for rational compact-support exchange; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-perfect-quotient-exchange-normalization: the existing node concerns Perfect quotient coefficient exchange with augmentation and completion-unit normalization; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-adjoint-left-projection-action: the existing node concerns Left-coefficient counit projection: transpose, unit and associativity; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-kun-geometric-point-projection-comparison: the existing node concerns Geometric-point projection morphism agrees with the constant-section projection morphism; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-system-compactification-pf-substitution: the existing node concerns Refinement comparisons intertwine strict-system projection maps; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-cbc-completed-open-kflat: the existing node concerns Completed-coefficient open extension preserves flat-term K-flat models; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sp-constant-reduction-models: the existing node concerns Coupled universal models for strict constant-coefficient reduction; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-asd-proper-finite-coefficient-extension: the existing node concerns Canonical unbounded proper direct-image comparison for finite coefficient extension; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-open-left-projection-action: the existing node concerns Left-coefficient action laws from normalized open restriction; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-cbc-ringed-open-flat-resolution: the existing node concerns Flat resolutions under ringed slice extension; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-completed-open-tensor-system-realization: the existing node concerns Strict open-tensor systems realize the completion-unit-normalized open map; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-etale-open-derived-tensor: the existing node concerns Open extension by zero and unbounded derived tensor on ordinary etale sites; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-compact-support-scalar-shift-normalization: the existing node concerns Canonical shifts of scalar proper/open mates and scalar limit maps; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-system-projection-tensor-associativity: the existing node concerns Tensor-variable associativity of the specified system projection maps; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sp-finite-free-direct-image-coherence: the existing node concerns Coherent finite-free coefficient comparison for ambient derived direct image; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-compact-support-completed-projection-coherence: the existing node concerns Completion coherence for the integral projection mate; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-fix-etale-origin-scalar-projection-square: the existing node concerns The scalar restriction of the etale-origin projection square for a qcqs morphism; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sp-finite-free-direct-image-columns: the existing node concerns Finite-basis columns of the restricted canonical coefficient mate; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-amb-open-projection-composition: the existing node concerns Composition of the canonical derived open tensor isomorphisms; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sp-intrinsic-open-projection-invertible: the existing node concerns Intrinsic open projection inverse is invertible; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-etale-sheaf-projection-map: the existing node concerns Etale sum-extension sheaf projection formula; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pur-varying-ring-tensor-support: the existing node concerns Tensor support for canonical varying-ring extension; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs def-sp-finite-free-direct-image-data: the existing node concerns Normalized scalar models and canonical coefficient comparison data; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-sp-etale-compact-support-tor-window: the existing node concerns Open flat models and the compact-support Tor window; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-tensor-presentation-identification vs lem-pd-module-ringed-topos-derived-comparison: the existing node concerns Module-object and ringed-topos derived tensor comparison; this child compares the two concrete quotient-system presentations and their tensor/projection/open maps, without a tensor-coherence or scalar-change equation.

lem-pur-system-clopen-mate-identification vs lem-sf-ambient-clopen-restriction-uniqueness: the existing node concerns Clopen factorization and restriction uniqueness for proper/open sheaf maps; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sf-clopen-comparison-tensor-square: the existing node concerns Tensor squares for open base change and the clopen comparison; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sf-unbounded-compact-support-proper-composition: the existing node concerns Unbounded ordinary etale compact supports composed with a proper direct image; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sf-ambient-proper-open-pasting: the existing node concerns Normalized proper/open pasting on ambient pro-etale and semilinear-system categories; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sf-ambient-exact-clopen-comparison-localization: the existing node concerns Exact localization identifies the intrinsic clopen comparison and its mate; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sf-native-weil-open-proper-interchange: the existing node concerns Proper/open interchange for native bounded constructible Weil complexes; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sf-semilinear-proper-open-mate-pasting: the existing node concerns Intrinsic proper/open mates and pasting for varying coefficient systems; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-coef-semilinear-proper-open-mate: the existing node concerns Canonical semilinear proper/open adjunction mate; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sf-composition-projection-mate: the existing node concerns Normalized compact-support composition satisfies the projection mate identity; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sf-proper-open-projection-mate: that node supplies the interchange identity in its intrinsic presentation; this child identifies the parent presentation with the corresponding factors and does not reassert the identity.

lem-pur-system-clopen-mate-identification vs def-sf-semilinear-proper-open-comparisons: the existing node concerns Canonical semilinear proper/open compositors and intrinsic clopen comparison; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-sf-etale-support-compositor: the existing node concerns Canonical unbounded etale compact-support compositor; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-trf-compact-composition-proper-square-normalization: the existing node concerns Compact-support composition along a proper square: closed and open normalizations; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-trf-compact-composition-tower-formula: the existing node concerns Computing finite pro-etale compact-support composition on a compatible tower; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-trf-finite-structural-maps-commshift: the existing node concerns Canonical finite-coefficient structural maps commute with shifts; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-trf-proper-composition-site-transport: the existing node concerns Site comparison preserves compact-support composition with a proper factor; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-trf-proper-open-site-transport: the existing node concerns Site comparison preserves finite proper/open interchange; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sfb-proper-open-tower-single-unit-formula: the existing node concerns Single derived-unit formula in a proper/open tower; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sfb-proper-open-tower-successive-unit-formula: the existing node concerns Successive derived-unit formula in a proper/open tower; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sfb-proper-open-tower-derived-unit: the existing node concerns Derived-unit resolution calculation in a proper/open tower; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sfb-exact-compactification-unit-refinement: the existing node concerns Normalized exact compactification units respect canonical refinements; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sfb-exact-compactification-unit-composition: the existing node concerns Composition of normalized exact compact-support units; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-weil-pbc-etale-open-proper-interchange: the existing node concerns Open extension by zero and proper derived pushforward interchange; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-amb-unbounded-proper-open-adjunction-normalization: the existing node concerns Adjunction normalization of unbounded proper/open interchange; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-cbc-proper-open-clopen-projector: the existing node concerns Clopen lift and adjunction-normalized component projection for a proper/open square; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-pur-system-clopen-tensor-compatibility: the parent asserts the tensor-interchange equation; this child only identifies its clopen arrow and proper mate.

lem-pur-system-clopen-mate-identification vs lem-weil-pbc-proper-open-identification-unit: the existing node concerns Unit normalization of the proper/open restriction identification; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-asd-compact-support-graph-sheaf-normalization: the existing node concerns Graph comparison agrees with the canonical map into direct image; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-cbc-normalized-proper-open-pasting: the existing node concerns Horizontal pasting for fixed normalized proper/open comparisons; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-proper-open-coefficient-mate: the existing node concerns Coefficient and site squares for cartesian proper/open interchange; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-exc-proetale-finite-cd-proper-open-interchange: the existing node concerns Deriving proper/open support under all-sheaf finite cohomological dimension; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-amb-unbounded-proper-open-interchange: the existing node concerns Unbounded torsion-coefficient proper/open interchange with its canonical maps; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-asd-compact-support-graph-geometric-base-change: the existing node concerns The specified forward graph comparison at a geometric base change; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-cbc-strict-tower-composition-maps: the existing node concerns Canonical strict-tower composition comparison maps; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sf-proper-open-comparison-site-normalization: the existing node concerns Normalization of the proper/open comparison under the site comparison; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-exc-proetale-cartesian-open-injective-acyclic: the existing node concerns Proper acyclicity of injectives extended from an arbitrary Cartesian open; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-cbc-open-extended-injective-proper-acyclic: the existing node concerns Open extension of an injective sheaf is acyclic for the proper right-hand map; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-cbc-normalized-proper-open-geometric-normalization: the existing node concerns Refinement and base change for fixed normalized proper/open comparisons; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-amb-compact-support-open-source-composition: the existing node concerns Compact-support composition with a source open; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-cbc-finite-constant-coefficient-transport: the existing node concerns Normalized finite scalar and etale-origin transport to constant coefficient modules; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-asd-compact-support-finite-graph-isomorphism: the existing node concerns The specified graph comparison for finite etale morphisms; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-proetale-proper-boundary-cohomology: the existing node concerns Boundary cohomology of an open-extended pro-etale injective on a proper scheme; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-amb-shriek-open-tower-counit: the existing node concerns Open compact-support composition on the pullback tower; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-sp-varying-ring-clopen-arrow-factors: the existing node concerns Separate the cartesian lift and clopen section factors before taking mates; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-varying-ring-cartesian-lift-pullback-equivalence: the existing node concerns Cartesian clopen lifts and equivalence of varying-ring inverse image; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-sp-varying-ring-proper-open-arrows: the existing node concerns Intrinsic varying-ring clopen proper/open arrows; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-pur-system-tensor-mate-arrows: that node defines a universal presentation and its arrows; this child identifies those concrete arrows with the separately stated simultaneous system constructions.

lem-pur-system-clopen-mate-identification vs lem-cbc-complete-proetale-refinement-exchange-coherence: the existing node concerns Refinement Exchange Coherence; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-pur-compact-support-strict-scalar-refinement: the existing node concerns Scalar mate compatibility with strict compactification refinements; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-amb-unbounded-compact-support-comparisons: the existing node concerns Unbounded ordinary etale compact-support comparisons; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-finite-site-tower-paste: the existing node concerns Finite-site comparison of the proper/open compatible-tower word; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-amb-shriek-tensor-composition: the existing node concerns Tensor projection maps respect compact-support composition; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-varying-ring-clopen-arrow-evaluation: the existing node concerns Compose the separately evaluated clopen arrow factors; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-varying-ring-open-base-change-evaluation: the existing node concerns Normalized coefficient evaluation of cartesian open base change; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-asd-compact-support-graph-comparison: the existing node concerns The specified sheaf and unbounded derived graph comparison; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-proper-open-comparison-normalization: the existing node concerns Structural normalization of explicit proper/open comparison; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-asd-compact-support-graph-derived-isomorphism: the existing node concerns Invertibility of the specified graph map on unbounded complexes; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-exc-proetale-proper-open-sheaf-comparison: the existing node concerns Proper/open comparison for pro-etale module sheaves; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-exc-etale-origin-proper-open-interchange: the existing node concerns Site transport preserves the canonical Cartesian proper/open interchange; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-refinement-coefficient-mate: the existing node concerns Coefficient and site squares for the explicit refinement theta; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-amb-compactification-projection-composition: the existing node concerns Projection maps respect the explicit proper/open compactification tower; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-asd-proper-open-refinement-adjoint-projection: the existing node concerns Adjoint of the unbounded proper-open refinement comparison; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-asd-etale-compact-support-normalization: the existing node concerns Normalization of compactified etale support and its exchange; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-proper-open-tower-comparison: the existing node concerns Open-adjunction normalization of proper/open interchange on strict coefficient towers; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-cbc-strict-tower-open-extension: the existing node concerns Normalized exact open extension on strict constant-coefficient towers; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-cbc-strict-tower-proper-open-calculus: the existing node concerns Normalized proper/open calculus on strict pro-etale towers; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-varying-ring-clopen-section-evaluation: the existing node concerns Normalized coefficient evaluation of the clopen section factor; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-pur-etale-horizontal-support-tower: the existing node concerns Etale compact-support composition on a pullback compactification tower; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-varying-ring-cartesian-comparison-lift-relabelling: the existing node concerns The cartesian open comparison on varying-ring systems relabels lifts; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-cbc-etale-clopen-mate-normalization: the existing node concerns The finite etale clopen mate has the proper-support resolution normalization; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-amb-shriek-open-exchange-adjoint: the existing node concerns Open compact-support exchange is the extension-composition mate; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-asd-compact-support-graph-sheaf-normalization-transpose: the existing node concerns Transpose of graph comparison; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-asd-compact-support-graph-coherence: the existing node concerns Base-change, proper-refinement and identity equations for the graph map; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-proetale-open-injective-proper-acyclic: the existing node concerns Open-extended injectives are proper-direct-image acyclic on pro-etale sites; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-varying-ring-ordinary-clopen-evaluation: the existing node concerns Ordinary coefficient evaluation preserves the single-square clopen arrow; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-cbc-strict-constant-tower-operations: the existing node concerns Strict constant-coefficient towers and normalized inverse/direct-image operations; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs def-cbc-strict-tower-proper-open-arrows: the existing node concerns Unit-normalized proper and open arrows on strict towers; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-sp-proper-open-coefficient-mate-transposed: the existing node concerns Transposed coefficient mate identity for proper/open interchange; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-pur-etale-chart-compact-support-normalization: the existing node concerns Unbounded compact-support normalization on a closed affine chart; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

lem-pur-system-clopen-mate-identification vs lem-cbc-proper-open-interchange-coherence: the existing node concerns Proper/open interchange and its base-change and composition equations; this child compares the two concrete quotient-system presentations and their clopen alpha and proper gamma, without a pasting, evaluation or scalar-change assertion.

