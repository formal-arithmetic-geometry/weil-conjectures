# Q91 stage-1 repair report

1. Files written:
   - dag/nodes/sec-smooth-purity/lem-pur-perfect-quotient-exchange-normalization.json: existing statement, re-split into a short seven-step assembly. Statement, source, statement dependencies, blueprint ancestry and Lean record preserved. Existing Mathlib searches retained; only queries actually run were appended.
   - dag/nodes/sec-smooth-purity/lem-pur-algebra-diagram-pullback-extension-coherence.json: new statement, unsplit, no Mathlib match. Fixes the derived scalar-unit/pullback/scalar-extension square on arbitrary small algebra diagrams, before any direct-image mate.
   - dag/nodes/sec-smooth-purity/lem-pur-algebra-diagram-evaluation-adjunction-normalization.json: new statement, unsplit, no Mathlib match. Fixes evaluation of the derived adjunction and the square comparing evaluation with derived coefficient restriction, for arbitrary input arrows and small algebra diagrams.
   - citations.json: one verbatim statement quote for every citation pair. original-proof.json preserves the full original seven steps as reading material, outside the delivery node directory. searches.jsonl is the unmodified msearch log. Helper scripts stay in the sandbox.
2. Attachments: none. Searches of lean/WeilConjectures for the blueprint tag and quotient-exchange names found no declaration giving the item. The recorded Sheaf theorem at PerfectQuotientExchangeNormalization.lean:430 has sorry at line 456; it is not an attachment.
3. WANTED: none.
4. Assignment repair: at first the read clone appeared already finished at stage 1 (Q78 review), and an unchanged dry run was rejected. I then found the dedicated repair entry in coord/returns/Q91.md at head e2a95534: the newer human instruction explicitly reopens the proof, requires at least two new statement-only nodes, and caps the parent assembly at 3000 characters. This is the authorization for this re-split. No statement dispute was found. The earlier assignment-consistency report is superseded by this report.
5. Nothing remains unfinished within the authorized stage-1 split. The two new nodes deliberately have no proofs, as required for assignment to later workers; they are not claims of completed Lean proofs. No Lean file, compiler, Lake, repository write or agent delegation was used.

## Review by Q91

I read the full original item and all seven proof steps, its chapter and unit records, the current main-20261015 proof of thm-pur-rational-and-qbar-purity (Step 2, coefficient-stage independence), the unit's coefficient clause, and delivery-errors B through E. The current unit record points at a newer snapshot, but the coefficient-compatibility route and ancestry used here agree with the specified current snapshot. No chapter or unit route was changed.

For the item and both new nodes I read Stacks sites-cohomology.tex at Equation 0B56 and Tag 0944 (the actual counit-defined map and its isomorphism for arbitrary unbounded E and perfect K), 07A4 (the flat-term K-flat tensor/pullback models), 07A6 (derived adjunction), 0D6E (derived direct-image composition), 0941 (the strict-diagram model and evaluation adjoints), and 0A07 (the diagram-topos proof of direct image commuting with derived inverse limit). I also read proetale.tex at 099M/099N for the completion formula. The two new statements are explicitly marked agent-formulated intermediate consequences, not mislabeled numbered Stacks theorems. In particular neither source asserts the new combined coherence square verbatim.

The first new node carries the previously inline identification of two differently constructed derived maps: the scalar-unit comparison followed by scalar-extension pullback, and the ordinary ambient tensor pullback. Its normalization is on simultaneous flat-term K-flat representatives, so it asserts equality after canonical localization, not an equality of arbitrarily chosen object isomorphisms. On an A-K-flat representative P, scalar extension P tensor B is B-K-flat; under the cartesian ring identification the comparison is induced by inserting one and multiplying scalars. The degreewise association commutes with all diagram structure maps, and the two localization comparison squares must agree. The ordinary chain-level equations in lem-pur-cochain-pullback-tensor-coherence supply the model, but do not themselves state this derived restriction square. This is a derived normalization task, not a separate restatement of d U(h)=hA.

The second new node carries the previously implicit comparison of whole derived adjunctions with coefficient evaluation. It quantifies over all M,N,t on a small algebra diagram and has no h_F or projection formula in its conclusion. Its content is the existence and normalization of beta_j, the counit equation, and the compatibility of beta_j with the two derived restriction comparisons. An ordinary varying-ring evaluation need not preserve K-injectives, and that is not assumed. A proof can construct the derived left extension at j with component at k the coproduct over arrows j to k of B_k tensor over B_j with the input, compare these left extensions under exact geometric inverse image using K-flat scalar association, and pass to right adjoints. The common derived-composition normalization is required for the d square. This construction is substantial and independent of the first node; it is not an elementary assertion that ordinary functor-category evaluation has an adjoint.

For every step I opened the complete cited statements, not their proofs:

- Step 1 uses the constant-module inverse-image isomorphism natural in coefficient maps to identify B_X with u^{-1}B_Y; diagram-ring-restriction-pushforward supplies the specified d. The new pullback-extension node supplies b. Ringed-coefficient-restriction-counit states precisely U(epsilon_B)b = epsilon_A G(d). Precomposing with G U(t), applying naturality of b, and substituting the counit transpose proves the displayed arbitrary-t transpose formula. Small diagram sites meet each cited smallness hypothesis.
- Step 2 uses the first new node to identify U(c)b with theta. I additionally cited reduction-pullback-derived-tower, whose statement uniquely characterizes tau by the same flat-term K-flat model; this explicitly ties theta on a constant input to the augmented lemma's tau. Constant-tower-pushforward-normalization states epsilon^J G(chi) = Delta(epsilon). Augmented-diagram-projection-mate states the transpose of hA using exactly that tau. Thus both transposes coincide, and the adjunction bijection gives equality in the strict derived category before evaluation. No conservativity of evaluation is being used for equality of morphisms.
- Step 3 uses the new evaluation node's counit/transpose equation and its delta ev(d) = d_j U(beta) square. Taking M = R_Y PF and N = R_X F identifies the evaluated h with the actual quotient-linear adjunction mate; scalar extension and evaluation give exactly the displayed finite source and target. By Step 2 the restricted map is ev(hA), and augmented-diagram-projection-mate identifies it with the ordinary counit-tensor projection. I retained the original quotient-diagram-projection-evaluation citation with H=F and K=underline A to supply the finite source/target identifications; ringed-projection-mate-exact explicitly supplies the tensor-unit identities. The new general evaluation lemma supplies the additional d/evaluation/restriction square. No componentwise K-injectivity or faithful evaluation is presumed.
- Step 4 retains the actual elementary argument: finite generators give a finite free surjection, the projective-module lifting characterization splits it, exact constant realization sends the representing quasi-isomorphism and splitting to sheaves, and strict-perfect-coefficient-package identifies the finite free constants. All four cited statements say precisely those facts. No node is added merely for a finite-projective splitting, and no uniform bound is inserted.
- Step 5 uses the full small-ringed-site perfect projection formula, whose statement allows unbounded F and needs only perfectness of the target coefficient, now supplied by Step 4. Constant-module inverse image identifies the pulled-back quotient. Levelwise-abelian-towers and exact-functor-complex-cohomology jointly say every cohomology map of hA is invertible; unbounded-derived-iso-cohomology then says hA is invertible. Strict-quotient-diagonal-normalization (1) explicitly says U is exact and conservative on derived categories, so Step 2 yields invertibility of h. Quotient evaluation preserves the resulting inverse. These arguments remain in the parent as the short assembly of existing nodes; no duplicate of the already-existing strict-perfect-tower-projection is created.
- Step 6 is exactly the strict augmentation equation of augmented-diagram-projection-mate, applied to the actual algebra quotient tower. It is already stated before inverse limit, with no perfectness or completeness assumption.
- Step 7 uses diagonal-normalization (4), eta = L(i) ell^{-1}, and the natural a from tower-pushforward-limit-comparison. Naturality first moves L P^J(i) past a^{-1}; the remaining factor a_{Delta F}^{-1} L(chi) ell^{-1} is P(ell^{-1}) by constant-tower-pushforward-normalization. I checked the order and domains of these factors and retained the full displayed calculation. No abstract uniqueness of object isomorphisms replaces equality of the specified maps.

I preserved all original work: old Steps 1-2 are now factored through the derived pullback-extension square, old Step 3 through evaluation/counit/restriction coherence, old Step 4 still displays the actual splitting and constant realization, and old Steps 5-7 still use their same cohomology, strict augmentation and normalized-limit arguments. The short formula manipulations after cited statements are elementary; the two new statement-only coherence tasks contain neither perfect-projection invertibility nor the completion-unit assertion, so neither is a renamed clause or the entire item. They are of comparable scale (roughly 2.5k and 3k characters of self-contained statement) and can be handled independently.

I tested A=0; I=A (all quotient modules zero, unique zero exchange); I=0 (identity scalar extensions and constant towers); A=Z,I=(p) (nonflat quotient maps); and A=k[t],I=(t), with k infinite (quotients perfect over A but not finite as sets). The arguments permit F unbounded or not complete and unrelated resolution bounds at different n. For the new general statements, u=id makes both coherence squares ordinary scalar association and evaluation, the one-object identity category reduces them to the ambient coefficient adjunction, and the empty J has the unique zero diagram and vacuous evaluations. No finiteness of quotients, coefficient flatness, scheme presentation or SGA source is used.

All new-node Mathlib searches were actually run with msearch.py and read. Both nodes have LeanFinder in two phrasings, Loogle, LeanSearch and grep. For the first node, ordinary SheafOfModules.pullbackComp and conjugateEquiv_pullbackComp_inv (PullbackContinuous.lean:167,177), pullbackIso, and ordinary algebra tensor cancellation do not assert the unbounded derived scalar restriction/tensor square. For the second, evaluationAdjunctionRight (Adjunction/Evaluation.lean:54) and its counit describe an ordinary constant-category functor category, not varying ring-module diagrams, their derived direct images or the two restriction comparisons. SheafOfModules.evaluation is site-object sections, not ring-diagram evaluation. I read the ordinary sheaf counit at PushforwardContinuous.lean:303: it is not the item or either new node. No Mathlib leaf was found. No search was invented or changed from an unavailable result into no match.

Blueprint searches run: quotient exchange, perfect coefficient, completion unit, projection formula, scalar extension, strict diagram, augmentation, pullback scalar, evaluation adjunction. The item and both new nodes have same_as=[], since no imported blueprint statement matches their full assertions. Their from.place points at the original Qbar coefficient-independence clause and explicitly records which old normalization steps are extracted. The two existing off-unit tools remain the previously accepted perfect projection formula and geometric inverse image of constants; their roles and the route are unchanged.

## Not duplicates

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-pe-constructible-comparison-tensor-test-reflection: The existing assertion reflects vanishing of tensor-test homology across the etale/pro-etale comparison; the new assertion identifies derived scalar-restriction and tensor-pullback maps on arbitrary algebra diagrams.

lem-pur-algebra-diagram-pullback-extension-coherence vs def-sf-point-fibre-tensor-common-stage: The existing definition fixes common finite-field coefficient-stage point tensorators; the new theorem is a derived algebra-diagram pullback/restriction square without Frobenius or point fibres.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-weil-pbc-ringed-slice-normalized-comparisons: The existing theorem constructs slice tensor/Hom/Koszul data; the new theorem compares change of scalar rings with inverse image and restriction on whole diagram sites.

lem-pur-algebra-diagram-pullback-extension-coherence vs def-sf-finite-open-tensor-operations: The existing definition fixes finite-coefficient scheme/open operations and maps; the new theorem proves a normalized derived scalar-extension square for arbitrary small algebra diagrams.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-derived-right-exact-tensor-comparison: The existing theorem gives the tensorator of one derived strong monoidal functor; the new theorem equates two paths that also involve coefficient restriction and its scalar unit.

lem-pur-algebra-diagram-pullback-extension-coherence vs def-coef-semilinear-derived-calculus: The existing node defines an interface assuming normalized calculus; the new theorem asserts an actual coherence equation between constructed functors.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-sf-point-integral-completed-tensor-comparisons: The existing theorem concerns point sections and completed finite-field integral coefficients; the new theorem is ordinary unbounded cartesian algebra-diagram pullback coherence.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-sf-completed-tensor-rational-naturality: The existing theorem extends linear reflector/tensor comparisons through localization at p; the new theorem concerns derived change of coefficient rings and exact inverse image before completion or scalar localization.

lem-pur-algebra-diagram-pullback-extension-coherence vs def-coef-semilinear-geometry-derived: The existing node defines normalized geometric-interface data, including assumed evaluation equations; the new theorem supplies a derived scalar-restriction coherence equation without assuming that interface.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-sf-ringed-finite-free-tensor-complex: The existing theorem gives an ordinary change-of-rings chain tensor isomorphism and K-flat preservation, explicitly no derived comparison; the new theorem compares canonical derived inverse-image/scalar-extension and restriction paths.

lem-pur-algebra-diagram-pullback-extension-coherence vs def-sf-point-fibre-tensor-rational-compatibility: The existing definition fixes rational point tensor and coefficient-stage squares; the new theorem is arbitrary small-site derived scalar-extension/pullback coherence.

lem-pur-algebra-diagram-pullback-extension-coherence vs def-sf-point-evaluation-tensor-coherence: The existing definition specifies associativity/symmetry/unit equations for point sections; the new theorem supplies the scalar-restriction/pullback square in derived algebra diagrams.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-pur-perfect-quotient-exchange-normalization: The item proves projection-exchange isomorphisms and a completion-unit equation for perfect adic quotients. The new node instead normalizes evaluation of an arbitrary derived adjunction arrow and two coefficient-restriction paths for all small algebra diagrams; it has no exchange isomorphism or completion conclusion.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-sbc-derived-restriction-zero-transport: The existing theorem is an H^0 restriction/single-comparison identity for etale schemes; the new theorem is a full unbounded adjunction/evaluation/restriction square for semilinear ring diagrams.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-sbc-restricted-derived-section-zero-comparison: The existing theorem compares degree-zero restricted section pullback with ordinary sections on a scheme square; the new theorem concerns evaluation at an algebra-diagram index and its full derived counit.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-sbc-derived-section-pullback-zero: The existing theorem identifies H^0 of derived section pullback on a sheaf in degree zero; the new theorem is a full adjunction and coefficient-restriction comparison for arbitrary unbounded diagram objects.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-sbc-derived-section-single-unit: The existing theorem compares derived section units on single-object complexes on schemes; the new theorem compares diagram evaluation counits and derived restriction compositions on arbitrary objects.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-sbc-restricted-derived-section-shift-comparison: The existing theorem computes shifted restricted scheme cohomology pullback; the new theorem evaluates whole unbounded ring-diagram adjunctions and compares coefficient restriction paths.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-sbc-restricted-derived-sections-single: The existing theorem identifies one restricted section morphism on sheaves in degree zero; the new theorem normalizes arbitrary adjunction transposes in derived semilinear diagram categories.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-sbc-restricted-derived-evaluation-pullback: The existing theorem is a commutative H^p scheme restricted-cohomology square; the new theorem is a pre-cohomology evaluation/direct-image/restriction comparison at arbitrary ring-diagram indices.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-sbc-restricted-derived-sections-shift-transport: The existing theorem concerns shifts of restricted scheme derived sections; the new theorem concerns full varying-ring diagram adjunctions and scalar restriction, with no shift-specific assertion.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-coef-enriched-sequence-projection-formula: The existing theorem computes finite projections of an enriched internal-Hom sequence adjunction on normalized systems; the new theorem compares arbitrary geometric diagram adjunctions with evaluation and scalar restriction, without internal Hom or normalized systems.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-coef-scalar-hom-zero-compatibility: The existing theorem identifies H^0 of a scalar internal-Hom comparison; the new theorem identifies entire derived geometric adjunction counits and evaluation/restriction paths.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs def-coef-compact-support-tensor-comparison: The existing definition specifies tensor presentations and compact-support coefficient arrows; the new theorem is a geometric diagram evaluation-adjunction coherence result without compact supports.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-pur-cochain-pullback-tensor-coherence: the existing node states equations of ordinary chain maps; the new node asserts the specified equality after derived scalar extension, inverse image, and coefficient restriction on an entire small diagram. It cites the existing chain model instead of copying it as a proof.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-sfb-ringed-comparison-tensor-adjunction: the existing theorem compares derived pullback paths monoidally and their conjugate right adjoints; it does not state the square with a scalar restriction functor U and scalar-extension unit.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-pur-quotient-diagram-projection-evaluation: the existing theorem evaluates a particular quotient projection composite pi(h tensor 1) for an adic quotient sequence. The new theorem supplies arbitrary-arrow adjunction transposes and the two-path d/ev square for arbitrary algebra diagrams, with no perfectness, projection or adic hypothesis.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-weil-pbc-tower-derived-evaluation-normalization: the existing theorem evaluates constant-abelian-category towers for a fixed exact left adjoint. The new theorem works with varying ring coefficients, where evaluation need not preserve K-injectives, and adds the compatibility with derived coefficient-restriction composition.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-pur-diagram-ring-restriction-pushforward: the existing node constructs d before evaluation; the new node normalizes its comparison with beta_j and d_j after evaluation, including the counit.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-pur-ringed-coefficient-restriction-counit: the existing node fixes the coefficient-restriction counit for one ringed site; the new node supplies evaluation of the entire algebra-diagram adjunction and the derived evaluation/restriction square.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-coef-sequence-global-sections-evaluation: the existing theorem gives evaluated global sections of inverse sequences after scalar restriction; the new theorem treats arbitrary geometric direct image and quotient-coefficient adjunction transposes, and the compatibility of its two restriction comparisons.

Additional same-tag comparisons reported by the live delivery tree (all statements opened in full):

lem-pur-algebra-diagram-pullback-extension-coherence vs def-pd-section-derived-realization: This defines a condensed-module/section-module derived realization on scheme pro-etale sites, without proving comparison compatibility; the new theorem asserts coherence of actual functors on arbitrary algebra diagrams.

lem-pur-algebra-diagram-pullback-extension-coherence vs def-pd-section-derived-tensor-data: This defines derived operations transported across the internal-module/section-module equivalence; the new theorem concerns changing coefficient rings on small diagram sites, not that equivalence.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-pd-module-ringed-topos-derived-comparison: This compares internal condensed-module objects with section-ring modules for schemes; the new theorem concerns diagram coefficient extension/restriction and index evaluation for already fixed ordinary module sheaves.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-pd-section-derived-tensor-normalization: This compares internal and section-module tensor structures for condensed coefficients on schemes; the new theorem equates scalar-restriction/pullback and ambient tensor paths on arbitrary algebra diagrams.

lem-pur-algebra-diagram-pullback-extension-coherence vs def-weil-pbc-normalized-origin-scalar-comparisons: This defines adic quotient scalar compositors as adjunction conjugates on a fixed site; the new theorem compares scalar extension with geometric inverse image and restriction, without an adic datum.

lem-pur-algebra-diagram-pullback-extension-coherence vs def-weil-pbc-ringed-projection-restriction-data: This defines data and the ProjectionCompatible predicate for localization to a site slice; the new theorem is an assertion about actual algebra-diagram scalar-extension/pullback comparisons.

lem-pur-algebra-diagram-pullback-extension-coherence vs def-weil-pbc-ringed-tensor-square-presentation: This defines ringed square presentation data, explicitly with no derived-square tensor coherence as data; the new theorem asserts a particular derived coherence square with scalar restriction and units.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-weil-pbc-augmented-cech-tensor-pullback: This compares pullback of augmented local Cech tensor actions; the new theorem compares scalar restriction with pullback/scalar-extension on arbitrary strict algebra diagrams, without ideals or Cech complexes.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-weil-pbc-augmented-diagram-projection-mate: This constructs an ambient constant-ring tower projection mate and proves its augmentation equation; the new theorem instead identifies the two left-side scalar-extension/restriction tensor comparisons before making any projection mate.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-weil-pbc-cochain-pullback-tensor-shift: This proves signed shift compatibility of a prescribed cochain tensor comparison; the new theorem compares two constructed derived coefficient-change paths including scalar units.

lem-pur-algebra-diagram-pullback-extension-coherence vs lem-weil-pbc-constant-derived-normalization-universal: This proves universality of constant realization of a scalar universal arrow; the new theorem equates pullback/scalar-extension with its ambient derived tensor comparison on arbitrary algebra diagrams.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs def-pd-section-derived-realization: This defines a condensed-module/section-module derived realization on scheme pro-etale sites, without proving comparison compatibility; the new theorem asserts coherence of actual functors on arbitrary algebra diagrams.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs def-pd-section-derived-tensor-data: This defines derived operations transported across the internal-module/section-module equivalence; the new theorem concerns changing coefficient rings on small diagram sites, not that equivalence.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-pd-module-ringed-topos-derived-comparison: This compares internal condensed-module objects with section-ring modules for schemes; the new theorem concerns diagram coefficient extension/restriction and index evaluation for already fixed ordinary module sheaves.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-pd-section-derived-pushpull-normalization: This transports scheme pro-etale adjunctions across the internal-to-section equivalence, whereas the new theorem evaluates varying-ring diagram adjunctions and compares their coefficient restrictions.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs def-pbc-successive-derived-scalar-normalization-data: This defines assumed successive scalar-extension normalization data and explicitly asserts no existence; the new theorem constructs geometric diagram evaluation comparisons and states their counit/restriction equations.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs def-weil-pbc-derived-direct-image-composition: This defines composition of bounded-below abelian etale scheme direct images; the new theorem asserts evaluation comparisons for arbitrary unbounded varying-ring module diagrams.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs def-weil-pbc-derived-normalization-arrows: This defines constant-sheaf scalar normalization and an underived pullback/restriction mate; the new theorem asserts full derived algebra-diagram evaluation, counit, and restriction compatibility.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs def-weil-pbc-ringed-slice-derived-data: This packages assumed derived functors and slice comparison equations; the new theorem proves existence and normalization of evaluation comparisons for a varying algebra diagram.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs def-weil-pbc-successive-derived-quotient-data: This defines assumed successive coefficient extension normalizations; the new theorem provides geometric index-evaluation adjunction and restriction equations, with no chosen normalization data as hypotheses.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-pbc-normalized-derived-adjunction-transport: This transports derived scalar adjunctions along additive equivalences; varying-ring diagram evaluation is not an equivalence, and the new theorem supplies its derived geometric direct-image comparison and restriction square.

lem-pur-algebra-diagram-evaluation-adjunction-normalization vs lem-weil-pbc-cohomology-pullback-derived-unit: This computes bounded-below etale scheme section pullback by a derived unit and Leray; the new theorem compares varying-ring diagram adjunctions before taking cohomology or sections.


Final citation audit correction: Step 3 now explicitly retains the original tensor-unit specialization and its tensor-unit identity citation. This avoids taking the scalar-extension/evaluation object identification from the new adjunction lemma, which does not itself state a tensor comparison. The first complete delivery dry run passed at 3b8ac57a539; the final dry run is rerun after this citation correction before pushing.
