# Repair of det-lem-int-tensor-product (Q53, 2026-10-22)

## Files written

- `dag/nodes/sec-six-functors-basics/det-lem-int-tensor-product.json`: statement unchanged verbatim; split into three assembly steps, 2359 characters in total.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-free-dual-chain-comparison.json`: statement, unsplit; no Mathlib match. Native scalar-free chart calculation and its actual derived evaluation normalization.
- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-derived-closed-localization.json`: statement, unsplit; no Mathlib match. Internal/sectionwise closed derived transport, slice comparison and the global evaluation isomorphism for local scalar-free models.
- `dag/nodes/sec-six-functors-basics/lem-sfb-evaluation-duality-completion.json`: statement, unsplit; no Mathlib match. Both specified duality triangles and the canonical product, tower and augmented completion comparisons.
- `dag/nodes/sec-six-functors-basics/lem-sfb-field-bounded-constructible-tensor.json`: statement, unsplit; no Mathlib match. Constant-field sheaf tensor models and bounded constructible closure with interval bounds.

The four new nodes have empty proof/proof_deps, null proof_origin and status unsplit. Their statements introduce their own objects. No Lean file, definition, target statement, chapter or unit record is changed. `citations.json` contains the verbatim statements supporting every citation in every parent step. Research files stay in the sandbox.

## Attachments

None. I searched the actual WeilConjectures source for the blueprint id and tensor/completeness notions, and for all four proposed ids. No finished project declaration states the whole item. `AlgebraicGeometry.ProEtale.integralTensorProduct` in `lean/Sheaf/Paper/IntegralTensorProduct.lean:237` ends in `sorry`. The helper left-adjoint instance is not an attachment for either clause. The item's existing Lean records are retained for the maintainer; no compiler was run.

## WANTED

None. The main-20261015 blueprint, Stacks source and relevant existing DAG statements are available locally. This is an agent-written extraction of the previously reviewed proof, not a claim that the blueprint was a human proof.

## Faults and changes

The return asks for distributed work rather than a shorter paraphrase of the old proof. The sandbox was actually empty at launch. I copied the current read-only live node, which contains exactly the returned eleven-step 12577-character argument, its prior search records, citations in the step uses, source references and review metadata. No prior sandbox report or searches.jsonl was present to reuse. The current live node is the baseline: its statement, statement dependencies, Lean information, blueprint snapshot/flags, earlier Mathlib searches and maintainer metadata are preserved. The delivery tool will overlay the current server baseline again.

The two blueprint source mistakes already identified in the prior review remain repaired: evaluation to the unit is not generally an isomorphism (rank two over a nonzero field gives a map from rank four to rank one); and equality of morphisms in a derived category cannot generally be checked on a cover. The extraction asks for local invertibility of the canonical comparison, then global duality identities through the closed adjunction. It never descends equality of derived maps. The non-existent sk-prop-integral-criterion remains replaced by actual criterion (2) of sk-lem-integral-models. Its tensor-closure clause (3) is not invoked.

An initial generic chart statement overlapped fine-grained ringed-site lemmas found by the tag scan. Before delivery I refined it to include the native internal scalar model, strict signed chart formula and its identification with the actual native derived closed adjunction. Similarly the transport node includes the global comparison for arbitrary unbounded targets, not only the already existing sectionwise internal-Hom isomorphism. The existing general ringed-site calculations are inputs available to the future workers, not new copies of those statements.

## Unfinished work

The four extracted nodes are deliberately not proved or split: they are separate queue items for other workers. The item itself has a complete assembly proof. No mathematical argument of the returned proof has been discarded: the exact old text, dependencies and source places are retained below, assigned to the four new work items or to the short assembly where the old step only applies existing same-unit statements. This preserves the detailed sign calculation, global adjunction proof, canonical completion-map identification, field sheafification argument and the two finite truncation inductions.

## Review by Q53

I read the chapter sec-six-functors-basics and all four unit steps of sk-lem-int-tensor, then the main-20261015 item statement and all three paragraphs of its proof. The route is still unit step 3: local duality, finite extension devissage along strata, residue-field closure and the integral recognition criterion. The item is a detail node, not the key statement of the unit, so I do not change the unit's realization fields.

For the chart node I read Stacks sites-cohomology.tex, Tag 08JH (lemma-Rhom-strictly-perfect) and Tag 08JJ (lemma-dual-perfect-complex), particularly the arbitrary unbounded target and the final finite-free calculation. I checked def-pur-hom-complex and def-pc-tensor-complex-sheaves: on degrees (a,b) the second differential sign is (-1)^(a+b+1), matching -(-1)^(a+b) in Hom. The displayed inverse is the finite-basis identity; it includes the zero complex and rank zero. The native scalar extension of a finite free A-module is finite free over R_S without any flatness assumption on R_S over the constant A sheaf. The extra native normalization is an equality of the canonical evaluation transpose after section-action transport; a mere abstract isomorphism of objects would not suffice.

For the transport/localization node I read Stacks Tag 08JB (lemma-restriction-RHom-to-U), the actual statements of def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-pe-internal-section-tensor-comparison, lem-sfb-module-object-ringed-site-derived-comparison, lem-weil-proetale-weakly-etale-localization, lem-pur-site-restriction-module-adjunction-exact and lem-weil-pbc-unbounded-derived-iso-cohomology. The ring identifications on charts are explicitly a hypothesis for a general condensed coefficient, rather than an unsupported appeal to the admissible-coefficient theorem for all condensed rings. For the parent specialization to integral coefficients, clause (1) of sk-prop-sfb-cartesian-coefficients does provide exactly this hypothesis on arbitrary schemes, without the invertibility hypotheses of its Tate-twist assertion. Bounds and ranks may vary by chart; the node makes no global boundedness or Noetherian assertion. Invertibility is detected by restrictions of kernels and cokernels of cohomology maps, never by local faithfulness on all derived Hom sets.

For the duality/completion node I read Stacks Tag 0FPU (example-dual-derived) and the source's first paragraph. The source omits the triangle verification; the complete original global adjunction argument is preserved in the assigned old steps below. I also read the existing evaluation-dual criterion and lem-pc-homotopy-limit-map. The first proves only the dual pair, whereas the extracted task also identifies the actual tensor/limit comparison with the augmented completion map. There is no claim that tensor preserves arbitrary ordinary inverse limits by exactness alone. Products follow from the right adjunction; sequential homotopy limits use exactness and the Roos triangle. Associativity is required to commute with every B_(n+1) -> B_n and the augmentations, so the conclusion is about the canonical map eta, not an arbitrary isomorphism to a completion. The B_n version works for the actual finite coefficient sheaves without silently identifying completed R_S with a constant valuation-ring sheaf. Empty product and zero M cases give the zero functor and the same identities.

For the field-closure node I read the third source paragraph and Stacks sites-modules.tex Tag 03ET (lemma-flatness-sheafification). I read the statements of lem-pc-sites-modules-sheafification-flat, lem-exc-constant-field-module-flat, lemma-constructible-pullback-stratification, sk-def-sfb-constructible and the truncation triangle input. All constant-field module sheaves are flat by the existing general result (the original sheafification proof remains below). Common strata are scheme fibre products, not unjustified set-theoretic factorization of morphisms. Intersections are constructible since S is Noetherian; common covers come from base change and the covering axiom. Finite-dimensional field models give rank rs, including rank zero and empty strata. In the bounded derived assertion one inducts separately over both finite cohomology intervals; a tensor of shifted sheaves is in degree i+j, so the interval is [a+c,b+d]. No Tor-amplitude conclusion over a non-field residue ring is used.

Parent step 1 cites the chart and transport statements for the actual evaluation map and its global invertibility; their statements explicitly allow every unbounded N and arbitrary S. The Cartesian coefficient citation supplies exactly the chart-ring hypothesis, and the duality/completion citation states both triangles, products, sequential cones and canonical completion compatibility. These are all the facts used by that step. The two newly extracted statements with overlapping ingredients still carry different tasks: one fixes the strict scalar chart map, the other proves the internal transport and global assertion on an arbitrary covered scheme.

Parent step 2 uses the transport node's exactness assertion and only triangulatedness clause (1) of sk-lem-int-integral-heart. I opened det-lem-int-tensor-shriek: its clause (2) gives exactly the finite extension generators a_!M with M integral bounded constructible and the scalar-free local models; clause (1) preserves membership under a_!. I opened det-lem-int-tensor-projection: it gives the displayed isomorphism for arbitrary ambient complexes and these actual coefficients. A stratum of a standing scheme is again a separated finite-type k-scheme, so all standing hypotheses needed in step 3 still hold.

Parent step 3 uses clause (1) of det-lem-int-tensor-pullback, then precisely criterion (2) of sk-lem-integral-models for both factors. I opened lem-weil-pbc-ringed-topoi-derived-tensor-pullback: it allows an arbitrary morphism of ringed topoi and arbitrary unbounded inputs; the identity topos and quotient ring map are therefore allowed, without a flat quotient hypothesis. The resulting scalar-extension isomorphism has exactly the residue-field tensor on the right. The field node gives bounded constructibility, and sk-thm-pe-constructible-comparison applies to discrete Noetherian kappa and qcqs S and supplies etale origin of the entire derived object. Thus both sides of the iff criterion are verified. Extension by zero and the finite extension construction are already supplied by step 2. There is no use of the criterion's own closure clause.

The source's notation for inverse limits is interpreted as sequential towers exactly as in the retained statement and earlier review. I compared this with the existing Lean statement in Sheaf.Paper.IntegralTensorProduct: it has the same two clauses, including all products, sequential homotopy-limit cones and IsDerivedComplete. It remains sorried, so no attachment replaces the split.

I checked delivery-errors B--E against the files: statement-only children, explicit objects/hypotheses and definitions, real search records, exact quotation citations, no source-route change, no new axiom or hollow construction, no node restating either complete parent clause. All nontrivial old local arguments are assigned below. The three parent texts are each below 2000 characters, their sum below 3000. The four children have comparable arguments to formalize: 1389, 2951, 2281 and 3589 old proof characters respectively, rather than concentrating the whole proof in one child.

## Mathlib and blueprint searches

Each new node has actual leanfinder, loogle, grep and leansearch runs, with a second semantic phrasing, recorded by msearch.py in searches.jsonl. After changing the native chart/transport search questions I ran fresh searches for those versions as well. All services answered; no failed service is labelled absence. The full responses are in the node records. I read the significant candidate sources: LinearAlgebra/Contraction.lean:170 (dualTensorHomEquivOfBasis), Algebra/Homology/Monoidal.lean:48 (tensorObj), CategoryTheory/Monoidal/Rigid/Basic.lean:77 and :410 (ExactPairing and tensorRightHomEquiv), and Condensed/Light/Monoidal.lean (underived light-condensed closed structures). None states any whole new node or a one-line specialization of it. Ordinary module tensor-Hom equivalences omit the sheaf-complex differential and derived-map normalization; the rigid bijections assume the dual pair; underived light-condensed structures omit the unbounded pro-etale derived assertions. No new Mathlib leaf is claimed.

I searched the whole imported blueprint with tools/blueprint_refs.py search for tensor, dualiz, residue field, finite-free dual, constant field, tensor closure, internal-module, completion, evaluation and finite free scalar, and searched parsed statements/titles throughout dag/nodes for the corresponding notions and tags. The nearest ancestor command returns det-lem-int-tensor-product itself. The child from.place fields name the source paragraph and old step. No blueprint node states any complete new native-model/augmented-completion/field-closure statement; same_as stays []. The already existing broad ringed-site, coefficient-stage and flatness lemmas are distinguished below rather than recreated as individual new flatness or abstract perfect-duality lemmas.

## Not duplicates

lem-sfb-evaluation-duality-completion vs det-lem-int-integral-heart-dualizable: the new task includes both duality identities and the comparison intertwining the actual coaugmentation for arbitrary algebra towers on ringed sites, for every target; the existing statement does not give this augmented completion comparison. Existing task: Local duals of integral constructible sheaves.

lem-sfb-evaluation-duality-completion vs lem-fix-closed-evaluation-dual-criterion: the new task includes both duality identities and the comparison intertwining the actual coaugmentation for arbitrary algebra towers on ringed sites, for every target; the existing statement does not give this augmented completion comparison. Existing task: Evaluation-isomorphism criterion for a dual pair in a closed monoidal category.

lem-sfb-evaluation-duality-completion vs lem-sf-perfect-tensor-roos-completion: the new task includes both duality identities and the comparison intertwining the actual coaugmentation for arbitrary algebra towers on ringed sites, for every target; the existing statement does not give this augmented completion comparison. Existing task: Perfect tensor quotient coaugmentation and its completion diagrams.

lem-sfb-evaluation-duality-completion vs lem-zl-dualizable-jointly-conservative-locality: the new task includes both duality identities and the comparison intertwining the actual coaugmentation for arbitrary algebra towers on ringed sites, for every target; the existing statement does not give this augmented completion comparison. Existing task: Dualizability detected by jointly conservative closed monoidal functors.

lem-sfb-field-bounded-constructible-tensor vs lem-exc-constant-field-module-flat: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: All modules over a constant field sheaf are flat.

lem-sfb-field-bounded-constructible-tensor vs lem-exc-constant-field-sheaf-tensor-cohomology: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: Tensoring over a constant field sheaf commutes with cohomology.

lem-sfb-field-bounded-constructible-tensor vs lem-fd-flat-constructible-tensor: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: Tensor with a flat constructible étale sheaf preserves bounded constructibility.

lem-sfb-field-bounded-constructible-tensor vs lem-pc-sites-modules-functorial-flat-cover: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: Functorial flat cover of a module sheaf.

lem-sfb-field-bounded-constructible-tensor vs lem-pc-sites-modules-sheafification-flat: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: Sheafification preserves flatness of module presheaves.

lem-sfb-field-bounded-constructible-tensor vs lem-pur-finite-tensor-constructible-cohomology: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: Finite-level derived tensor has constructible cohomology without a boundedness claim.

lem-sfb-field-bounded-constructible-tensor vs lem-sfb-constant-module-flat: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: Constant realization preserves flat modules.

lem-sfb-field-bounded-constructible-tensor vs lem-sfb-derived-scalar-localization-reflection: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: Derived scalar localization is reflective with its normalized unit.

lem-sfb-field-bounded-constructible-tensor vs lem-sfb-locally-closed-generator-tensor-intersection: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: Tensor comparison for locally closed finite-free generators.

lem-sfb-field-bounded-constructible-tensor vs lem-sfb-scalar-hom-telescope-evaluation: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: Scalar localization internal-Hom comparison with every telescope leg and evaluation.

lem-sfb-field-bounded-constructible-tensor vs lem-weil-pbc-free-sheaf-flat: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: The sheafified free presheaf on a representable with flat coefficients is flat (j_{X!} of a constant flat sheaf is flat).

lem-sfb-field-bounded-constructible-tensor vs lem-weil-pbc-scalar-localization-sheaf-exact: the new task is pro-etale tensor closure of two bounded constructible constant-field complexes, with sum-of-interval bounds and finite-stratum models; the existing statement does not assert this result. Existing task: Exactness of actual scalar localization on module sheaves.

lem-sfb-finite-free-dual-chain-comparison vs lem-fix-ringed-site-perfect-duality-for-model: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Perfect duality in a specified normalized coefficient presentation.

lem-sfb-finite-free-dual-chain-comparison vs lem-fix-site-perfect-scalar-hom: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Evaluation-normalized scalar Hom comparison for a site-perfect first variable.

lem-sfb-finite-free-dual-chain-comparison vs lem-pc-finite-projective-internal-hom-evaluation: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Canonical tensor-dual evaluation for a finite free retract.

lem-sfb-finite-free-dual-chain-comparison vs lem-pc-perfect-ring-hom-tensor-differential: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Signed tensor-dual evaluation commutes with differentials.

lem-sfb-finite-free-dual-chain-comparison vs lem-pc-perfect-ring-hom-tensor-dual-iso: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Finite-projective Hom is tensor with the explicit dual.

lem-sfb-finite-free-dual-chain-comparison vs lem-pc-strictly-perfect-ordinary-evaluation: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Ordinary strictly perfect evaluation is degreewise invertible.

lem-sfb-finite-free-dual-chain-comparison vs lem-pur-completed-line-complete: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: A locally free completed coefficient line is derived complete.

lem-sfb-finite-free-dual-chain-comparison vs lem-sf-etale-local-dual-interval: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Uniform local models and Tor interval for a twisted coefficient dual.

lem-sfb-finite-free-dual-chain-comparison vs lem-sfb-ringed-site-bounded-dual-components: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Components and signs of the ordinary bounded dual and bidual.

lem-sfb-finite-free-dual-chain-comparison vs lem-sfb-ringed-site-bounded-evaluation-assembly: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Finite-support assembly of ordinary tensor-Hom evaluation on a ringed site.

lem-sfb-finite-free-dual-chain-comparison vs lem-sfb-ringed-site-finite-retract-dual-exact: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Internal dual and exact Hom of a finite-free retract sheaf.

lem-sfb-finite-free-dual-chain-comparison vs lem-sfb-ringed-site-perfect-duality: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Perfect-complex duality on a small ringed site.

lem-sfb-finite-free-dual-chain-comparison vs lem-sfb-ringed-site-strict-perfect-hom: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Ordinary Hom calculation for bounded finite-projective complexes on a ringed site.

lem-sfb-finite-free-dual-chain-comparison vs lem-sfb-scalar-perfect-dual-realization: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Scalar finite-projective dual realization on a ringed site.

lem-sfb-finite-free-dual-chain-comparison vs lem-sfb-split-perfect-dual-tor-window: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Signed dual models and Tor windows for split-perfect sheaf complexes.

lem-sfb-finite-free-dual-chain-comparison vs lem-weil-pbc-condensed-finite-free-tensor-exact: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Tensoring with a pro-etale locally finite free internal module preserves finite limits.

lem-sfb-finite-free-dual-chain-comparison vs lem-weil-pbc-condensed-internal-hom-sections: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Sections of internal Hom identify with additive module morphisms.

lem-sfb-finite-free-dual-chain-comparison vs lem-weil-pbc-derived-coyoneda-evaluation: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Derived additive coyoneda computes maps from a single complex.

lem-sfb-finite-free-dual-chain-comparison vs lem-weil-pbc-ringed-site-locally-free-derived-hom: the new task fixes scalar extension into native internal modules and identifies its strict signed chart map with the native derived evaluation against every unbounded target; the existing statement is not that native scalar-chart normalization. Existing task: Derived maps from locally finite free sheaves via hypercohomology.

lem-sfb-internal-derived-closed-localization vs def-coef-semilinear-derived-calculus: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Ordinary derived semilinear calculus interfaces.

lem-sfb-internal-derived-closed-localization vs def-pur-external-rhom-pairing-interface: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: External global Hom evaluation interface.

lem-sfb-internal-derived-closed-localization vs def-sfb-internal-slice-derived-hom-comparison: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Local internal module-object derived Hom and restriction comparison.

lem-sfb-internal-derived-closed-localization vs def-sfb-ringed-slice-comparison-model: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Normalized ringed slice comparison data.

lem-sfb-internal-derived-closed-localization vs def-weil-pbc-ringed-derived-restriction: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: RingedDerivedRestriction.

lem-sfb-internal-derived-closed-localization vs def-weil-pbc-ringed-presentation-comparison-data: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Ringed presentation comparison data.

lem-sfb-internal-derived-closed-localization vs lem-coef-rational-bidual-triangle-compatibility: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Coefficient biduality map is compatible with shifts and triangles.

lem-sfb-internal-derived-closed-localization vs lem-coef-semilinear-operations-existence: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Geometric and coefficient operations on a fixed semilinear system calculus.

lem-sfb-internal-derived-closed-localization vs lem-coef-semilinear-system-existence: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Ordinary semilinear system calculus and cartesian internal Hom.

lem-sfb-internal-derived-closed-localization vs lem-coef-signed-single-dual-restriction: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Normalized slice comparison for a single coefficient dual.

lem-sfb-internal-derived-closed-localization vs lem-coef-slice-hom-source-shift: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Slice restriction preserves the normalized source shift of derived Hom.

lem-sfb-internal-derived-closed-localization vs lem-fix-ringed-site-perfect-duality-for-model: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Perfect duality in a specified normalized coefficient presentation.

lem-sfb-internal-derived-closed-localization vs lem-pe-internal-section-tensor-comparison: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Relative tensor and K-flatness under the internal-to-sectionwise module equivalence.

lem-sfb-internal-derived-closed-localization vs lem-pur-external-evaluation-transpose-natural: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Naturality and open restriction of the external evaluation transpose.

lem-sfb-internal-derived-closed-localization vs lem-pur-external-rhom-derived-braiding: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Localization tensor comparison preserves Koszul braiding.

lem-sfb-internal-derived-closed-localization vs lem-pur-external-rhom-signed-cones: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Transport normalized external evaluations to both native coefficient cones.

lem-sfb-internal-derived-closed-localization vs lem-sfb-internal-module-operations-transport: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Internal and sectionwise module operations agree.

lem-sfb-internal-derived-closed-localization vs lem-sfb-module-object-ringed-site-derived-comparison: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Module-object and ringed-site derived internal Hom agree.

lem-sfb-internal-derived-closed-localization vs lem-sfb-open-closed-internal-hom-formulas: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Derived internal Hom for open extension and closed support.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-element-restriction-hom: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Exact closed restriction on arbitrary element sites.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-kflat-rhom-currying: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Evaluation-normalized natural currying on K-flat representatives.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-augmented-cech-restriction: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Restriction preserves the augmented finite Cech tensor complex.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-cech-completion-restriction: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Unit-normalized restriction of Cech completion.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-cech-koszul-comparison-existence: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Existence of the normalized ringed Koszul Cech comparison.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-cech-koszul-dual-limit: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Extended Cech complex and Koszul dual limit.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-complete-elements-locality: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Restriction and descent of complete local sections.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-internal-hom-exact-restriction: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Derived internal Hom calculus on small ringed sites.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-localization-complex-models: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: The unchanged localization complex models and K-flat coefficient certificate.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-localization-factor-restriction: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Restriction preserves one localization complex and its augmentation.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-localization-natural-currying: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Natural evaluation-normalized currying for bounded localization complexes.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-localization-rhom-calculus: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Derived internal Hom and localization of a bounded localization complex.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-model-currying: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Currying with a specified K-flat coefficient sheaf.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-model-currying-coherence: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Restriction preserves the constructed K-flat coefficient currying comparison.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-model-restriction: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Canonical coefficient and tensor-complex transports along a further slice.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-slice-evaluation-coherence: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: The normalized slice comparisons preserve the evaluation counit.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-slice-evaluation-transpose: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Slice restriction preserves evaluation for an arbitrary dualizing object.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-slice-normalized-comparisons: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Existence of normalized slice tensor, Hom and Koszul comparisons.

lem-sfb-internal-derived-closed-localization vs lem-weil-pbc-ringed-slice-representative-evaluation: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Normalized slice evaluation on K-flat and K-injective representatives.

lem-sfb-internal-derived-closed-localization vs lem-weil-proetale-derived-restriction-closed-monoidal: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Normalized native pro-etale restriction is braided closed monoidal.

lem-sfb-internal-derived-closed-localization vs prop-sf-dualizable-hom: the new task includes the native global evaluation isomorphism for pro-etale locally scalar-free models on arbitrary schemes together with derived transport and covering detection; the existing statement is not this full native local-to-global result. Existing task: Internal Hom through the coefficient dual.

## Exact allocation of the returned proof

These are retained proof arguments for the future workers, not proofs inserted in unsplit child statements. They are copied verbatim from the current returned node, including the citations and source places, so no shortening obscures work. The four extracted tasks retain all non-elementary local arguments. Old steps 9--11 are the application of existing same-unit devissage/projection/pullback and residue-recognition statements and remain visible in the parent's short assembly.

### Old step 1 → lem-sfb-internal-derived-closed-localization

Use a small skeleton of each pro-étale site. The internal-module category can be treated as sheaves of modules over its reconstructed section ring, by [def-weil-pbc-internal-abelian-sheaf-module-equivalence]. Its hypotheses hold here: abelian sheafification and monoidality of its local equivalences are supplied by [lem-weil-pbc-sheaf-tensor-closed]. This equivalence is identity on the underlying abelian sheaves, hence exact. The coequalizer defining relative module tensor in [def-sfb-modobj-relative-tensor] represents bilinear maps balanced for the section-ring action, so under this equivalence it is exactly sheaf tensor over that ring. Consequently the equivalence identifies the K-flat derived tensors and their internal-Hom right adjoints. All tensors below are these ambient tensors, without completion.

They are exact in each variable: represent a fixed argument by a K-flat resolution with flat terms, available on a ringed site by [lem-pc-kflat-resolution]. The K-flat tensor functor is triangulated by [lem-sc-source-kflat-tensor-left-triangulated]; the derived tensor of [sk-def-sfb-derived-tensor-hom] is this functor. Symmetry gives exactness in the other variable. The hypotheses apply both to $R_S$-module sheaves and to constant residue-field module sheaves.

Cited statements: def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-weil-pbc-sheaf-tensor-closed, def-sfb-modobj-relative-tensor, lem-pc-kflat-resolution, lem-sc-source-kflat-tensor-left-triangulated, sk-def-sfb-derived-tensor-hom.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md; All three paragraphs: exactness of ambient derived tensor; K-flat construction made explicit.

### Old step 2 → lem-sfb-finite-free-dual-chain-comparison

First compute the dual on a chart, over any small ringed site $(\mathcal C,R)$. Let $T$ be a bounded complex of finite free $R$-modules and put $D_T=\mathcal Hom^\bullet_R(T,R[0])$. Each $\mathcal Hom_R(T^i,-)$ is exact and is a finite sum of the identity functor by [lem-sc-finite-free-internal-hom-exact]. Therefore [lem-pc-bounded-exact-term-hom-quasi-iso], applied to a K-injective replacement of an arbitrary complex $F$, shows that $\mathcal Hom^\bullet_R(T,F)$ computes $R\mathcal Hom_R(T,F)$ as defined in [def-pur-derived-internal-hom]. The complex $D_T$ is bounded finite free, hence K-flat by [lem-pc-bounded-above-flat-kflat-site]. For each degree $n$, the evaluation map
$$\bigoplus_{a+b=n} F^a\otimes_R(D_T)^b\longrightarrow\prod_i\mathcal Hom_R(T^i,F^{i+n})$$
is an isomorphism: only finitely many $i$ occur, and for $i=-b$ the summand map sends $y\otimes\phi$ to $(x\mapsto y\phi(x))$. In a basis its inverse sends $f:T^i\to F^{i+n}$ to $\sum_j f(e_j)\otimes e_j^*$. It is a chain map: the dual differential is $d\phi=(-1)^{b+1}\phi d_T$, so the second tensor-differential term has sign $(-1)^{a+b+1}$, exactly the second term of $df=d_Ff-(-1)^nf d_T$ in [def-pur-hom-complex] and [def-pc-tensor-complex-sheaves]. Thus the canonical comparison $F\otimes_R^{\mathbf L}D_T\to R\mathcal Hom_R(T,F)$ is an isomorphism for every $F$, not merely for bounded or constructible $F$.

Cited statements: lem-sc-finite-free-internal-hom-exact, lem-pc-bounded-exact-term-hom-quasi-iso, def-pur-derived-internal-hom, lem-pc-bounded-above-flat-kflat-site, def-pur-hom-complex, def-pc-tensor-complex-sheaves.

Source: literature/stacks-project/sites-cohomology.tex; Tag 08JH (lemma-Rhom-strictly-perfect); Tag 08JJ (lemma-dual-perfect-complex), finite-free calculation.

### Old step 3 → lem-sfb-internal-derived-closed-localization

Now let $M$ have the local models of the statement and set $D=R\mathcal Hom_{R_S}(M,R_S)$. For a covering chart $W\to S$, [lem-weil-proetale-weakly-etale-localization] identifies its pro-étale site with the slice; Apply the untwisted clause (1) of [sk-prop-sfb-cartesian-coefficients] to $f:W\to S$ and the admissible condensed ring $\Lambda=\underline{\mathcal O_E}$: its canonical ring isomorphism $f^{-1}R_S\simeq R_W$ identifies the restricted ring with $R_W$. This clause applies to arbitrary schemes and morphisms; it imposes no invertibility condition on $S$, and neither its Tate-twist clause nor its finite-extension clause is used. On each chart, derived internal Hom restricts to internal Hom on the slice by [lem-weil-pbc-ringed-internal-hom-exact-restriction]. Tensor restricts to tensor by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], applied to the slice morphism with its restricted coefficient ring. Thus for every $N$ the canonical global evaluation comparison
$$u_N:N\otimes_{R_S}^{\mathbf L}D\longrightarrow R\mathcal Hom_{R_S}(M,N)$$
restricts to the isomorphism in step 2, since $P\otimes_{\mathcal O_E}R$ is a bounded finite free complex. It follows that $u_N$ is an isomorphism globally. Here only detection of isomorphisms is local: slice restriction is exact by [lem-pur-site-restriction-module-adjunction-exact], so kernels and cokernels of each $H^q(u_N)$ restrict to zero. Every section of either sheaf is locally zero on the given covering, hence zero by the sheaf axiom. Apply [lem-weil-pbc-unbounded-derived-iso-cohomology] to conclude. This argument uses a small skeleton of the pro-étale site as in [def-weil-pbc-proetale-site].

Cited statements: lem-weil-proetale-weakly-etale-localization, sk-prop-sfb-cartesian-coefficients, lem-weil-pbc-ringed-internal-hom-exact-restriction, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-pur-site-restriction-module-adjunction-exact, lem-weil-pbc-unbounded-derived-iso-cohomology, def-weil-pbc-proetale-site.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md; Dualizability of a local model: local internal Hom and detection of the canonical comparison; Tag 08JB.

### Old step 4 → lem-sfb-evaluation-duality-completion

The closed adjunction of [sk-def-sfb-derived-tensor-hom], followed by $u_B^{-1}$, gives natural bijections
$$\operatorname{Hom}(M\otimes^{\mathbf L}A,B)\simeq\operatorname{Hom}(A,R\mathcal Hom(M,B))\simeq\operatorname{Hom}(A,B\otimes^{\mathbf L}D).$$
Suppress associators and the symmetry that moves $B$ past $M,D$. Write $e:D\otimes^{\mathbf L}M\to R_S$ for evaluation. Since $u_B$ is the canonical evaluation comparison, the inverse bijection takes $h:A\to B\otimes^{\mathbf L}D$ to the contraction of $M\otimes^{\mathbf L}h$ by $e$. Let $c:R_S\to M\otimes^{\mathbf L}D$ correspond to $1_M$ at $(A,B)=(R_S,M)$. Transposing this defining equality gives $(1_M\otimes e)(c\otimes1_M)=1_M$. Tensoring this equality with $1_A$ shows that $c\otimes1_A$ transposes to $1_{M\otimes A}$, so it is the adjunction unit at $A$. The inverse-bijection formula gives the counit at $B$ as contraction with $e$. The other adjunction triangle, on the right-adjoint image of $R_S$, is therefore $(e\otimes1_D)(1_D\otimes c)=1_D$. Thus $e,c$ satisfy both duality identities globally. Symmetry interchanges the two dual objects and gives also $D\otimes^{\mathbf L}-\dashv M\otimes^{\mathbf L}-$.

Cited statements: sk-def-sfb-derived-tensor-hom.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md; Dualizability of a local model: evaluation, coevaluation and both adjunctions, with triangle identities proved globally.

### Old step 5 → lem-sfb-evaluation-duality-completion

Write $T_M=M\otimes^{\mathbf L}-$. The adjunction $D\otimes^{\mathbf L}-\dashv T_M$ implies product preservation directly: for any $A$ and family $(N_i)$,
$$\operatorname{Hom}(A,T_M\prod_iN_i)\simeq\operatorname{Hom}(D\otimes^{\mathbf L}A,\prod_iN_i)\simeq\prod_i\operatorname{Hom}(A,T_MN_i).$$
The bijections respect projections, so they identify the canonical product comparison. Step 1 gives exactness, and [lem-pc-homotopy-limit-map] then identifies $T_M(R\varprojlim_nN_n)$ with $R\varprojlim_nT_M(N_n)$. For $B_n=(\mathcal O_E/\pi_E^n)_S$, associativity gives $(T_MN)\otimes^{\mathbf L}_{R_S}B_n\simeq T_M(N\otimes^{\mathbf L}_{R_S}B_n)$ as $R_S$-complexes. These are the canonical associations of the same threefold tensor, so they commute with $B_{n+1}\to B_n$ and with $N\to N\otimes^{\mathbf L}B_n$. If $N$ is complete, apply $T_M$ to its completion isomorphism and the preceding limit comparison. The result is exactly the canonical completion map for $T_MN$, hence an isomorphism by [sk-def-pe-derived-completion]. This proves every assertion in the second paragraph of the imported statement.

Cited statements: lem-pc-homotopy-limit-map, sk-def-pe-derived-completion.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md; Dualizability of a local model: products, sequential derived limits and the canonical completion map.

### Old step 6 → lem-sfb-field-bounded-constructible-tensor

We next verify tensor closure with the residue field $\kappa=\mathcal O_E/\pi_E$, which is a field by [def-weil-l-adic-coefficient-extension]. Every sheaf $F$ of $\kappa_S$-modules is flat. To apply [lem-pc-sites-modules-sheafification-flat], view $F$ as a presheaf of modules over the constant presheaf $\kappa$. Each $F(U)$ is a vector space, so tensoring with it preserves finite limits of vector spaces (choose a basis, so this is a direct sum of copies of the identity). Finite limits of presheaves are sectionwise; the hypotheses of that lemma hold. The ring sheafification is $\kappa_S$ and the module sheafification is $F$ with its original action, by [lem-pc-sites-module-sheafification-interface]. This proves finite-limit preservation of sheaf tensor with $F$; sheaf tensor is also a left adjoint by [lem-pc-sheaf-modules-tensor-closed], so it preserves cokernels and is exact. In particular $F[0]$ is K-flat by [lem-pc-bounded-above-flat-kflat-site], and $F[0]\otimes^{\mathbf L}G[0]=(F\otimes G)[0]$ for module sheaves.

Cited statements: def-weil-l-adic-coefficient-extension, lem-pc-sites-modules-sheafification-flat, lem-pc-sites-module-sheafification-interface, lem-pc-sheaf-modules-tensor-closed, lem-pc-bounded-above-flat-kflat-site.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md; The stratum: flatness over the constant residue field, repaired via Tag 03ET (lemma-flatness-sheafification).

### Old step 7 → lem-sfb-field-bounded-constructible-tensor

For constructible $\kappa_S$-module sheaves $F,G$ on the Noetherian scheme $S$, intersect the strata of their two finite stratifications: base-changing the stratification of $G$ along each stratum immersion $Z_a\to S$ of $F$ gives, by [lemma-constructible-pullback-stratification], a stratification of $Z_a$ with strata $Z_a\times_S Z'_b$, and the composites $Z_a\times_SZ'_b\to S$ form a finite stratification of $S$ refining both; its strata are constructible since $S$ is Noetherian. Restriction to a stratum or to an object of a pro-étale cover is module inverse image along a morphism $g$; by clause (1) of [sk-prop-sfb-cartesian-coefficients] for the finite admissible ring $\kappa$, $g^{-1}\kappa_S\simeq\kappa_T$, so restrictions of $\kappa_S$-modules are $\kappa_T$-modules and the restriction of a local model $\kappa_U\otimes_\kappa P$ is again $\kappa\otimes_\kappa P$ over the new coefficient sheaf. On each intersection refine a trivializing cover for $F$ by the pullbacks of a trivializing cover for $G$; the covering axiom makes this a common cover. The finite constant local models in [sk-def-sfb-constructible] are finitely presented, hence finite-dimensional, $\kappa$-vector spaces, so choose bases giving $F|_V\simeq\kappa_V^r$, $G|_V\simeq\kappa_V^s$ on each covering object $V$. Since $F$ and $G$ are flat (step 6), their tensor is the derived tensor, and [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] (applied to the restriction morphism with the ring isomorphism above) gives $(F\otimes G)|_V\simeq F|_V\otimes G|_V$. The basis $e_i\otimes f_j$ identifies this with $\kappa_V^{rs}$. It is therefore a finite constant local model on each stratum, and $F\otimes G$ is constructible. This includes rank zero and the empty stratum.

Cited statements: sk-def-sfb-constructible, lemma-constructible-pullback-stratification, sk-prop-sfb-cartesian-coefficients, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md; The stratum: common stratification, common trivializing cover, and the rank-rs tensor model.

### Old step 8 → lem-sfb-field-bounded-constructible-tensor

Let $A,B\in\Dbc(S,\kappa)$ with $S$ a standing scheme. The truncation triangles of [lem-weil-pbc-truncation-triangle] express each bounded object as finitely many extensions of shifts of its constructible cohomology sheaves. Steps 6 and 7 compute the tensor of any pair of these sheaves as a constructible sheaf. By step 1 tensor is exact in both variables, and [sk-def-sfb-bounded-constructible] says that the bounded constructible category is triangulated on this Noetherian $S$. Induct first through the finitely many truncation triangles for $A$ and then those for $B$ to obtain $A\otimes^{\mathbf L}_{\kappa_S}B\in\Dbc(S,\kappa)$. A cohomological bound is $[a+c,b+d]$ when the input bounds are $[a,b]$, $[c,d]$, since the tensor of $H^i(A)[-i]$ and $H^j(B)[-j]$ is concentrated in degree $i+j$.

Cited statements: lem-weil-pbc-truncation-triangle, sk-def-sfb-bounded-constructible.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md; The stratum: finite truncation induction establishing residue-field tensor closure.

### Old step 9 → parent assembly step 2

Fix $L\in\Dbc(X,\mathcal O_E)$. By step 1 and the triangulatedness assertion (1) of [sk-lem-int-integral-heart], the full class of $K$ for which $K\otimes^{\mathbf L}_{R_X}L$ is bounded constructible is closed under isomorphisms, shifts and extensions. Clause (2) of [det-lem-int-tensor-shriek] therefore reduces the claim to $K=a_!M$, where $a:S\hookrightarrow X$ is a stratum inclusion and $M\in\Dbc(S,\mathcal O_E)$ has the finite-free local models in the statement. A locally closed subscheme of a standing scheme is again separated finite type over $k$. The projection isomorphism in [det-lem-int-tensor-projection] gives
$$(a_!M)\otimes^{\mathbf L}_{R_X}L\simeq a_!(M\otimes^{\mathbf L}_{R_S}a^*L).$$
Clause (1) of [det-lem-int-tensor-shriek] says that $a_!$ preserves the integral category, so it remains to treat the inside tensor.

Cited statements: sk-lem-int-integral-heart, det-lem-int-tensor-shriek, det-lem-int-tensor-projection.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md; Reduction to a stratum: finite extension devissage and the locally closed projection formula.

### Old step 10 → parent assembly step 3, with the completion and field-tensor arguments delegated to the new nodes

By clause (1) of [det-lem-int-tensor-pullback], $N=a^*L$ lies in $\Dbc(S,\mathcal O_E)$. Clause (2) of [sk-lem-integral-models] says precisely that $M$ and $N$ are derived complete and their reductions $\bar M,\bar N$ modulo $\pi_E$ are bounded constructible complexes over the constant field $\kappa_S$. Step 5 shows that $M\otimes^{\mathbf L}_{R_S}N$ is derived complete. Apply [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] to the identity topos with ring map $R_S\to\kappa_S$. Its monoidal scalar-extension isomorphism gives
$$(M\otimes^{\mathbf L}_{R_S}N)\otimes^{\mathbf L}_{R_S}\kappa_S\simeq\bar M\otimes^{\mathbf L}_{\kappa_S}\bar N.$$
The right side is bounded constructible by step 8. It is pulled back from the étale site by [sk-thm-pe-constructible-comparison], applicable because $S$ is Noetherian and hence qcqs and $\kappa$ is a discrete Noetherian ring. The two conditions of clause (2) of [sk-lem-integral-models] now imply $M\otimes^{\mathbf L}_{R_S}N\in\Dbc(S,\mathcal O_E)$. This uses that node's actual residue criterion, replacing the nonexistent node sk-prop-integral-criterion in the imported proof.

Cited statements: det-lem-int-tensor-pullback, sk-lem-integral-models, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, sk-thm-pe-constructible-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md; The stratum: completeness, monoidal reduction, residue comparison and integral criterion.

### Old step 11 → parent assembly step 3

Apply $a_!$ to the membership established in step 10 and use step 9's projection isomorphism. This proves the claim for every generator $a_!M$. Induction through the finite extension construction supplied in step 9 proves it for every $K\in\Dbc(X,\mathcal O_E)$. Throughout, the tensor was the ambient uncompleted tensor; completeness was proved, not imposed by replacing it with a completed tensor.

Cited statements: .

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md; Reduction to a stratum and The stratum: conclusion through the finite extension construction.

## Validation

Server-only checks and the required deliver.py dry run are run after writing this report. Their final outcome is recorded below when the admitted invocation exits. No local check_dag.py, review_split.py, preflight, Lean, Lake or compiler command is run.

The required deliver.py --no-push invocation exited successfully: `OK (not pushed) deliver/Q53/det-lem-int-tensor-product at fe313e3ddd1: preflight passed`. The parent and all four statement-only child files were included in that delivery. A supplemental concept search of WeilConjectures source found ordinary etale sheaf tensor closure and the ell-adic finiteness tensor-closure theorem; these do not state the new arbitrary-Noetherian-scheme constant-field assertion with interval bounds or either native evaluation comparison. Their exact source hypotheses were read before pushing.
