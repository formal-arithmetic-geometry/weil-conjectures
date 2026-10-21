# Stage-1 repair: lem-sfb-extend-to-qlbar-constructible

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-extend-to-qlbar-constructible.json`: existing statement, unchanged, with a short three-step assembly instead of the returned 3851-character proof.
- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-extension-inverse-image.json`: new statement, not a Mathlib leaf; inverse image commutes naturally with extension along arbitrary internal ring objects.
- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-extension-finite-presentation.json`: new statement, not a Mathlib leaf; scalar extension carries a finite free cokernel presentation to a finite free cokernel presentation.
- `citations.json`: verbatim supporting quotations for every node used by every parent proof step.

## Attachments

None claimed. In `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean:175–179`, `AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj` has exactly the parent statement but its proof is `sorry`. Its existing Lean record and all imported metadata are retained. No Lean was written or compiled.

The side library `lean/Sheaf/AlgebraicGeometry/BoundedConstructibleExtendScalars.lean` contains useful source implementations: the private `pullbackExtendScalarsIso` (line 30), private `extendScalarsRegularIso` (line 81), and public `AlgebraicGeometry.ProEtale.fp_extend` (line 103). These are supporting code readings, not a claim that the requested declaration in WeilConjectures is finished. The finite-presentation helper additionally specifies the finite-free comparisons and the conjugated cokernel presentation. No new proof or axiom audit is asserted for these source declarations.

## WANTED

None. The current blueprint, dependency statements and source implementations suffice for this repair. No SGA source is used.

## What was wrong and what changed

The maintainer requested a finer split of the returned proof, whose three steps totalled 3851 characters. I retained the previous retry's two helper statements and its short assembly, compared them with the current repository parent, and supplied the missing report and helper proof arguments. The two substantial constructions formerly inline are now separate nodes; the existing exact-derived and homology nodes already cover the other non-elementary argument. Each helper argument below is well below 3000 characters, and the parent proof is below 2000 characters. New nodes remain statement-only `unsplit`, as required by the stage-1 node format; their proofs in words are recorded below for the subsequent worker.

The current parent definition `sk-def-sfb-bounded-constructible` and the actual upstream `IsConstructibleModuleObject` use finite stratifications with locally finitely presented internal modules. The returned proof instead asked for constant-scalar matrix local models and discussed affine-local versus global constructibility. Those stronger conventions are unnecessary for this parent. The retained repair uses exactly the current finite stratification and presentation covers, with actual inverse-image rings. It never identifies them with coefficients pulled back from a point. The parent statement is byte-for-byte unchanged; no extra assumption on X, E or K is introduced. The chapter and unit route, including unit step 9, is unchanged.

## Proof in words: lem-sfb-internal-extension-inverse-image

Source: the last clause of `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-to-qlbar-constructible.proof.md`, expanded by the agent. I read the tensor coequalizer in `sk-def-sfb-change-of-scalars`, the strong monoidal inverse image in `def-sfb-finite-upper-star-monoidal`, the adjunction in `def-sfb-finite-upper-lower-star-adjunction`, and the action formula in `def-sfb-modobj-transport`.

Write Q for the balancing coequalizer of the two maps S tensor R tensor M to S tensor M. The inverse image F preserves this coequalizer: for any target N, adjunction identifies maps F(Q) to N with maps Q to g_*N, hence with maps F(S tensor M) to N equalizing the images of the two arrows. This is the coequalizer universal property, naturally in N. The invertible tensorators of F identify the image pair with the balancing pair F(S) tensor F(R) tensor F(M) to F(S) tensor F(M). Compatibility with the monoid multiplication, unit and M-action is exactly the lax monoidal transport formula. Consequently the two proposed objects are coequalizers of the same pair. The unique isomorphism commuting with the quotient maps is F(S)-linear: precomposition with the tensor of the quotient map reduces linearity to the action on the first factor. Its inverse is linear by the same argument. For a module map, the two candidate composites agree after the quotient map, so uniqueness proves naturality. The rings remain F(R), F(S) throughout.

This is a categorical comparison construction, not a clause asserting constructibility or boundedness. Its implementation needs the balancing diagram, monoidal comparisons and the module action, which are what the old step hid.

## Proof in words: lem-sfb-internal-extension-finite-presentation

Source: the same blueprint proof's clause “tensoring local finite presentations ... gives local finite presentations”, expanded by the agent. I read `sk-def-sfb-change-of-scalars`, `def-sfb-finitely-presented-module`, `sk-def-sfb-sheaf-tensor` and the source implementation at `lean/Sheaf/AlgebraicGeometry/BoundedConstructibleExtendScalars.lean:62–107`. The regular-module comparison is also the first assertion of the existing `lem-weil-pbc-regular-extension-comparison`.

Let A be extension of scalars. On the regular module, multiplication S tensor R to S, sending the pure tensor s tensor r to s phi(r), equalizes the balancing arrows. It descends to an S-linear map S tensor_R R to S. The map back inserts the unit of R. Multiplication followed by this insertion is the identity because the balancing relation rewrites s tensor r as s phi(r) tensor 1; the other composite is the identity by the unit law. Equivalently use the cited regular-module comparison. Since A preserves finite colimits, applying it to the finite coproduct of k copies of R and then using that comparison gives A(R^k) isomorphic to S^k, including k=0. Applying A to the chosen cokernel cofork gives a cokernel cofork, since cokernels are finite colimits and A preserves zero maps (it preserves the zero object). Conjugate A(f) by the two finite-free comparisons. The resulting cofork is a cokernel cofork for f_S, so its universal property gives A(M) isomorphic to coker(f_S). These are precisely the witnesses in the definition of finite presentation. Flatness is not used.

## Search results and reuse

I read and reused all twelve entries of the retained `searches.jsonl`, together with the recorded parent searches; no search was invented or replaced by an unlogged service request. Each helper was searched with LeanFinder, Loogle, LeanSearch and grep, and with a second conceptual phrasing. Their exact queries and outputs remain in their JSON `mathlib_searches`. I also read the closest Mathlib source hits: `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` (presentations and `Presentation.map`) and `Algebra/Module/FinitePresentation.lean` (ordinary module base change). These concern `SheafOfModules` or ordinary modules. Our objects are the project's `CategoryTheory.Mod` internal modules; their finite presentation is `Mod.IsFinitelyPresented` in `ModuleObjects/Free.lean:50`. Transporting between these interfaces is not a one-line specialization, and neither hit supplies the monoidal internal inverse-image comparison. Thus both nodes remain unsplit, with no Mathlib match.

Whole-DAG searches used the concepts extension/scalar change, finite presentation, inverse image, relative tensor, the balancing coequalizer and the source helper names. Whole-blueprint searches with `tools/blueprint_refs.py search` included `extension scalars finite presentation`, `inverse image extension`, `relative tensor`, `finite presentation`, `scalar comparison`, and `extension of scalars`; the ancestor command confirms this parent is the blueprint ancestor. No blueprint node states either new helper. The sources are blueprint clauses, not Stacks-tagged results, so there is no new shared Stacks tag to audit.

## Not duplicates

lem-sfb-internal-extension-inverse-image vs lem-pur-inverse-image-scalar-comparison: the existing node assumes a scheme isomorphism and uses sheaves of modules with a unit-section normalization; the new node allows every scheme morphism and uses internal module-object transport.

lem-sfb-internal-extension-inverse-image vs lem-pur-independent-inverse-image-tensor-comparison: the existing node compares tensor products over one fixed ring through a specified set-sheaf algebraic inverse image; it explicitly omits scalar extension. The new comparison changes R to S and uses the monoidal abelian inverse image.

lem-sfb-internal-extension-inverse-image vs lem-sp-stratum-scalar-extension: the existing node requires finite constant coefficient rings and a stratum immersion; the new comparison is for arbitrary internal commutative rings and any scheme morphism, including the presentation cover maps.

lem-sfb-internal-extension-inverse-image vs lem-sf-finite-field-local-tensor-model: the existing node assumes constant fields and a prescribed constant local model; it does not give the arbitrary internal-ring natural functor isomorphism.

lem-sfb-internal-extension-finite-presentation vs lem-weil-pbc-regular-extension-comparison: the existing node supplies the rank-one regular-module isomorphism and an endomorphism compatibility. The new node supplies every finite-rank comparison and the resulting cokernel presentation.

lem-sfb-internal-extension-finite-presentation vs lem-sfb-lfp-tensor-single: the existing node concerns derived tensor of two locally finitely presented modules over special ell-adic coefficients on a noetherian space. The new node changes arbitrary internal coefficient rings and preserves a global finite presentation, with no flatness or noetherian hypothesis.

Both new nodes vs lem-weil-pbc-bounded-constructible-exact-scalar-extension: the existing theorem concerns bounded constructible derived complexes after an exact scalar extension. Neither new node states that conclusion: one constructs the ring-changing inverse-image comparison and the other preserves a global presentation without flatness. I did not replace the requested finer proof by a black-box application of the whole existing derived theorem.

## Review by Q26

I read the current blueprint statement and its proof, the parallel subfield proof, and the chapter and two-colimit unit. Their route is termwise exact extension, cohomology, and local finite presentations on unchanged strata. I compared the retained retry against the current parent: only proof, proof dependencies, proof origin and split report differ. The existing Lean theorem remains sorried, so it is not an attachment. The human's re-split request is met by the two separate categorical arguments above; it is not a rebase or an unchanged re-push.

For parent step 1 I opened all five cited statements. `lem-sfb-qlbar-flat` really supplies finite-limit preservation for every scheme, matching the global hypothesis of `lem-sfb-extend-scalars-preserves-homology`; `sk-def-sfb-change-of-scalars` supplies finite-colimit preservation. `def-sfb-left-derived-exact` supplies the exact-to-termwise identification, and `def-sfb-derived-extend-to-qlbar` names precisely this derived extension. Their combination gives the cohomology formula. No claim of a derived comparison is taken merely from a definition of flatness.

For step 2 I opened `sk-def-sfb-bounded-constructible`, `def-sfb-constructible-module`, `def-sfb-locally-finitely-presented` and `def-sfb-finitely-presented-module`. They supply, in order, constructible cohomology, a finite scheme stratification, pro-etale covers and finite free cokernel presentations over the actual twice-pulled-back coefficient rings. The new inverse-image statement can be applied to both the immersion and each cover morphism; the second application uses its arbitrary-ring formulation. The other new statement requires no flatness, so it applies to those pulled-back rings without any additional coefficient identification. Composing the isomorphism into a cokernel presentation proves its invariance under the comparisons. No scalar entries are required to be constant. The helper statements and the proofs above were checked against those exact definitions and the displayed tensor coequalizer; neither is a restatement of the parent.

For step 3 I checked that the bounded-constructible criterion asks for one finite interval and constructibility in every degree. Step 2 applies in every degree, including zero cohomology. Step 1 and preservation of the zero object retain the same interval. This final assembly is elementary; the non-elementary cohomology and local-presentation comparisons have already been cited. Every citation quote is copied verbatim from its node's statement, and the proof-dependency list is exactly the union of the step uses.

I checked the small cases: the empty scheme and empty strata impose no extra cover requirement; rank zero uses the preserved zero object; the zero module has a zero-rank presentation; identity coefficient maps and identity inverse images give the identity comparisons; the zero target ring gives the zero module; a nonflat map such as Z to Z/2 still preserves a cokernel presentation, although it need not preserve kernels. Thus no flatness was silently inserted into the finite-presentation node. No quasi-compactness, quasi-separatedness, noetherianity or characteristic hypothesis was used.

B1–B9: the new nodes introduce all objects, use the project's definitions, contain statement-only unsplit records and exact logged searches, and have specified blueprint origins. C1–C8: every non-elementary parent input is cited, no proof of a node is substituted for its statement, and the generic off-unit exact/derived tools are explained in the split report. D1–D5: the parent still carries the stratification-and-cover assembly, and neither helper carries bounded constructibility. E1–E7: I checked hypotheses, coefficient categories, the two restriction maps and the edge cases above. No mathematical statement dispute was found. No parent step is longer than 2000 characters.

## Unfinished work

None in the requested stage-1 repair. The two newly exposed statements are deliberately unsplit queue items; their short arguments and sources are given above. Delivery validation follows below.
