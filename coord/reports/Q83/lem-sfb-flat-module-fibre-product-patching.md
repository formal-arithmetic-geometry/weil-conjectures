# Stage-1 report: lem-sfb-flat-module-fibre-product-patching

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-module-fibre-product-patching.json: existing statement, now split in six steps; statement and statement dependencies unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-tensor-inclusion-flat-reduction.json: new statement-only generic lemma, unsplit; no Mathlib match. One new node, zero new Mathlib leaves.
- citations.json: one exact statement quotation per step/node citation.
- report.md: this report.

## Attachments

None. Searches of lean/WeilConjectures by the item's blueprint tag, by 0D2I and by flat-module/fibre-product/patching terminology found no declaration proving both clauses. The item has no Lean audit requiring extraction of another sorry.

The generic auxiliary implication has related sorry-free code in lean/WeilConjectures/Mathlib/RingTheory/Filtration.lean:66 (Module.Flat.lTensor_subtype_injective_of_smul_eq_zero) and :198 (Module.Flat.lTensor_inclusion_injective_of_smul_le). I read both statements and the latter proof. Neither declaration alone has the new statement's hypothesis interface: :198 assumes injectivity for all submodules of every module killed by J, rather than flatness of E/JE. It is therefore recorded here as useful implementation material, not an exact individual attachment or a Mathlib leaf.

## WANTED

None. All mathematical sources used are available in literature/stacks-project.

## Problems found and corrected

No statement dispute: the item agrees with Stacks 0D2I (1),(2) in Situation 08KH. The source writes L instead of L' in part (2)'s displayed tensors; I read these as the flat module of that clause, as its proof explicitly requires. The DAG statement already does this correctly.

The imported item had no proof. Its seeded two definition dependencies alone would not justify right exactness, flat exactness, the ideal criterion, base-change recovery, or the 051C consequence. The split now cites existing statement nodes for the first four and introduces only the missing relative tensor-inclusion lemma. In particular I did not apply either existing nilpotent-ideal criterion: J need not be nilpotent. I wrote out J times the A'-span of c being contained in c, rather than silently assuming c is already an A'-submodule.

The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor confirms None. I preserved that ancestry and filled the new node's from.place and via relative to it. The latest blueprint unit and direct-images proof (3) were read from literature/blueprint/latest, not from the historical path in the unit record. This is an auxiliary algebra input in the existing alteration/deformation chain, not a replacement of a unit step.

## Unfinished work

The new generic statement is deliberately unsplit, as required for a one-level stage-1 delivery. Its future proof is the first paragraph of 051C: use the ideal Tor-kernel formula to get Tor_1(R/J,E)=0; present a module killed by J by a free R/J-module; the Tor exact sequence and flatness of E/JE show its first Tor vanishes; apply that vanishing to V/U to obtain the tensor injection. Alternatively the two project Filtration declarations above already implement the needed relative-purity argument. No work on the dispatched split is left apart from required validation and delivery.

## Review by Q83

I read Stacks more-algebra.tex Situation 08KH, lemma-module-over-fibre-product (07RU), and lemma-flat-module-over-fibre-product (0D2I) including both proofs. For the one new node I read algebra.tex lemma-what-does-it-mean (051C), its first-paragraph free-presentation proof, remark-Tor-ring-mod-ideal (00M6), and the interpretation of tensor injectivity in the low-degree Tor sequence. I also read lemma-flat (00HD), including the distinction between arbitrary ideals and finitely generated ones. Source tags were checked against tags/tags.

Step 1 uses the statement of lem-sfb-patched-module-base-change for the two canonical projection-induced tensor isomorphisms, not its internal proof. The surjection A' to A and the given gluing isomorphism are exactly its hypotheses. Clause (1) of lem-weil-pbc-tensor-over-quotient-ring then identifies P/JP with N through the first projection. This is flat over R/J=B by the item's hypothesis.

Step 2 uses the same canonical second base-change map. I checked that the tensor reassociation has the displayed inverse t tensor (p tensor a') mapping to a't tensor p, so no tensor-commutation theorem is hidden there. For T=I, J=I as R-modules and the composite with rho is exactly ideal multiplication. The definition node def-weil-pbc-flat-ring-map really defines flat modules by preservation of injections, so it suffices for this application to I included in A'; it is not cited for tensor exactness.

Step 3 uses clause (2) of the quotient-tensor node, since J kills the image ideal in B, and uses the actual right-exactness statement of lem-weil-pbc-tensor-right-exact for the short quotient sequence of b. Flatness of N gives injectivity for the image ideal included in B. The resulting intersection b cap J need not be finitely generated; the proof subsequently treats every ideal inside J, so this does not introduce a false finite-generation assertion.

Step 4 uses precisely the new relative tensor-inclusion statement with E=P and U=c included in V=d. Its hypotheses were proved in steps 1 and 2. For a generator a'c of d and j=(0,i), the equality j(a'c)=(0,ia')c lies in c because ia' is in I. Thus Jd is contained in c even though a' need not lie in the image of R. This is the critical condition permitting 051C, with no nilpotence.

Step 5 applies the same explicit tensor comparison to d, now an A'-ideal. Flatness of M' gives its injection into M'. Step 4 then gives injectivity for c, and step 3 returns to b. I read lem-weil-pbc-flat-fg-ideal-criterion: it tests exactly the multiplication maps for finitely generated R-ideals, which have now all been treated. This proves the first clause without a stronger hypothesis.

Step 6 verifies the ring-module sequence by its coordinate maps and surjectivity of A' to A. I read lem-weil-pbc-flat-tensor-exact: it gives both left injectivity and middle exactness after tensoring with flat L; I do not claim this from the flatness definition alone. The direct-sum and unit tensor identifications have explicit mutually inverse formulas from def-weil-pbc-module-tensor-product. The kernel of the resulting difference map is exactly the displayed compatible-pair module, and the map from L has the required l tensor 1 coordinates. This proves the exact canonical map of the second clause.

For B-E of delivery-errors I checked that the new statement introduces R,J,E,U,V and its maps, cites the two actual notion nodes, contains no proof steps or proof dependencies, and is strictly a generic input rather than either clause of the item. Every cited statement was opened, and citations.json copies it verbatim. All six non-elementary steps are below 2000 characters; the only inline tensor identifications have two explicit inverse formulas and balancing checks. There is no circular citation. Searches of the whole DAG by tags and terms, and blueprint_refs searches for flat module, fibre product, 051C, tensor injective, annihilated, flatness, and purity found no duplicate. No SGA source is used.

Small cases for the item: if I=0, then R=B and the compatible-pair module identifies with N; if A=0 then R=B times A' and the argument is the product-ring decomposition. If A'=0 then A=0 and only the B-part survives. N=0 or M'=0 causes no step to require faithfulness or nonzero modules. With A'=Z, A=Z/2, B=Z/2, N=Z/2, M'=Z and the evident reduction, R=Z and P=Z; J=2Z is not nilpotent and the proof still applies. The nodal-ring non-flat module in the proof of 07RV shows why the second assertion must retain flatness of L; I retained it.

Small cases for the new node: J=0 reduces to the definition of flatness of E; J=R forces U=V, giving the identity injection even if E is not flat. U=0 requires JV=0, and the tensor source is zero. Over R=Z with J=2Z and E=Z, all hypotheses hold and the asserted inclusion is ordinary inclusion. E=Z/2 has flat reduction over Z/2 but multiplication J tensor E to E is zero with nonzero source, so it does not satisfy the missing injectivity hypothesis. These checks rule out an accidental claim that flat reduction alone suffices.

The Mathlib search commands and exact query text are in searches.jsonl and the nodes. I tried two semantic phrasings. I read the returned statements, and the closest candidate LinearMap.lTensor_injective_of_exact_of_flat in Mathlib/RingTheory/Flat/Equalizer.lean:192 assumes a flat cokernel over R, not just an ideal-killed cokernel and flat reduction. The ideal criteria are reused as existing leaves instead of recreated. All searches recorded for the new node were actually run. The invalid Ideal.Quotient Loogle pattern is recorded as such in the raw result and is not evidence of mathematical absence; valid Loogle, LeanFinder, LeanSearch and grep searches were also run.

## Not duplicates

lem-sfb-tensor-inclusion-flat-reduction vs lem-trf-local-nilpotent-projective-flat-lift: concludes projectivity for an already flat module across a nilpotent ideal; the new lemma concerns tensor inclusions and does not assume nilpotence.

lem-sfb-tensor-inclusion-flat-reduction vs lem-sfb-affine-isolated-deformation-lift: constructs affine scheme deformations with prescribed local rings; the new statement is an ordinary module tensor criterion.

lem-sfb-tensor-inclusion-flat-reduction vs lem-sfb-flat-algebra-small-extension-control: gives cotangent obstructions and torsors for algebra lifts over small extensions; the new statement makes no algebra-lifting assertion.

lem-sfb-tensor-inclusion-flat-reduction vs lem-sfb-nilpotent-ideal-module-flatness: assumes a nilpotent ideal and concludes global flatness; the new lemma assumes no nilpotence and concludes only relative tensor injectivity.

lem-sfb-tensor-inclusion-flat-reduction vs lem-sfb-nilpotent-ideal-flatness-criterion: assumes a nilpotent ideal and concludes global flatness; the new lemma covers arbitrary ideals and only inclusions with ideal-killed quotients.

lem-sfb-tensor-inclusion-flat-reduction vs lem-sfb-space-square-zero-flatness-criterion: is a geometric criterion for algebraic-space thickenings; the new lemma concerns arbitrary modules and ideals.

lem-sfb-tensor-inclusion-flat-reduction vs lem-sfb-nilpotent-fibre-flat-module: lifts module flatness along a ring map with a nilpotent base ideal; the new lemma assumes no second ring or nilpotence.

lem-sfb-tensor-inclusion-flat-reduction vs lem-sfb-finite-embedded-dual-number-graphs: classifies embedded first-order deformations on projective schemes, not generic tensor inclusions.

lem-sfb-tensor-inclusion-flat-reduction vs lem-sfb-tor-one-extension-exactness: states middle exactness of a three-term Tor sequence for arbitrary extensions; it does not give the ideal-relative vanishing/injectivity asserted here.

lem-sfb-tensor-inclusion-flat-reduction vs lem-sfb-ring-deformation-smoothness-test: is a marked deformation-functor smoothness criterion for Artinian local bases, not a tensor-inclusion criterion.

lem-sfb-tensor-inclusion-flat-reduction vs lem-weil-pbc-tensor-over-quotient-ring: gives quotient tensor isomorphisms and no preservation of injections across an extension; it is reused in the item.

lem-sfb-tensor-inclusion-flat-reduction vs lem-weil-pbc-flat-local-criterion-nonzerodivisor: has local Noetherian finite-module and nonzerodivisor hypotheses, concluding flatness; the new lemma has none of those assumptions.

lem-sfb-tensor-inclusion-flat-reduction vs lem-weil-pbc-flat-module-completion-flat: states flatness of adic completion over Noetherian rings, with no arbitrary ideal-killed tensor inclusion.

lem-sfb-tensor-inclusion-flat-reduction vs lem-weil-pbc-flat-variant-local-criterion: has local Noetherian finite-module hypotheses and concludes global flatness; these hypotheses are unavailable for the new generic implication.

The finite-projective patching node, finite-module patching node, and patched-module-base-change node were also read: respectively they concern finite projectivity, finite generation, and recovery of scalar extensions, rather than the two flatness clauses or the new generic tensor inclusion.
