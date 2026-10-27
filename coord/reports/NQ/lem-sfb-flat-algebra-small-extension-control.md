# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-algebra-small-extension-control.json`: split into ten steps, statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-ideal-flatness-criterion.json`: new statement-only input; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ring-square-zero-extension-classification.json`: new statement-only input; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every citation in every item step.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the item tag and small-extension, cotangent, marked-lift and extension-class terminology. UniversalFirstOrderThickeningCore constructs a universal formally unramified thickening, BasisIffBasisQuotientOfNilpotent lifts bases of modules already known flat, and DirectSumExtensionAssembly concerns module Ext-one; none proves this item's ring-deformation statement. No compiler, Lake command, or Lean edit was used.

## WANTED

None. The Stacks sources used here are present locally.

## Findings and changes

The imported item was an unsplit statement. Its hypotheses and every conclusion agree with the cited route: cotangent.tex Tag 08SP (lemma-find-obstruction), Tag 08QQ (lemma-flat-base-change-cotangent-complex), Tag 08SF (lemma-localize), and algebra.tex Tag 051C (lemma-what-does-it-mean). No statement correction was required. I did not add finite-type, isolated-singularity, lci, Noetherian, or finite-module assumptions.

Rather than creating a new general obstruction-and-torsor node that repeats the item, I used extension classes and the existing transitivity triangle to derive both conclusions in the item's steps. The only new inputs are classification of arbitrary square-zero extensions (before any lifting problem is imposed), and a module flatness criterion (with no cotangent complex). The proof shows why a marking fixes the kernel identification, why a square-zero solution is flat, and why the class fibre has a free action. In particular, it does not assume that Ext-one always injects into the larger extension-class group: the needed Hom-zero is proved in Step 7.

Blueprint search commands were run for `cotangent`, `square-zero`, `extension`, `flat nilpotent`, `square-zero extensions`, `cotangent Ext`, `0GPT`, `0GPX`, `08RB`, `051C`, and `08QS`. I read the matching imported statements; none gives either new input or this item. Searches by source tags and notions across all of `dag/nodes` found the cotangent base-change, transitivity, localization, naive comparison, flat-tensor, tensor-over-quotient, and derived-category tools used below. The latest blueprint file read is `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, proof (3). The current created.item chain has no surviving imported blueprint ancestor: `tools/blueprint_refs.py ancestor lem-sfb-flat-algebra-small-extension-control` reports None. I retained the inherited precise proof place and via chain; the new nodes' from.node is null, exactly as computed by the tool. This is reported explicitly rather than inventing a blueprint identity.

All new-node Mathlib queries were executed with the required msearch.py command and their returned summaries/digests are copied in the node records. I read the returned hits, including Extension/Cotangent/Basic.lean:53--105 and Flat/Tensor.lean:90--97. The former defines the conormal-to-differential linear map of a presentation, not derived Ext classes of ring extensions. The latter tests multiplication injectivity for every finitely generated ideal, not lifting flatness across one nilpotent ideal. A second semantic phrasing was tried for each new input. The item also has new semantic and grep searches, in addition to its preserved imported searches. No failed service is described as a negative result.

## Unfinished work

The two new nodes are deliberately statement-only and unsplit, as required for a one-level split. There is no unfinished argument in the item's assembly proof. No proof step exceeds 2000 characters.

## Review by NQ

I read Stacks cotangent.tex section-deformations, its equation-to-solve and the whole proof of Tag 08SP, then defos.tex Tags 0GPT/0GPU/0GPV/0GPW and 0GPX/0GPY, including the polynomial-presentation formula. The extension-class input uses the full cotangent complex: Tag 08RB compares its truncation in degrees -1,0 with the naive complex, and a module shifted to degree -1 sees no lower-degree tail. The class formula sends a lifted polynomial relation to its kernel value. Pairing two such maps and then adding them gives the Baer-sum clause; composing a presentation map gives the pullback formula in 0GPW. Thus the new classification node is stated without unsupported extra finiteness or flatness hypotheses. Its source explicitly distinguishes the Baer clause derived from the formula from what Stacks states verbatim. In a later split, this argument can use the already existing naive-comparison node; it is not a new copy of that comparison.

For the module input I read algebra.tex Tag 051C in full and the statement of 00M6: injectivity of multiplication is precisely the missing Tor-one vanishing, and nilpotence is what promotes quotient flatness to flatness of the whole module. The existing local criteria require Noetherian rings and finite modules, neither available for arbitrary B here. This is why those nodes cannot substitute for the new input.

Step 1 uses precisely the two tensor-over-quotient identifications in `lem-weil-pbc-tensor-over-quotient-ring`; I checked the formula and the fact that the maximal ideal annihilates I. The assumption that the surjection respects augmentations puts I inside the maximal ideal. The explicit inverse on tensors makes this step elementary; it invokes no hidden deformation theorem.

Step 2 uses `lem-weil-pbc-flat-tensor-exact` to preserve the injection I into C', not just the definition of flatness, and `lem-weil-pbc-tensor-over-quotient-ring` to replace I tensor E by I tensor B. The statement of the former includes the left injection; the latter includes tensoring an annihilated module. I checked the kernel action and the formula i times a lift of b, which makes the marking force the kernel identification. Step 3 uses the same quotient-tensor statement and the new nilpotent criterion, after establishing IE=N, E/IE=B, and that multiplication is the given injection. There is no assumption that E is finite over anything.

Step 4 uses the new classification statement's compatible-map criterion with base C', A=C, B=B, M=I, N=N, and u=c. A C'-algebra map C' to E is the structural map itself, so the fibre contains exactly the required solutions and no extra maps. Step 5 uses the full statement of `lem-pur-sheaf-ring-derived-coefficient-adjunction` on the one-object site, and `lem-trf-one-point-derived-ring-identification` to justify its use for ordinary modules. Both statements were opened and their unbounded hypotheses read. `lem-trf-cotangent-transitivity-triangle` states both the specified arrows and naturality in diagrams of triples, exactly what is needed here and again in Step 10.

Step 6 uses the mathlib leaf `lem-weil-pbc-hom-out-of-triangle-exact`. Its two factorization clauses apply after shifts and rotation and give the kernel/image assertion at eta and at z. The obstruction is the actual composite eta[1] after d, not an unnamed existence class. Step 7 uses the existing arbitrary-polynomial-presentation statement `lem-trf-lci-naive-cotangent-model`, not an lci-only theorem: the empty set of variables gives P=C', kernel I, differential term zero. Universal derivations of C' over itself vanish by the explicit definition in `def-weil-pbc-kahler-differentials`. Nonpositive degrees follow from `def-trf-cotangent-resolution-data`. The mathlib orthogonality leaf then gives Hom(L_C/C',N)=0; Step 5's adjunction gives Hom(A_0,N)=0. The same Hom-exact leaf proves uniqueness of t, so the action is simply transitive.

Step 8 uses `lem-trf-flat-resolution-canonical-tensor-comparison` with the bounded-above flat resolution B[0] of B, so its comparison is exactly B tensor^L_C k to B tensor_C k. That verifies the hypothesis of `lem-trf-cotangent-flat-base-change`, whose statement I read, rather than assuming k flat over C. The already cited adjunction and one-point equivalence identify the resulting Hom groups with the T^j in the item. This identification is for all relevant j and uses no perfectness or finite generation.

Step 9 uses the mathlib leaves `lem-weil-pbc-localization-module-exact`, `lem-weil-pbc-localization-flat`, and `lem-pc-module-flat-transitive`. I opened each statement: the first preserves an arbitrary exact module sequence; the second covers any multiplicative subset including zero; the third requires flatness of each of two successive ring/module maps, furnished here by the hypothesis and localization. The fraction argument explains the exact localized kernel and why its coefficients are S^{-1}N. Step 10 uses the classification node's actual compatible-map criterion on E to E_S, the triangle node's naturality clause, and `lem-trf-cotangent-augmentation-localization`'s canonical quasi-isomorphism for arbitrary multiplicative subsets. Thus localization sends eta[1]d to eta_S[1]d_S and z+t v to z_S+t_S v_S. Natural adjunction and the specified square-induced cotangent map from the base-change node identify these with the maps on the special-fibre T groups. I checked that this does not assert localization of Ext is an isomorphism: no such conclusion is valid without additional finiteness assumptions.

The non-Mathlib cotangent and scalar-adjunction tools from other units are listed in split_report.tool_uses with their purpose. These are tools for ordinary rings and module derived categories; they implement the inherited affine formal-lifting route rather than replacing a unit-level proof. Definitions and Mathlib leaves are not recorded as route exceptions.

Small cases checked: I=0 gives the unique marked lift and zero coefficient groups; B=0 gives the zero lift and zero groups; polynomial B over C gives no positive cotangent Ext; S={1} gives identity localization; 0 in S gives zero localized rings and groups. For the nilpotent criterion, R=k[e]/e^2, J=(e), M=k fails the injectivity hypothesis (the multiplication is zero with nonzero domain), while M=R satisfies it; J=0 reduces to its assumed flatness. For extension classification, A=R gives zero Ext-one and the unique split class, whereas split extensions of general A provide the zero class and derivations change maps rather than quotient markings. These tests include positive characteristic and infinite sets of polynomial variables. No source error or statement dispute was found.

I corrected the potential missing-flatness inference by making the multiplication criterion a separate generic input and giving the comparison on kernel tensors in Step 3. I also kept the Hom-zero argument explicit instead of treating a fibre as automatically a torsor under the entire Ext-one group. No independent reader was used: this is the direct-delivery self-review required by the dispatch brief.

## Not duplicates
lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-base-change-ideal-kernel-generators: expresses a base-changed kernel as a span; the new criterion deduces flatness across a nilpotent ideal.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-colimit-eventually-flat: descends flatness in a directed Noetherian system; the new criterion has no system or colimit.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-colimit-maximal-kernel-descent: kills a maximal-ideal multiplication kernel after passage along a directed system; the new criterion concludes flatness from nilpotence.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-criterion-flatness-fibre-noetherian: is a fibre criterion for finite nonzero modules over Noetherian local rings, not the arbitrary-module nilpotent-ideal criterion.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-finite-ideal-kernel-descent: descends finitely many multiplication-kernel elements in a colimit system; the new criterion has no colimit and concludes flatness.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-finite-tensor-kernel-generators: proves finite generation of a multiplication kernel over Noetherian rings; the new criterion has no finiteness hypothesis and concludes flatness.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-flat-another-variant-local-criterion: proves flatness after a localized tensor base change for finite modules over Noetherian local rings; the new criterion is the unrestricted nilpotent-ideal criterion.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-flat-local-criterion-nonzerodivisor: assumes a Noetherian local map, finite module, and a regular element; the new criterion allows an arbitrary module and a nilpotent ideal.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-flat-variant-local-criterion: assumes Noetherian local rings and a finitely generated module; the new criterion has neither assumption and instead assumes nilpotence.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-localized-base-change-ideal-kernel-span: controls the span of a multiplication kernel after localized tensor base change; the new criterion has neither a base-change square nor a span conclusion.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-quotient-cycle-lift: lifts a Tor cycle to a resolution; the new criterion asserts flatness and does not specify a cycle formula.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-quotient-tensor-comparison: constructs a map of quotient tensor complexes; the new criterion asserts flatness from a nilpotent ideal.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-tensor-over-quotient-ring: identifies quotient tensor products and proves no flatness-lifting assertion.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-tor-ideal-comparison-compatibility: constructs, identifies or compares Tor-one with a multiplication kernel; the new criterion uses that kernel vanishing to deduce flatness from nilpotence, and is not a Tor computation.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-tor-ideal-connecting-formula: constructs, identifies or compares Tor-one with a multiplication kernel; the new criterion uses that kernel vanishing to deduce flatness from nilpotence, and is not a Tor computation.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-tor-ideal-homology-exactness: constructs, identifies or compares Tor-one with a multiplication kernel; the new criterion uses that kernel vanishing to deduce flatness from nilpotence, and is not a Tor computation.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-tor-ideal-homology-formula: constructs, identifies or compares Tor-one with a multiplication kernel; the new criterion uses that kernel vanishing to deduce flatness from nilpotence, and is not a Tor computation.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-weil-pbc-tor-ideal-kernel-naturality: constructs, identifies or compares Tor-one with a multiplication kernel; the new criterion uses that kernel vanishing to deduce flatness from nilpotence, and is not a Tor computation.

lem-sfb-nilpotent-ideal-flatness-criterion vs lem-sfb-flat-algebra-small-extension-control: is the present marked algebra deformation problem; the new criterion concerns only module flatness and neither obstruction nor torsor.

lem-sfb-ring-square-zero-extension-classification vs def-trf-naive-cotangent-comparison-data: defines comparison data only; the new node is a theorem classifying square-zero algebra extensions.

lem-sfb-ring-square-zero-extension-classification vs lem-trf-lci-naive-cotangent-model: identifies a truncation of the cotangent complex with a presentation complex; the new extension node classifies ring extensions and their compatible maps.

lem-sfb-ring-square-zero-extension-classification vs lem-trf-standard-cotangent-boundary-cokernel: computes a presentation boundary cokernel; the new node classifies ring extensions and their functorial classes.

## Validation

The server's `review_split` passed, and `check_dag` reported no finding introduced by the sandbox or on its nodes. The first required delivery dry run passed preflight at 1b2d1f50ccc. I then added the newly run item searches to the preserved item search record and reran the final dry run before pushing.
