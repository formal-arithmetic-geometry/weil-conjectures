# Stage-1 delivery: lem-sfb-prime-to-ell-scalar-bar-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-prime-to-ell-scalar-bar-model.json`: split; statement and statement dependencies preserved; six proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-positive-bar-row-local-effacement.json`: statement, unsplit; no Mathlib match. Relative, sheaf-valued analytic effacement for the regular noncomplete scalar module and a prime-to-ell group.
- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-bar-row-finite-index-transfer.json`: statement, unsplit; no Mathlib match. Generic internal finite-coset transfer and horizontal homotopy, commuting with the vertical differential before taking cohomology.

The sandbox also contains `citations.json` (one verbatim statement quote for each use in each numbered step), the actual `searches.jsonl`, and the sandbox-only writing script. No Lean, repository, launcher, unit, chapter, or coordination file was written.

## Attachments

None. Searches for the item's blueprint tag, prime-to-ell scalar/bar terminology and internal profinite Hom comparisons in `lean/WeilConjectures/` found no finished declaration stating the item. The existing action and bar specification definitions are not an attachment of this comparison theorem. The broader search in `lean/Sheaf/` found no such theorem either. Neither new node has an existing project declaration.

## WANTED

WANTED: an exact reference for relative open-subgroup effacement of positive INTERNAL vertical bar-cohomology rows for the regular condensed ring of all continuous norm-topological algebraic ell-adic scalar functions, for `lem-sfb-relative-positive-bar-row-local-effacement`.

WANTED: an exact reference for finite-index transfer on ordinary internal condensed-module bar double complexes, compatible with all profinite base changes and a second differential, for `lem-sfb-internal-bar-row-finite-index-transfer`.

WANTED: a reference assembling the above into the actual scalar underived-to-derived bar augmentation for `lem-sfb-prime-to-ell-scalar-bar-model`. The abstract spectral-sequence portion is in Stacks `homology.tex`, Tags 012X and 0132, with the column-specialization in Tag 0133. These tags do not supply the analytic lemma.

## Problems found

The current blueprint's `latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), motivates this scalar input but does not prove it. The new proof is therefore explicitly agent-written. The unit record retains its historical sketch, while the current paragraph routes rational and algebraic coefficients through the open coefficient comparison. This delivery stays below that open-image input and changes neither the unit nor chapter.

There is no item repair record and no prior sandbox split to retain. The item is unsplit in the read repository. The blueprint ancestor utility returns None; the inherited null `from.node` and exact `via` chain are retained, and the new nodes prepend this item to that chain. Whole-blueprint searches for bar total, local effacement, corestriction, transfer and cohomology sheaf did not find either new statement; `same_as` is empty.

## Source error

The current statement of `lem-sfb-norm-algcl-profinite-cech-exact` explicitly gives a metrizable profinite surjection with a nontrivial global degree-one continuous Omega-valued Cech cocycle, while the older proof of `lem-sfb-norm-algcl-bar-augmentation`, step 2, still uses that node for universal positive Cech exactness. That is a concrete C4 mismatch visible in the statements, not evidence against this item's total comparison. This delivery does not cite that node or the older procyclic bar augmentation. It does not infer completeness of Omega or acyclicity of individual Omega Hom columns. No change of the present item statement was needed; there is no STATEMENT-DISPUTED declaration for it.

## Not duplicates

lem-sfb-relative-positive-bar-row-local-effacement vs lem-sfb-evaluated-positive-bar-row-local-effacement: the latter forms vertical kernel/image quotients of the complexes evaluated at the point. The new statement takes internal cohomology sheaves first, then arbitrary profinite sections, and allows finite covers of that parameter. Evaluation at a point cannot supply that sheaf-valued statement.

lem-sfb-relative-positive-bar-row-local-effacement vs lem-sfb-norm-algcl-profinite-cech-exact: the latter concerns a single profinite surjection and its Cech functions; its local split-cover contraction has no bar horizontal cycles or open subgroups. Its global-exactness assertion has explicitly been corrected to a counterexample. The new lemma does not restore that false assertion.

lem-sfb-relative-positive-bar-row-local-effacement vs lem-sfb-profinite-invariants-sheafified-cohomology: the latter identifies derived invariants with sheafified object cohomology but asserts no local boundary after subgroup restriction of the positive vertical rows.

lem-sfb-relative-positive-bar-row-local-effacement vs lem-sfb-prime-to-ell-cochain-finite-quotient-descent: that compares two explicit scalar function complexes, not the vertical derived-Hom cohomology sheaves of an injective resolution.

lem-sfb-internal-bar-row-finite-index-transfer vs lem-sfb-evaluated-positive-bar-row-transfer: the latter states maps on abstract rational vertical cohomology after point evaluation of a resolution. The new lemma works on internal double-complex objects before evaluation and cohomology, for arbitrary rings and coefficient complexes, with parameter compatibility.

lem-sfb-internal-bar-row-finite-index-transfer vs lem-sfb-continuous-cochain-finite-index-transfer: the latter's coefficients are topological vector spaces with jointly continuous action. An arbitrary internal condensed module or injective resolution term is not such a topological coefficient space. The new lemma cannot be a one-line specialization.

lem-sfb-internal-bar-row-finite-index-transfer vs lem-sfb-finite-coset-homogeneous-averaging: that gives a transfer formula for equivariant continuous functions into a topological vector space; it does not give an internal sheaf homotopy commuting with a second differential.

lem-sfb-internal-bar-row-finite-index-transfer vs lem-sfb-condensed-injective-bar-rows: exact horizontal rows for equivariant injectives do not give restriction/corestriction identities on their vertical cohomology or the specified homotopy.

Neither new node states a bar-total comparison, an isomorphism of the two objects in the item, resolution independence, or augmentation normalization. They are not clauses of the item moved under new names: their combination is used to kill a specific E2 obstruction, and steps 1, 2, 4, 5 and 6 carry the remaining argument.

## Mathlib searches and read hits

All searches recorded in the new nodes were executed by the mandated msearch command for Q62 and this item. The two semantic phrasings for effacement returned Nobeling exactness, light condensed sheaf constructions, and continuous cochain definitions. I read the local `Condensed/Light/InternallyProjective.lean`: its free-profinite lifting criterion is conditional and in a different coefficient category, not the needed scalar or positive-row comparison. The online continuous-cohomology hit's named file is absent from the pinned local Mathlib, so it cannot be recorded as a local match. The grep searches for condensed bar rows and effacement were empty.

For transfer, I read the actual `RepresentationTheory/Homological/GroupHomology/Functoriality.lean`: its corestriction is the covariant homology map induced by a homomorphism, not finite-index cohomological transfer with the required homotopy. I also read `GroupCohomology/Shapiro.lean`: its coinduced representation isomorphism is for discrete Rep and has neither profinite parameter sheaves nor the second differential. Other semantic hits were ordinary group transfer and Rep bar resolutions. The Loogle queries returned no hits; no unavailable service was recorded as absence. No Mathlib leaf is claimed.

## Review by Q62

I read the current latest blueprint direct-image proof, the whole item statement, its parent scalar acyclicity split, and the statements of every node used in the six steps. I checked the Stacks labels in local `homology.tex` against `tags/tags`: Tag 012X is the double-complex section, Tag 0132 is `lemma-first-quadrant-ss`, and Tag 0133 is `lemma-double-complex-gives-resolution`. They justify finite-diagonal spectral machinery only. The two new nodes are agent-formulated analytic and algebraic subclaims at the precise scalar tame-kernel place; their sources explicitly say the exact external references are WANTED. Neither claims to follow a nonexistent numbered theorem.

Step 1 uses `lem-sfb-homogeneous-injective-total-target` for existence and underlying injectivity, and `lem-sfb-profinite-free-hom-resolution-evaluation` for the actual section evaluation, parameter naturality and resolution augmentations. I checked that the latter says these things for every profinite S and P without claiming acyclicity. The bar-derived node provides the compatible model, not a comparison with underived functions. Left exactness here only identifies the kernel in resolution degree zero, and the equivariant augmentation has zero composite with the next resolution differential. Thus the written chain map is the map the item specifies, including the action-dependent first face on I.

Step 2 applies `lem-sfb-normed-scalar-profinite-hom-acyclic` ONLY for finite E. Its statement gives exactly the canonical unit and parameter naturality, which is sufficient for all columns of this same compatible resolution. The total-column comparison has precisely the first-quadrant and column-quasi-isomorphism hypotheses used here. No negative bidegrees or infinite diagonal occur.

Step 3 uses the new local-effacement node for a horizontal cocycle in a positive INTERNAL vertical cohomology sheaf. It does not use the point-evaluated statement as if evaluation were exact. A cohomology section is locally a cocycle because it is the sheaf quotient of cycles by boundaries; restrictions of such representatives agree with the quotient maps. On each finite cover, the new internal transfer supplies the same-resolution identity after vertical and horizontal cohomology. Multiplication by the nonzero finite index has inverse the constant rational scalar in Omega, so the class vanishes there; separatedness of the quotient sheaf then kills the original class. This elementary deduction is written in the parent, not made into a third node. The prime-to-ell assumption is used by the analytic effacement input, not falsely needed for rational scalar invertibility.

Step 4 uses the exact E1/E2 descriptions, functoriality and finite abutment from `thm-sp-double-complex-spectral-sequences`. The row-collapse node states the bottom EDGE is an isomorphism, not just an objectwise existence of an isomorphism. I checked that the map from the row-zero source double complex induces the identity on its bottom E1 row; functoriality and the sole surviving filtration piece identify its cohomology map with that very edge. This verifies invertibility of the specified j rather than an unspecified isomorphism of its source and target. Neither of these cited statements assumes a cohomological-dimension bound or a limit interchange.

Step 5 uses the full statement of `lem-sfb-condensed-bar-total-naturality`, which explicitly provides equivariant resolution lifts, uniqueness after localization, the total homotopy sign and inverse comparison maps. I checked the augmentation equation on every source summand. Underlying exactness and injectivity are supplied in step 1. The item does not need a new resolution-choice theorem.

Step 6 is a written calculation using the bar normalization statement. In degree zero the only component is the original resolution augmentation. I recomputed the trivial-group signs: the scalar differential is 0 in even degrees and 1 in odd degrees, and h is 1 in positive even degree. Thus dh+hd is the identity off degree zero, including degree 1; commuting with the resolution differential cancels the signed vertical cross terms. This is an elementary parity calculation, not a hidden analytic lemma. The resulting map is the ordinary resolution comparison required by the item.

For the local-effacement node I checked q>0 is explicit and p=0 means the restricted section must vanish; the degree-minus-one module is zero. For finite G one may choose H=1: its positive vertical cohomology is zero internally because the underlying resolution is exact, so the claim has the expected easy case. For G=1 this applies directly. The empty S has zero section modules. These checks do not prove the general analytic statement; it remains an honestly unsplit input. In particular local primitives on a parameter cover are not silently strengthened to global primitives.

For the transfer node I checked H=G admits t=id and h=0, the zero ring/complex gives zero maps, and finite G with H=1 has the usual sum over finitely many cosets. The maps are required before both cohomologies, so commuting with the vertical differential is part of the stated obligation, not an unmentioned assertion in the parent's proof. The lemma allows an arbitrary nonnegative equivariant complex and arbitrary condensed ring; it introduces neither injective coefficients nor an unstated topological realization of them.

Against delivery-errors B through E: both new nodes are self-contained statement-only JSON records with definition dependencies, single-escaped TeX, empty proof/dependency lists, fresh IDs, blueprint places and actual three-kind search records. No Mathlib match or line number is invented. Whole-DAG, whole-blueprint and project-source duplicate searches were performed before creation; the nearest related statements are distinguished above. Every use is quoted verbatim in citations.json. Non-elementary operations are supported by cited result statements rather than definitions or their proofs. No new lemma restates the total comparison. The finite-index inversion, sheaf-local quotient reasoning, bottom-edge identification, equivariance and sign conditions were checked explicitly. All six proof steps are under 1000 characters, so none reaches the 2000-character long-step threshold. The three generic spectral tools from other units are declared in split_report.tool_uses; no chapter route, target statement or definition was changed. No SGA source is cited.

## Unfinished work

No stage-1 assembly work remains. The two new lemmas remain unsplit and need their own later workers; in particular this delivery does not claim to have proved the analytic effacement input or to have removed Lean sorries. The required server checks and delivery preflight are run by the authorized delivery commands.
