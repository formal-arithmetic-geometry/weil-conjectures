# lem-sfb-finite-model-stratum-filtration

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-model-stratum-filtration.json` — item restored from the shared DAG and split into seven proof steps; no new nodes and no Mathlib leaves.
- `citations.json` — verbatim statement quotes for every cited node in every step.
- `searches.jsonl` — the six Mathlib searches run for this item.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the upstream reference for the item id, its proposed blueprint tag, and the key finite-model/stratification phrases; no finished declaration states this item.

## WANTED

None.

## Problems in the node, blueprint, or brief

The sandbox initially lacked the assigned node even though the shared DAG contains it; I restored the shared copy before editing. The imported node had no proof and inherited a stale `created` record from another worker, which I retained as history while filling the stage-1 split fields. No statement correction was needed. The item deliberately assumes only a Noetherian underlying topological space; the proof therefore uses topological Noetherian induction and qcqs consequences, without adding local Noetherianity, finite type, separatedness, or local freeness.

## Unfinished work

None. The required server `check_dag` preflight passed after the node was restored. The final `deliver.py --no-push` dry run passed with `OK (not pushed)` after the citation quotes were expanded to exact full statements.

## Review by NB

I read the item node, the fixed chapter `sec-six-functors-basics`, the assigned unit `sk-def-sfb-dc-restricted-functors`, the constructibility definition `sk-def-sfb-constructible`, and the source passages Stacks Topology Tag 09Y5 and pro-étale Tags 09AA, 09AH, 09BN, and 03DI–03DJ. I also read the existing statements of every cited node: `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` supplies the minimal closed subset needed to terminate the 09Y5 induction; `lem-weil-pbc-reduced-induced-closed-subscheme` supplies a reduced closed subscheme on each closed stratum; `sk-prop-sfb-cartesian-coefficients` identifies all coefficient inverse images; the module upper-star, lower-shriek, and lower-star definitions identify the functors used; and `lem-weil-pbc-proetale-ringed-open-closed` supplies exactness, the counit short exact sequence, and the open/closed restriction identities.

Step 1 is exactly the finite-stratification and finite-constant-local-model clause of `sk-def-sfb-constructible`. Step 2 expands Tag 09Y5 rather than citing a new node that would merely restate an item clause; the cited minimal-condition statement is used only for termination. Step 3 checks the good-stratification order, proves that maximal-first prefixes are open, and applies the cited reduced-subscheme construction; it also checks quasi-compactness and quasi-separatedness directly from the Noetherian topology. Step 4 checks that every refined stratum lies in an original stratum and that pulling back a scalar finite presentation preserves the finite constant local-model condition, with the coefficient comparison supplied by the cartesian-coefficients statement. Step 5 applies the cited ringed localization sequence to each `v_k` and verifies the qcqs hypothesis established in Step 3; the cited module definitions say exactly what `v_k^*` and `v_{k!}` mean. Step 6 applies the same sequence inside each `V_k`, uses the exactness stated for open extension, and spells out the elementary equality of extension-by-zero along a composite of opens; the cited lower-star definition supplies the meaning of `(t_k)_*`. Step 7 checks naturality directly from the counits, restrictions, and canonical extension-by-zero maps.

I tested the edge cases `X=\varnothing` (empty partition, `r=0`), `r=1` (the single counit is an isomorphism), and a two-stratum dense-open/closed-point example. The argument never uses local Noetherianity of structure sheaves, finite type over a field, or local freeness, so integral torsion finite presentations remain allowed. The Mathlib search results only concern algebraic filtrations, finite generation, or Noetherian instances and do not state this constructible sheaf filtration. The first delivery preflight rejected several citation quotes for being shorter than its minimum evidence length; I repaired `citations.json` by using the exact full statement for every cited node, and the subsequent dry run passed.

## Second reading by NB

- Step 1 checked against the constructible definition in the main-20261015 blueprint and the Noetherian-topology compactness leaf; the qcqs prerequisite is now established before unpacking constructibility.
- Step 2 checked line by line against Stacks Tag 09Y5 and Tag 0052; the recursive partition pieces, strict closed remainder, component choice, and termination argument now match the source under only topological Noetherianity.
- Step 3 checked against the good-stratification order calculation, Tag 09Y5, the reduced-closed-subscheme node, and the compactness leaf; maximal-first prefixes, reduced strata, and qcqs conclusions are explicit.
- Step 4 checked against the constructible and cartesian-coefficient statements; pullback of the finite scalar presentation and allowance for torsion are exactly justified.
- Step 5 checked against the ringed pro-étale localization statement and the reduced-complement construction; the required closed complement and quasi-compact open hypotheses are now supplied.
- Step 6 checked against Tags 09AH and 03DI--03DJ and all three module-functor definitions; the short exact sequence and composite extension-by-zero calculation are stated explicitly.
- Step 7 checked naturality against the counit, restriction, and extension-by-zero maps in the localization sequence; the induced quotient isomorphisms are functorial for fixed strata.
- New Mathlib leaf `lem-sfb-noetherian-space-compact-subsets` checked against Stacks Tags 0051 and 04ZA and `TopologicalSpace.NoetherianSpace.isCompact` at Mathlib/Topology/NoetherianSpace.lean:65, with the DCC equivalence recorded at lines 81--92.
- New Mathlib leaf `lem-sfb-noetherian-component-open` checked against Stacks Tag 0052(3) and `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent` at Mathlib/Topology/NoetherianSpace.lean:203.

Changes made: replaced the inapplicable scheme-level minimal-closed-subsets citation (which required local Noetherianity and quasi-compactness) with the two exact topological Mathlib leaves; corrected the Tag 09Y5 refinement to split each old stratum into the source's three pieces; established qcqs before using the global constructible definition; supplied a reduced closed complement before the localization application; regenerated all citation quotes; and repaired every malformed LaTeX escape in the proof JSON. I tested the empty scheme ($r=0$), the one-stratum case (the counit is an isomorphism), and a two-stratum dense-open/closed-point example; no statement correction was needed.
- The existing Mathlib leaf `lem-sc-irreducible-components-cover` is used as a generic cross-unit tool only to choose an irreducible component through a point; this unit has no component-cover node, so the maintainer should record that tool use at landing.

## Not duplicates

- `lem-sfb-noetherian-component-open` vs `lem-sbc-constant-local-dimension-components`: the existing node concludes a dimension equality under local Noetherianity; this leaf gives a nonempty open inside each irreducible component from only topological Noetherianity.
- `lem-sfb-noetherian-component-open` vs `lem-sc-locnoeth-components-locally-finite`: the existing node asserts local finiteness of components for a locally Noetherian scheme; this leaf asserts the Tag 0052(3) open-subset property under the weaker topological hypothesis.
- `lem-sfb-noetherian-component-open` vs `lem-sc-components-open-injection`: the existing node concerns the injective map of components under an open inclusion; this leaf produces a nonempty ambient open contained in one component.
- `lem-sfb-noetherian-component-open` vs `lem-sc-affine-noetherian-underlying-space`: the existing node derives Noetherianity for an affine scheme from a Noetherian ring; this leaf uses an already Noetherian underlying topology and proves the component-open fact.
- `lem-sfb-noetherian-component-open` vs `lem-weil-pbc-noetherian-open-subscheme-noetherian`: the existing node assumes a locally Noetherian quasi-compact scheme and concludes an open subscheme is Noetherian; this leaf has no local Noetherian or scheme quasi-compactness hypothesis and concludes Tag 0052(3).
- `lem-sfb-noetherian-component-open` vs `lem-weil-pbc-irreducible-refinement-topological`: the existing node asserts existence of an irreducible refinement of a finite stratification; this leaf states the nonempty-open-in-component input used by the Tag 09Y5 induction.
- `lem-sfb-noetherian-component-open` vs `lem-sc-noetherian-finite-irreducible-components`: the existing node states finiteness of the component set; this leaf states that each component contains a nonempty open.
- `lem-sfb-noetherian-space-compact-subsets` vs `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`: the existing node gives a minimal closed subset only for locally Noetherian quasi-compact schemes; this leaf gives compactness of every subset from the weaker topological Noetherian condition.
- `lem-sfb-noetherian-space-compact-subsets` vs `lem-weil-pbc-noetherian-open-subscheme-noetherian`: the existing node concludes local Noetherianity and quasi-compactness of an open subscheme under scheme-level Noetherian hypotheses; this leaf gives the topological compactness theorem needed for arbitrary opens and closed strata.

Further checks in the second reading: the original step 4 and step 5 cited `sk-prop-sfb-cartesian-coefficients`, whose quantified assertions are restricted to admissible coefficients although this item allows any commutative condensed ring. I replaced that citation by the existing `lem-sfb-alpha-iso`, which is quantified over every condensed ring. Step 4 now explicitly constructs the map from each reduced new stratum to its original (possibly nonreduced) stratum, using `lem-weil-pbc-reduced-source-factors-through-closed-subscheme`, checks pullback composition, and pulls back the finite matrix using the covering/colimit and strong tensor statements. This repairs the set-theoretic-factorization gap rather than inferring scheme factorization from subset inclusion. Step 5 identifies internal module objects with ordinary sheafwise modules and compares the two extension-by-zero functors through their common lifted adjunction. The Noetherian qcqs conclusion is now checked directly from diagonal preimages, with no uncited affine-intersection criterion. The proof of goodness spells out the closures of the new open and all inductive strata.

These additional cross-unit statements are generic tools: `lem-weil-pbc-reduced-source-factors-through-closed-subscheme` supplies reduced-source factorization, and `def-weil-pbc-internal-abelian-sheaf-module-equivalence` identifies the internal module convention with the localization theorem's convention. The unit has no substitute for either. I removed the first worker's nested `split_report.tool_uses` proposal; the differences and reasons belong here for the maintainer to record. I also corrected the first worker's rejected Loogle queries to verdict `unavailable`; their actual parser errors remain recorded, and none is treated as evidence of absence. Both new leaves are statement-only, self-contained, with the appropriate definition citations, Stacks tags and labels, exact declarations/files/lines, and the actual LeanFinder/Loogle/grep searches. Whole-blueprint and existing-DAG searches found no identical statement; every same-tag candidate has been read and distinguished in `## Not duplicates`.

Small-case checks additionally include an affine spectrum of a field and $\operatorname{Spec} k[\epsilon]/(\epsilon^2)$ with its reduced stratum: the reduced-source factorization supplies the needed comparison without assuming that the original stratum is reduced. The scalar zero module and the zero coefficient ring are allowed; a finite presentation may have zero rows or columns, and all displayed exact sequences still apply. The item statement is unchanged.

For step 6 I replaced the presheaf-composition assertion by the explicit two-adjunction Hom calculation, citing module pullback composition. The resulting comparison carries the composite counit to the original counit (both transpose the identity), so the new short exact sequence really gives inclusions of the prescribed counit subobjects of $F$.
