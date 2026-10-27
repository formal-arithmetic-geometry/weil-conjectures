## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-quasiseparated-space-etale-specializations.json`: item, split into seven steps, statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-qs-affine-chart-point-fibres.json`: one new statement-only prerequisite, unsplit; no Mathlib match.
- `citations.json`: the verbatim statement used for each node citation of each numbered step.

Attachments: none. Searches of `lean/WeilConjectures/` by the item id, algebraic-space terminology, and specialization/generalization terminology found no declaration proving every clause. The scheme flat-generalizing theorem is a Mathlib leaf already represented in the DAG; it does not prove the algebraic-space statement.

WANTED: none. All mathematical sources used are local Stacks sources. No SGA route is used. No Lean was written and no compiler or build command was run.

The imported item had no proof. Its statement is correct, including a relative quasi-compact diagonal over an arbitrary scheme S; I did not replace this with absolute quasi-separatedness or assume S quasi-separated. The only new node supplies finite *point-set* fibres of an affine chart and its relation under precisely this relative input. The item itself proves continuity, lifting at the prescribed point, and noncollapse. Neither clause has been moved into a new node.

The source proof for lifting first constructs some point over the specialization and then moves the lift to the prescribed chart point. The delivery makes the saturation already proved in that source explicit: membership of u in the saturated closed set immediately supplies a generalization of that very u. This is the same finite-fibre closure argument, with its final transfer shortened by elementary set theory.

Nothing remains unfinished in this one-level split; the new prerequisite intentionally remains statement-only for a future stage-1 worker.

## Sources and blueprint searches

I read `decent-spaces.tex`: Tag 03JX (`lemma-bounded-fibres`), in particular the implication from Zariski local quasi-separatedness to condition gamma; Tag 03JV (`lemma-UR-finite-above-x`), condition (1); Tags 03IM (`lemma-no-specializations-map-to-same-point`) and 03K2 (`lemma-specialization`), including their proofs; and the short applications Tags 03K5 and 03IL. I also read `spaces-properties.tex` Tag 03W7 (`lemma-quasi-separated-quasi-compact-pieces`), statement and its relative-to-absolute local comparison. These prove the new node without any global assumption on S: relative quasi-separatedness implies Zariski local absolute quasi-separatedness, then 03JX gives gamma, whose affine-chart finite-fibre formulation is 03JV (1). The extra condition that W maps into an affine open of S is available in our application and makes the original relative-diagonal construction transparent; it does not assert that W is affine over S.

For the item I followed the proofs of 03K2 and 03IM, rather than taking the final clauses 03IL and 03K5 as new nodes. The chapter and unit records were read. This node is a supporting point-topology input to the dimension comparison down the existing alteration/moduli branch, not a change to the six-functor theorem or its route. I read the latest blueprint `sec-six-functors/sk-thm-sf-kunneth-verdier/thm-sf-ctf-stability.proof.md`. The old detail label in the inherited provenance is historical; the current blueprint does not contain a separate node stating these point-topology facts. `blueprint_refs.py ancestor` returns null for this inherited chain, and that value is preserved, with the actual place and full via chain in the new node.

Before writing the new node I searched the entire DAG for 03JX, 03JV, 03JS, 03W7 and their key words, and read the statements of all candidates listed below. Whole imported-blueprint searches for `finite fibres`, `specializations`, `generalizations`, `quasi-finite`, `etale chart`, `finite point`, 03JS, 03JV, 03W7 and 03JX found no matching blueprint statement. Scheme finite-fibre and Galois-category statements do not apply to the point-set quotient of a space. Project-source searches found no corresponding space declaration.

The Mathlib searches ran only through msearch.py, and their query strings and results are recorded in the node and searches.jsonl. Two different LeanFinder descriptions, LeanSearch, Loogle and Mathlib grep were used for the prerequisite. Hits include `Scheme.Etale`, scheme finite fibres, scheme quasi-separated diagonals, and generic site structures, not the stated algebraic-space theorem. The flat-morphism search returned `AlgebraicGeometry.Flat.generalizingMap`, already attached to `lem-weil-pbc-flat-generalizations-lift`. A second phrasing was used before concluding absence. Interrupted search processes had finished and their logged results were read; they were not replaced by invented searches.

## Review by Q08

I reread the unchanged item against 03IL and 03K5: the relation is x generalizes a(u), the lift must generalize the specified u, and comparable points with equal image must be equal. Continuity comes directly from the final-topology definition. The relative/absolute issue is handled by 03W7 in the new finiteness prerequisite. There is no extra surjectivity, finite-type, local-Noetherian or quasi-compact-source hypothesis on the original chart.

Step 1 uses the actual final-topology definition, the affine-open basis theorem, and the open-immersion/composition clauses of `lem-weil-pbc-etale-composition-cancellation`. The statement of `def-trf-algebraic-space` tests representable etaleness by scheme pullback; `lem-trf-space-fibre-products-etale-covers` supplies the sheaf products and scheme representability. Thus the projections R to W really are etale scheme maps. The affine-base reduction uses only continuity of the structural scheme map and an affine neighbourhood inside its inverse image. Every original generalization of u remains in W, so this reduction is valid for both conclusions.

Step 2 uses flatness from the etale definition and the exact generalization-lifting assertion of the existing flat leaf. I checked its Mathlib declaration is a generalizing, not a specializing, map, so the direction is correct. The fibre-discreteness node says the entire scheme fibre is discrete, while `def-pc-scheme-fibre` explicitly says its topology is the subspace topology of the set-theoretic fibre. Both facts are necessary to infer equality of comparable points in one projection fibre. The scheme sobriety node gives uniqueness of the generic point of a singleton closure, which gives antisymmetry; no sobriety of X is assumed.

Step 3 invokes the new prerequisite with this same W, X and S. W is affine and maps into an affine base open by step 1. Its two conclusions give exactly finite A and B, not merely finite fibres of R over W. Consequently C and D are finite unions of singleton closures. Finiteness is the non-elementary input; the closed-set construction is elementary and includes the empty case.

Step 4 uses the flat lifting theorem at a specified r and the specified generalization of s(r). The resulting r-prime has image x in X and hence lies in B. This proves the reverse inclusion in s-inverse(C)=D; continuity proves the forward one, and the same proof works for t. The point-calculus node explicitly states surjectivity of the map from points of a sheaf product to pairs of points with equal image. That is the clause used for saturation; mere existence of categorical fibre products would not suffice. This step does not cite the proof of any node.

Step 5 uses openness and continuity from that same point-calculus statement. The restriction W to its point image I is an open surjection. Because C is saturated, the displayed identity I minus p(C)=p(W minus C) proves closedness directly. Since I is open and contains the special point, it contains x. Closedness within I suffices: no image subspace or global surjectivity of W to X is assumed. Membership of u in C, not just existence of some point over p(u), finishes the required lifting at u. This is an elementary consequence of the preceding saturation and the cited open-map property.

Step 6 sets up the recursion with t(r_n)=v_n and s(r_n)=v_(n+1), explicitly constructs r_(n+1) by lifting along t, and defines v_(n+2). Point-surjectivity supplies r_0; the new node supplies the finite fibre in which all v_n lie. I checked the recurrence preserves both the specialization direction and the common image y, so it is not an informal appeal to induction. Only the scheme projections are used for flat lifting.

Step 7 propagates an adjacent equality backwards using discreteness of an s-fibre from step 2 and then applying t. Antisymmetry of the scheme's specialization relation rules out a non-adjacent repeat in an otherwise strict chain. Thus a distinct initial pair produces infinitely many distinct points of the finite set in step 6, a contradiction. This last finite-poset argument is elementary and uses only consequences already established in earlier steps.

For the new node I checked B1-B9: it introduces S, X, W, R, the projections and all finiteness hypotheses; defines quasi-compactness on tests; cites the actual scheme, space, point-topology, affine-spectrum, etale and product notions; has TeX written once, statement only, no proof sketch, empty proof dependencies, and a source with the actual labels and tags. It is a finiteness input, not either conclusion of the item. The comparison with the existing uniform geometric-bound node is especially important: that node assumes absolute quasi-separatedness, while our item assumes only a relative quasi-compact diagonal over arbitrary S.

Small-case checks: if W is empty both fibres in the new node are empty; points outside the image also have empty fibres. For X=Spec k and a finite separable affine chart, A is the finite point set and B has the expected finite arrow set, so the statement does not mistakenly bound B by the size of A. If the original U is an infinite disjoint union of etale field spectra, the item still applies after affine shrinking although U has infinite fibres; the new finiteness assertion is only applied to affine W. For an identity chart of a scheme the lifting is the given generalization and noncollapse is immediate. The recursion handles the reflexive specialization because equality simply propagates backwards. An arbitrary non-quasi-separated base is permitted since 03W7 is a local statement.

Corrections made during the self-reading: I avoided applying the existing absolute quasi-separated geometric-bound lemma under a relative hypothesis, and made the closure descent and equality propagation explicit. I reused the existing flat lifting and discrete-fibre nodes instead of creating scheme-specialization lemmas. Every cited statement has been opened and copied verbatim to citations.json. Every step is below 2000 characters, and no long-step lemma is hidden. The two cross-unit uses (space point calculus and scheme etale fibre discreteness) are declared as generic tools in split_report, with their precise purpose; the maintainer decides acceptance. There was no prior returned delivery and no independent second reader is claimed.

## Not duplicates

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-space-topological-dimension-local-rings: states equality of topological dimension with local-ring dimensions, not finiteness of point fibres of an affine chart and its relation.

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-quasiseparated-space-sober: states sobriety of the space, not affine-chart fibre finiteness.

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-quasiseparated-space-atlas-dimension: states equality of dimensions for an atlas over a field, not finite fibres over an arbitrary relative base.

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-space-etale-maximum-degree: requires a separated finite-type space over an affine base and a surjective chart and describes a maximal degree locus; our finiteness input assumes no finite type or surjectivity.

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-quasiseparated-space-dense-scheme-open: gives a dense open scheme subspace; it gives no finite-chart-fibre assertion.

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-quasiseparated-space-etale-specializations: states continuity, lifting of generalizations and noncollapse; the new node states only finite point fibres of an affine chart and its relation, used in the actual closure and tower proofs.

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-space-etale-atlas-topological-dimension: states dimension equality after base change for a surjective atlas, not the finite point sets used in the specialization proof.

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-decent-space-finite-field-map: assumes decency and proves a field-valued morphism finite under a closed-point and finite-extension hypothesis; it neither derives decency from the relative diagonal nor states finite chart/relation point fibres.

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-locally-separated-space-decent: requires an absolute diagonal which is an immersion and states quasi-compactness of field-valued maps; the new node assumes only a quasi-compact relative diagonal, not a locally separated space.

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-qs-space-rational-point-topology: states injectivity and closedness for K-rational points over a field, not finiteness of chart/relation fibres.

lem-sfb-relative-qs-affine-chart-point-fibres vs lem-sfb-space-qc-etale-fibre-bound: assumes absolute quasi-separatedness and bounds geometric fibres of a quasi-compact chart uniformly; the new node works with a relative diagonal over arbitrary S and gives finite point fibres of W and its relation. The absolute hypothesis of the existing node is not present here, so it is not a direct specialization.
