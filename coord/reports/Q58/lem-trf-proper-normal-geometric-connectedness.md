# Q58: lem-trf-proper-normal-geometric-connectedness

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proper-normal-geometric-connectedness.json`: split statement; no exact Mathlib match. Six proof steps, all dependencies reused.
- `citations.json`: 17 verbatim statement quotations for every step/node citation.
- `searches.jsonl`: actual search-command results, including exploratory searches whose candidates were superseded by existing DAG nodes.

New nodes: 0. New Mathlib leaves: 0. No Lean written or compiled.

## Attachments

None. Searched the project Lean source by the item id, 0AY8, Zariski connectedness, Stein factorization, and geometric-fibre language. HenselianConnectedness.lean treats henselian bases, not arbitrary normal integral bases, and its connectedness theorem contains sorry. GammaSpecAdjunction.lean only constructs the affine factorization. Neither is an exact attachment.

## WANTED

None.

## Findings and changes

The imported statement agrees with all six hypotheses and both conclusions of Stacks 0AY8, lemma-geometrically-connected-fibres-towards-normal, in more-morphisms.tex. Its statement and statement dependencies were retained exactly. The source's phrase finite (or even integral) in Morphisms 0AB1 matters: the existing lem-trf-finite-birational-normal-iso only states the finite case and cannot be invoked for this non-Noetherian problem. Instead the proof writes the integral-closure argument on affine opens using the existing general ring-normality criterion. This is the affine algebra of the source's integral-birational-normal argument, not a different unit route.

There is no previous item copy or split in this sandbox. Existing Q41 provenance, blueprint ancestry, and original Mathlib-search records were retained. Additional searches were really run with msearch.py and appended from its log. Search results about integral schemes or normalizations do not prove connectedness with this reduced, potentially reducible source; Geometrically/Connected.lean only derives fibre instances after assuming GeometricallyConnected. Exploratory searches for generic-point injectivity and affine normality became unnecessary when the DAG supplied the existing inputs. No new node was created for these elementary consequences.

The item is a descendant of lem-trf-local-term-locality, not the key statement of its unit; no unit record is changed. Read the chapter and sk-i-curve-zero records and the current main-20261015 ancestor. This is the already-recorded auxiliary Zariski connectedness input in the exceptional-tree/nearby-cycle branch. Blueprint-wide connected-fibres, normality, and irreducible-component searches gave no second blueprint statement of this exact theorem; same_as stays empty. All new proof dependencies were checked for paths back to the item; none exists.

One inherited graph issue was observed while reading the transitive Stein dependencies: def-weil-pbc-ideal-module-product-stalk is missing in this local shared snapshot. This delivery does not introduce or edit that edge. The required server delta/preflight decides against its actual baseline.

## Not duplicates

No new nodes, so no new/existing pairs require comparison. In particular the general existing lem-sc-irreducible-components-cover was found and reused instead of making a topology leaf. The generic-section detection argument is written in the item's Step 4, and the normal-domain specialization of the existing general ring criterion is written in Step 2.

## Review by Q58

I read the full statement and proof of Stacks 0AY8 and the general Stein theorem 03H2, not its Noetherian analogue. I also read Morphisms 0AB1 including its explicit integral variant, the reducedness and generic-point paragraphs 0AXN/normalization-generic used by 0AY8, Algebra 030C and its normal-ring integral-closure implication, Schemes 01HV for affine stalks, Schemes 01IS for sobriety, Topology 004W(3)--(4) for component coverage, and the vanishing-section paragraph of 03GY. There are no new-node sources to audit.

For Step 1 I opened the statements of proper-fp-permanence, qcqs-over-affine, reduced-scheme, integral-scheme, and spec-domain-stalks-function-field. They respectively give base change of properness, the actual qcqs conclusion needed for Y, reduced section rings/local rings, domain affine rings, and both the affine-stalk and fraction-field identifications. A nonempty affine in integral S contains its generic point, so its generic fibre really is the given X_xi. No quasi-compactness of S or Noetherianity is used.

For Step 2, the spec-domain-stalks statement gives all A_p, not merely the generic stalk. The normal-ring definition therefore has exactly the stalkwise hypothesis supplied by S. The existing reduced-normal-total-fractions statement gives (1) implies (2). Its finite-minimal-primes assumption is satisfied because a domain has exactly one minimal prime, even when A is not Noetherian. Its total fraction ring is precisely K. This avoids using the inadequate finite-only 0AB1 node.

For Step 3, I read the complete statement of stein-factorization-affine. It gives integrality, properness, and geometric connectedness for an arbitrary commutative ring A. It does not promise finiteness, and the split never takes finiteness from it. The map r is the canonical restriction, followed by the assumed equality as K-algebras; no flat-base-change comparison is silently used.

For Step 4, component coverage holds for every topological space and sobriety for every scheme, with no finite-component assumption. Their statements supply a component through any chosen point and its generic point. Since Y is open that generic point lies in Y. Dominance of every component, an explicit hypothesis of the item, puts it over xi. I checked the factorization through the generic fibre using the residue-field map and the fibre-product definition. A section's residue-zero locus is closed by its affine V(h) description, so it contains every specialization of that generic point. The nilpotent-section lemma is applied only after checking residues vanish at all points and Y is quasi-compact; reducedness then kills the nilpotent. A section need not have zero germ merely because it has zero residue: the proof never makes that false inference.

Step 5 uses only the preceding integrality, injectivity, and integral-closedness assertions. Applying r to a monic equation puts r(b) in A; injectivity then gives b in the structural image of A. I wrote the two-sided inverse sheaf gluing on affine opens, including the empty open and nonaffine intersections. Step 6 uses the affine-spectrum functor and the exact geometric-connectedness clause of the existing Stein node. Under the structural ring isomorphism, the field map to Spec B is the one induced from the chosen Spec L to U. Its fibre is the original base-changed fibre by the universal property, so both connectedness and nonemptiness follow. Every node quoted by every step has its actual statement copied verbatim to citations.json.

I checked B--E of delivery-errors.md: the statement is unchanged and self-contained, source tags/labels are named, no new unsplit node hides a proof, no new elementary/duplicate/restatement node was made, and all non-elementary facts are direct statement citations. The generic-restriction and integral-closure arguments are written explicitly. Every step is below 2000 characters. The three off-unit non-leaf tools are proposed in split_report.tool_uses; they are generic tools, not replacements of the local-term unit. The normal criterion and Stein inputs have no dependency path back to this item.

Small cases: f the identity on any normal integral scheme gives B=A directly; a proper geometrically connected variety over a field with H0 equal to the field gives the same calculation. Empty X cannot satisfy H0(X_xi)=K as K-algebras. A nontrivial finite field extension fails that generic-section hypothesis. A disjoint vertical component violates the component-dominance hypothesis and would invalidate Step 4, so it is correctly excluded. Nilpotents would break the last step of section detection and are correctly excluded. Non-Noetherian normal valuation bases still satisfy the domain/minimal-prime argument, so the proof has not inserted a hidden Noetherian or finite-presentation assumption.

## Unfinished work

None in the requested one-level split. Existing unsplit dependencies remain the maintainer's queue items.
