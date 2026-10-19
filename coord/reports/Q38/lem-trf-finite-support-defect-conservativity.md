# Q38: lem-trf-finite-support-defect-conservativity

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-support-defect-conservativity.json`: existing statement, now split into four proof steps; statement and hypotheses unchanged; no new nodes or Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every cited node in every step.
- No Lean files, unit records, live repository files, or compiler/build outputs were written.

## Attachments

None. I searched the exact blueprint tag and the key phrases in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; no finished declaration states this item. The source checkout is reference-only and has no matching declaration.

## WANTED

None. The cited Varshavsky PDF is present locally. The finite direct-image and stalk inputs are existing DAG nodes with Stacks sources.

## Issues found and repaired

The imported item had an empty proof and status `unsplit`. Its statement is mathematically correct, including the empty-support case and the isomorphism-reflection clause. I did not alter its statement, dependencies, or source. No `STATEMENT-DISPUTED` issue was found. The proof now expands the §3.2.4 finite-support argument rather than treating the target as a one-line restatement. Existing nodes supply all auxiliary facts, so creating another support or finite-stalk node would duplicate the DAG.

## Not duplicates

There are no new nodes. I searched the whole DAG and blueprint for closed-support reconstruction, finite direct-image conservativity, finite-support pushforward, and the relevant Stacks tags. `lem-cbc-open-closed-recollement` already supplies the supported-complex reconstruction triangle; `lemma-weil-pbc-finite-direct-image-exact` and `lemma-weil-pbc-finite-stalk-formula` already supply exactness and the finite-fibre stalk formula. The delivered item combines these existing tools and does not restate either node as a new child.

## Mathlib searches

The inherited item searches were retained after reading their results. They comprise LeanFinder, Loogle, grep, and LeanSearch searches for derived direct-image conservativity and finite-support stalk formulas, all with no matching Mathlib theorem. In this continuation I also ran the required msearch commands for the item's closed-support/finite-direct-image phrasing: LeanFinder returned only ideal-sheaf and module pushforward infrastructure; Loogle's `Sheaf.pushforward` and namespace queries were unknown identifiers; LeanSearch returned generic faithful pushforward instances; grep found only ideal-sheaf support declarations. None states the etale derived assertion. These results are recorded by `msearch.py`; no Mathlib leaf is claimed.

## Review by Q38

I read the item, chapter `sec-trace-formula`, unit `sk-i-curve-zero`, the inherited blueprint ancestor `lem-trf-local-term-locality`, the Varshavsky PDF §3.2.2(I) and §3.2.4, and the complete statements of every cited node. The source's finite-projection paragraph says that a defect supported on a closed subset finite over the projection base vanishes after finite direct image; the DAG statement packages the corresponding general derived conservativity assertion. I checked all hypotheses: `i` is closed, `f=h∘i` is finite, `A` is finite, and every cohomology stalk outside `i(V)` is zero. No properness or smoothness hypothesis was added.

Step 1 uses `lemma-weil-pbc-geometric-stalk-conservative` for the vanishing of the restriction to the open complement and `lem-cbc-open-closed-recollement` for the functorial triangle and exact closed direct image. Their statements say exactly those facts. Exact inverse image then gives the derived restriction vanishing, so the triangle gives `K ≅ i_*i^{-1}K`; this is the support reconstruction needed later.

Step 2 uses the canonical derived pushforward composition comparison `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, the exact closed image clause of the recollement node, `lemma-weil-pbc-finite-direct-image-exact`, and the faithful exact forgetful functor of `lem-weil-pbc-module-sheaves-colimits-forgetful`. The direct-image section formula is the same after forgetting coefficients, so abelian exactness transfers to finite `A`-module sheaves. `lem-weil-pbc-exact-functor-derived-functor` then supplies termwise computation and the displayed cohomology formula. I checked that the composite in the composition node is instantiated with `i` followed by `h`, hence is exactly `f`.

Step 3 uses the exact finite-fibre formula of `lemma-weil-pbc-finite-stalk-formula`: every geometric point of `V` lies in the finite fibre over its image in `S`. A zero finite product forces each factor to vanish, and the cited stalk-conservativity node turns this into vanishing of each restricted cohomology sheaf. The converse is functorial. Empty fibres and `K=0` were checked explicitly.

Step 4 applies the cone criterion. The long exact cohomology sequence shows the cone of a map between supported complexes remains supported on `i(V)`. The Mathlib leaf `lem-sf-exact-functor-derived-triangulated` states that termwise exact derived functors are triangulated, so the cone vanishing equivalence is exactly equivalent to reflection of isomorphisms. This step does not assume that either input map is an isomorphism.

I verified every citation quote in `citations.json` against the node files, and every proof dependency is the union of the step uses. The seven off-unit generic tools are declared in `split_report.tool_uses`; no route-specific lemma was silently substituted. No cycles, hidden clause nodes, SGA 4 citations, or steps over 2000 characters were introduced. Small cases checked were `V=∅`, `W=V` with `h` finite, a skyscraper sheaf over a point, and a cone of a non-isomorphism. No source or statement correction was necessary.

## Unfinished work

None in the split. The mandated server dry run and delivery remain to be run.
