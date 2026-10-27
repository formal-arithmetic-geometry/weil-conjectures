# Q97: lem-sfb-space-topological-dimension-local-rings

## Files written

- Item: `dag/nodes/sec-six-functors-basics/lem-sfb-space-topological-dimension-local-rings.json`, statement, split, no Mathlib match.
- New: `lem-sfb-quasiseparated-space-sober`, statement-only, unsplit, no Mathlib match.
- New: `lem-sfb-quasiseparated-space-etale-specializations`, statement-only, unsplit, no Mathlib match.
- `citations.json`, `searches.jsonl`, and this `report.md`.

## Attachments

None. Whole-project searches for the item id and algebraic-space dimension, sobriety and specialization terminology found no matching project declaration. Scheme results do not attach to these algebraic-space statements. No Lean was written or compiled.

## WANTED

None.

## Findings and changes

The statement is correct and unchanged. Chart local-ring dimension is not the dimension of neighbourhoods: an integral curve's generic point has local ring dimension zero, while its open neighbourhoods can have dimension one. The first draft cited the existing atlas-dimension node. During work another group landed that node using this item, and the server dry run correctly rejected the resulting cycle. I removed that citation and followed the proof of Stacks 0A4J directly: compare strict specialization chains in an atlas and the space, then apply the scheme local-ring supremum theorem. This requires two new point-topology prerequisites, neither of which states any dimension equality or a clause of the item. Both are left statement-only.

I read the chapter and unit records, the three blueprint levels in SETUP, and the current latest direct-images proof (3). This supporting descendant realizes the inherited dimension conversion for the Tag 0ADD branch; no unit or chapter route is replaced. The ancestor tool prints None, as already recorded in blueprint.from.node; inherited metadata is retained. Whole-blueprint searches for dimension local ring, local ring, etale dimension, dimension, topological dimension, specialization, sober, 0A4J, 0BAN, 03IL, 03K5 and 03K6 found no imported node stating a new prerequisite. Whole-DAG tag and statement searches found only scheme sobriety and finite-groupoid orbit incomparability, which do not imply the general algebraic-space results in one line. These existing statements were opened. The latter assumes finite source and target maps of a groupoid; an arbitrary etale atlas here is not finite.

Mathlib searches for the item and both new nodes were run through msearch.py and their hits read. The new prerequisites share queries explicitly asking for sobriety, lifting and noncollapse on quasi-separated algebraic spaces, with a second semantic phrasing. Results are scheme sobriety, generalizing scheme maps, or definitions; no algebraic-space theorem matched. The grep hit Scheme.ringKrullDim_stalk_eq_coheight at Mathlib/AlgebraicGeometry/Properties.lean:376 was read and is scheme-only. Earlier searches on the imported item are retained. No unavailable service was reported as no match.

## Not duplicates

lem-sfb-quasiseparated-space-sober vs lem-sfb-space-topological-dimension-local-rings: the new node asserts existence and uniqueness of generic points for irreducible closed subsets; the existing node asserts a dimension equality and supplies neither point-topology assertion. The shared 03JX tag only justifies the quasi-separated hypothesis.

lem-sfb-quasiseparated-space-sober vs lem-sfb-quasiseparated-space-atlas-dimension: the new node asserts existence and uniqueness of generic points for irreducible closed subsets; the existing node asserts a dimension equality and supplies neither point-topology assertion. The shared 03JX tag only justifies the quasi-separated hypothesis.

lem-sfb-quasiseparated-space-sober vs lem-sfb-space-etale-atlas-topological-dimension: the new node asserts existence and uniqueness of generic points for irreducible closed subsets; the existing node asserts a dimension equality and supplies neither point-topology assertion. The shared 03JX tag only justifies the quasi-separated hypothesis.

lem-sfb-quasiseparated-space-etale-specializations vs lem-sfb-space-topological-dimension-local-rings: the new node asserts lifting of single specializations and noncollapse in etale fibres; the existing node asserts a dimension equality and supplies neither point-topology assertion. The shared 03JX tag only justifies the quasi-separated hypothesis.

lem-sfb-quasiseparated-space-etale-specializations vs lem-sfb-quasiseparated-space-atlas-dimension: the new node asserts lifting of single specializations and noncollapse in etale fibres; the existing node asserts a dimension equality and supplies neither point-topology assertion. The shared 03JX tag only justifies the quasi-separated hypothesis.

lem-sfb-quasiseparated-space-etale-specializations vs lem-sfb-space-etale-atlas-topological-dimension: the new node asserts lifting of single specializations and noncollapse in etale fibres; the existing node asserts a dimension equality and supplies neither point-topology assertion. The shared 03JX tag only justifies the quasi-separated hypothesis.

lem-sfb-quasiseparated-space-sober vs lem-sfb-quasiseparated-space-etale-specializations: sobriety concerns generic points of closed irreducible subsets; the second concerns lifts and fibres of etale charts. Neither statement supplies the other.

lem-sfb-quasiseparated-space-sober vs lem-sc-scheme-sober: the latter is only for schemes; the new node is for arbitrary quasi-separated algebraic spaces.

lem-sfb-quasiseparated-space-etale-specializations vs lem-sfb-finite-groupoid-orbit-incomparability: the latter assumes finite source and target for a groupoid and states only orbit incomparability; the new node allows arbitrary etale charts and also gives generalization lifting.

## Unfinished work

None for the one-level split. The two new statements remain unsplit for later workers.

## Review by Q97

I read decent-spaces.tex Tags 03JX (lemma-bounded-fibres and its implication chain), 03K6 (proposition-reasonable-sober with its proof), 03IL (lemma-decent-specialization), 03K5 (lemma-decent-no-specializations-map-to-same-point), and 0A4J (lemma-dimension-decent-space and its proof). These are the sources for both new prerequisites. Quasi-separatedness implies decency without any Noetherian or quasi-compactness assumption on the space. The sobriety node spells out its meaning rather than introducing an undefined notion. The specialization node spells out the direction by closure membership and does not assert specialization lifting in the opposite direction. Its continuity clause follows from the final topology already in stmt_deps. Neither new node includes a proof sketch or defines anything by an existence assertion.

For the item I read spaces-properties.tex Tags 0BAM (lemma-pre-dimension-local-ring), 04NA (definition-dimension-local-ring), 0BAN (lemma-dimension and its proof), 03H4 (lemma-points-cartesian), and 0A4H (lemma-dimension-decent-invariant-under-etale). I also read properties.tex Tag 04MU (lemma-dimension), and descent.tex lemma-dimension-local-ring-local. The step-by-step argument is as follows.

Step 1: the opened def-trf-algebraic-space supplies the representable surjective etale scheme atlas. The opened def-trf-algebraic-space-jointly-surjective-family expressly identifies covering on field-valued classes with surjectivity on points. Choosing it and interpreting its surjectivity are elementary.

Step 2: the opened lem-a1-space-fibre-product-point gives a scheme fibre-product point projecting to any two chart points with the same image. Representable etaleness in def-trf-algebraic-space says both scheme projections are etale. The opened lem-sfb-etale-stalk-invariants gives equality of their local-ring dimensions, with no global Noetherian assumption. Applying just that dimension clause twice proves chart independence explicitly. No normality or regularity clause is used.

Step 3: I opened lem-sc-scheme-sober and checked its statement gives existence and uniqueness of generic points for every irreducible closed subset of the scheme atlas. The new sobriety prerequisite gives exactly the same assertion for X. In each space, closures of points and their unique generic points identify strict closed-irreducible chains with strict specialization chains. The dimension definition def-kun-topological-krull-dimension is thereby applied directly, without importing an uncited chain comparison theorem. For an atlas chain, continuity preserves each specialization and the new noncollapse assertion prevents adjacent images from coinciding. For a chain in X, start at its final specialization and use atlas surjectivity once, then lift each generalization in succession using the new lifting assertion. Distinct images ensure strict lifted steps. This writes out the inductive construction for every finite length, including length zero. Equal possible lengths imply equal suprema, so infinite dimension needs no additional limiting argument. This is the chain argument in 0A4J, not an appeal to the dependent atlas-dimension node.

Step 4: the opened lem-pc-scheme-dimension-local-rings states exactly the scheme dimension equality with its supremum of all stalk dimensions, including the empty case. It assumes only that U is a scheme. Step 5 proves both upper-bound inequalities, explicitly using step 2 and the surjectivity of step 1. It assumes neither attainment nor finiteness of either supremum.

I tested empty X and U, a field spectrum, an integral curve with generic and closed points, and an infinite disjoint union of affine spaces of increasing dimensions. The two new prerequisites hold for a non-surjective open chart as well as an atlas; the lifting direction is generalization from a chosen special point. The empty space is sober vacuously, and lifting/noncollapse are vacuous for an empty chart. No quasi-compactness of U, absolute quasi-separatedness of S, finite type, or equidimensionality is introduced. The generic point-lifting, scheme sobriety and scheme-dimension comparisons are off-unit tools declared in split_report for review.

Against delivery-errors B--E, every non-elementary step cites statements that supply what it uses; all cited statements were opened. New nodes have explicit hypotheses, no hidden proof, required search records and blueprint provenance, and do not repeat the item's dimension conclusion. No SGA source is used. Citation quotes are complete node statements, checked literally. proof_deps is exactly the union of uses. All steps are below 2000 characters. The initial dry run's short-excerpt complaint was repaired by supplying complete statements; the second dry run's live-cycle finding was repaired by the chain argument and the two strictly smaller prerequisites.
