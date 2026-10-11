# Stage-1 report: lem-pc-ring-derived-map-lift

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-ring-derived-map-lift.json`: completed the Tag 064E split with three proof steps; no Mathlib match for the full lift.
- `dag/nodes/sec-picard-framework/lem-pc-ring-precise-vanishing.json`: new statement-only Tag 064D dependency; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-ring-derived-map-representative.json`: new Mathlib leaf for `CochainComplex.IsKProjective.Qh_map_bijective`.
- `citations.json`: verbatim quotes for every dependency used by every step.

## Attachments

None. A grep of the slopmaster2 `WeilConjectures/` tree found no declaration tagged `(blueprint: lem-pc-ring-derived-map-lift)` and no sorry-free declaration of the exact bounded-projective lifting statement.

## WANTED

None.

## Not duplicates

lem-pc-ring-precise-vanishing vs lem-sc-bounded-above-projective-kprojective: the new node gives vanishing of derived morphisms into a complex with cohomology zero in degrees at least $n$, while the existing Mathlib leaf only states K-projectivity (Hom-complex acyclicity) for bounded-above projective complexes.

lem-pc-ring-precise-vanishing vs lem-weil-pbc-hom-into-triangle-exact: the new node is a derived-category vanishing criterion from a truncated projective source; the existing node is exactness of Hom into a distinguished triangle.

lem-pc-ring-derived-map-representative vs lem-sc-bounded-above-projective-kprojective: the new node states bijectivity of the homotopy-to-derived morphism map, whereas the existing node states only the K-projective acyclicity property.

## Review by J1

I read the target statement against Derived Categories Tag 064E (`derived.tex`, `lemma-lift-map`) and its cited Tags 064B, 064C, and 064D. The ring-module specialization introduces $R$, $n$, the bounded projective complex $P$, the lower-degree vanishing, the two complex morphisms, and the homotopy conclusion (equivalently the displayed equality after applying $Q$). I also read `def-weil-abstract-derived-category` to verify that its $Q$ is the localization used in the statement.

Step 1 uses the cone and distinguished-triangle clause of `def-weil-abstract-derived-category` and the long exact cohomology statement of `lem-sf-derived-homology-long-exact`; these state respectively that the cone triangle exists in $D(R)$ and that its cohomology sequence is exact. The isomorphism hypotheses above $n$ and surjection at $n$ were checked directly in the four consecutive terms, giving $H^j(C(\\alpha))=0$ for every $j\\ge n$.

Step 2 uses the exact statement of the new Tag 064D node: a bounded projective source vanishing below $n$ has no derived morphisms to a complex whose cohomology vanishes in degrees at least $n$. The hypotheses are exactly the item hypotheses and the conclusion of Step 1, so the composite into the cone is zero.

Step 3 uses `lem-weil-pbc-hom-into-triangle-exact`, whose statement gives the factorization through the first arrow of a distinguished triangle when the composite with the second arrow is zero. It then uses the Mathlib leaf `lem-pc-ring-derived-map-representative`; its statement is precisely the bijection needed to replace the derived factor $δ$ by a chain map $\\gamma$. The resulting equality is $Q(\\alpha)\\circ Q(\\gamma)=Q(\\beta)$, hence $\\alpha\\circ\\gamma$ is homotopic to $\\beta$.

I searched the whole DAG and blueprint for Tags 064D/064E, for precise-vanishing language, and for the representation statement before creating nodes; no duplicate statement or blueprint node was found. The Mathlib searches were run for the item and both new nodes with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as unavailable in each JSON. I tested the hypotheses on the zero complex and on a one-term projective complex with $n=0$; the cone vanishing and factorization reduce to the stated surjectivity/isomorphism conditions. The imported auxiliary node had `created.item` pointing to the neighboring triangle item; this split corrects ownership to the present item and supplies its missing proof.

## What was wrong and what changed

The imported node was statement-only and owned by `lem-pc-ring-pseudo-coherent-distinguished-triangle`. I retained its statement, corrected its ownership metadata, and supplied the Tag 064E cone argument. The missing Tag 064D vanishing input and the chain-map representation input are now explicit dependencies rather than hidden assertions.

## Unfinished

Nothing.

## Second reading by J1

- Item statement: checked against Stacks Tag 064E, including the chain-map hypotheses and homotopy conclusion; repaired the temporary derived-morphism phrasing so the cone $C(\\alpha)$ is defined.
- Step 1: checked against the cone triangle in `def-weil-abstract-derived-category` and the exact sequence in `lem-sf-derived-homology-long-exact`; the $j>n$ and $j=n$ cases use exactly the stated isomorphism/surjection hypotheses.
- Step 2: checked against `lem-pc-ring-precise-vanishing`; its bounded-projective, truncation, and cohomology-vanishing hypotheses match the step.
- Step 3: checked against `lem-weil-pbc-hom-into-triangle-exact` and the representative bijection; the factor is represented by a chain map and yields homotopy, with no unstated cone or derived-map assumption.
- `lem-pc-ring-precise-vanishing`: checked against Tag 064D hypothesis by hypothesis, including zero-complex and one-term projective cases; statement-only and strictly smaller than 064E.
- `lem-pc-ring-derived-map-representative`: checked against Mathlib declarations `CochainComplex.IsKProjective.Qh_map_bijective` (DerivedCategory/KProjective.lean:43) and `isKProjective_of_projective` (HomotopyCategory/KProjective.lean:113); exact bounded-above-projective specialization and recorded searches are present.
- Duplicate and blueprint checks: searched the DAG and imported blueprint for Tags 064D/064E and the representation claim; no duplicate or blueprint statement found.
- Changes: restored the source-faithful chain-map/homotopy interface, updated Step 3 and its source place, and made the Mathlib file/line citation exact; this fixes the cone typing gap without changing the intended derived equality.
