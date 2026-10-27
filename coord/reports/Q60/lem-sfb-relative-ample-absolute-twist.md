# Q60 stage-1 delivery: lem-sfb-relative-ample-absolute-twist

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-ample-absolute-twist.json`: statement item, split in eight steps; Mathlib searches find no match. Statement and statement dependencies unchanged.
- `citations.json`: verbatim statements for all 24 step/node citations.
- `searches.jsonl`: actual msearch records; new searches appended to the item's existing search history.

Zero new nodes and zero new Mathlib leaves. No unit file changed: this is an auxiliary node, not the unit's key statement. No Lean file was written and no compiler or Lake command was run.

## Attachments

None. Searches of `lean/WeilConjectures/` by the item tag and by relative ampleness / absolute twist found no declaration giving this statement. Related Chow relative-ampleness and projective-graph statements do not give this general assertion. No project declaration was treated as finished merely because its theorem body delegates to another declaration.

## Literature wanted

None. The source is present: `literature/stacks-project/morphisms.tex`, Tag 0892, label `lemma-pullback-ample-tensor-relatively-ample`, assertion (1), statement and proof at lines 8829–8888. Also read `properties.tex`: Tag 01PW (`lemma-invert-s-sections`), 01PV (`lemma-affine-cap-s-open`), 09MP (`lemma-ample-separated`), and 01Q3 (`proposition-characterize-ample`), together with the proof of `lemma-ample-tensor-globally-generated`. No SGA source is used.

## Findings and corrections

The imported item is correct. Its quasi-compact morphism hypothesis plus ampleness on inverse images of every affine open is exactly the source's relative-ampleness assumption. Its nonnegative uniform bound states precisely the source's “a sufficiently large”, including every integer beyond the bound. There is no statement dispute or weakening.

The item was statement-only. The proof now explains denominator clearing, why multiplication by a positive extra power removes nonvanishing outside the chosen inverse image, the finite common exponent, and the passage from one ample twist to all sufficiently large twists. It establishes quasi-separatedness of Z explicitly before invoking 01PW, rather than assuming it from quasi-compactness. This only needs the existing qcqs and affine-intersection tools; the source proves the stronger separatedness through relative ampleness.

The old node `lem-per-relative-ample-absolute-twist` has exactly the same statement, and its argument was useful reference material. It is explicitly listed in `coord/route-pivot-dropped.txt` (line 1888). The live item's `blueprint.from.place` expressly says it is the replacement of that dropped per-chapter node. Thus I reused and independently checked the argument but did not cite the dropped node or create another replacement. All 16 distinct proof dependencies are live, and none is in the dropped-id list. Whole-blueprint searches `0892` and `relative ample absolute` returned zero matches. The existing null ancestor and via chain are retained, as reported by `blueprint_refs.py ancestor`.

The first formerly long preliminary step is now three separate steps: invertibility and quasi-compactness, separatedness on the base and inverse images, and the affine-cover argument for quasi-separatedness. Every step is below 2000 characters. Nothing non-elementary is moved into a clause-restating new lemma.

## Not duplicates

lem-sfb-relative-ample-absolute-twist vs lem-per-relative-ample-absolute-twist: these statements are identical; the latter is route-pivot-dropped, and the former is the maintainer-created live replacement explicitly described in its inherited provenance. This delivery modifies only that assigned live item and creates no duplicate node.

## Review by Q60

I read Tag 0892(1) and its proof in the local Stacks source, the item's current statement and provenance, its parent `lem-sfb-quasiprojective-qc-composition`, the recorded chapter and unit, and the current blueprint direct-image proof (3). The item is a generic scheme-theory input below the modification-composition chain; it does not change the chapter or unit route. Its source is precisely the intermediate 0892(1) lemma used by 0C4K in the parent. No new node needs a separate source audit.

For each proof step I opened the cited node statements, rather than relying on their titles or proofs:

1. `lem-weil-pbc-invertible-pullback-tensor` clauses (1),(2) give tensor/pullback invertibility and monoidal comparisons; induction gives powers. The tensor-unit case is written explicitly. `def-weil-pbc-ample-invertible-module` supplies quasi-compactness of T, and `lem-weil-pbc-qcqs-morphism-permanence` (2) then applies because f is quasi-compact. The empty Z case is handled before any point or nonempty finite cover is selected.
2. `lem-weil-pbc-ample-scheme-separated` applies both to M on T and to N on each Z_V, since the item's hypothesis covers every affine V. `lem-weil-pbc-separated-affine-open-intersection` applies to T over Spec Z. `lem-pc-separated-quasi-separated` is applied to the structure morphism of each Z_V, not to an unproved separated f.
3. `lem-weil-pbc-affine-scheme-qcqs` gives precisely the source quasi-compactness and target quasi-separatedness needed for permanence (1) on U -> V. Thus inverse images of the affine V'' are quasi-compact. Finite affine covers of those inverse images lie inside Z_V'', which is quasi-separated by Step 2. Both directions of `lem-weil-pbc-quasi-separated-affine-cover-criterion` apply exactly as stated. Their finite intersections cover U intersect U', yielding quasi-separatedness of Z with no finiteness assumption on the original cover.
4. The ampleness definition selects t and s with affine nonvanishing loci and positive degrees. `lem-weil-pbc-tensor-power-section-nonvanishing-pullback` states the required inverse-image equality for any positive degree, and the tensor comparison node identifies its target with f*(M^m). The relative hypothesis applies to the actual affine open T_t, not to an arbitrary open.
5. `def-sc-invertible-module` includes quasi-coherence. The coefficient N^n and the twisting module f*(M^m) are invertible by the cited tensor lemma. `lem-sc-p1-section-clearing-denominators-qcqs` states exactly the section extension needed on qcqs Z; Steps 1–3 supply those hypotheses. Its exponent can be zero, which causes no problem because b is strictly positive. The tensor lemma's fibre formula proves the equality of nonvanishing loci both inside and outside Z_q; this equality is not inferred merely from restriction of the section.
6. The arithmetic is explicit: for m dividing a and a >= m(e+1), b=na/m-e is an integer >=1 and (e+b)m=na. Finite quasi-compactness selects W_i; their fixed loci do not depend on a. A positive common multiple and a maximum bound produce A valid for every i. The stated ampleness definition needs a cover by affine section loci of possibly different positive powers, exactly what this constructs. This step is elementary and creates no new arithmetic or covering node.
7. `pqf-def-coherent` gives the hypotheses on O_T directly (associated ring module and one generator). `lem-weil-pbc-coherent-twist-global-generation` states generation for every sufficiently large degree, so choose a nonnegative K. `lem-sc-global-generation-nonvanishing-cover` gives a nonvanishing section at every point. The pullback-locus node, used with tensor degree 1 and invertible module M^c, makes a cover on Z; it does not need c>0, so c=0 is allowed.
8. `lem-sc-affine-cap-section-open` states affineness for an arbitrary invertible section on an affine open; it applies to Q_c and Z_u. The tensor lemma's fibre formula gives exactly Z_u intersect Z_w for the product section, including its positive tensor power. The ample definition and quasi-compactness of Z prove ampleness, and `lem-sc-ample-iso` transports it along the displayed monoidal comparison to P_a. This proves the entire tail with a0=A+K. The ample-times-globally-generated argument is written out from these existing statements, not hidden behind a source citation.

I checked the delivery-errors B–E cases: statements introduce their own objects; no new statement-only node conceals a proof; citations have verbatim evidence; no definition is used in place of an uncited theorem; no off-unit tool changes the unit route; no dropped node is cited; the hypotheses of 01PW and each affine intersection are established; there is no circular dependency or unproved final clause. Generic tool uses are declared in split_report for maintainer review, not written into the maintainer-owned tool_uses field.

Small cases checked: empty Z and empty T; f the identity (ordinary ample twists); affine T with trivial M; n=m=1 and e=0 in the exponent calculation; different positive m_i in the finite synchronization; and c=0 when the global-generation bound allows it. Negative twists are never needed because a0,A,K are nonnegative. The searches were actually run through msearch.py: Loogle and grep return zero hits, while the semantic searches return permanence lemmas, functions on basic opens and convex ample sets, whose signatures do not assert this theorem. A second semantic phrasing was tried. Existing search records were retained.

## Unfinished work

None in the assigned stage-1 split. The dependency proofs remain owned by their existing nodes; this delivery introduces no new open node.
