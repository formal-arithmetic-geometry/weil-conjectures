## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_finite_affine_cover`
with a complete proof following the existing two-step DAG plan.
The statement, visibility, docstrings, definitions, and final imports are unchanged.

First choose the positive powers, global sections, and affine opens supplied by
`hL.2`, retaining all their properties. Register `hL.1` as the compact-space
instance. Apply Mathlib's `IsCompact.elim_finite_subcover` to the point-indexed
open cover, then reindex the resulting finite subset using `Finset.equivFin`.
The inverse equivalence transports the powers and dependent section types
along with the opens; its inverse identity proves the final covering clause.
No assumption of nonemptiness is used, so the same proof covers empty schemes.

The searches through the launcher used LeanFinder for finite subcovers and
Loogle for `IsCompact.elim_finite_subcover`; local ripgrep checked the source
library's ampleness declarations and Mathlib compactness/finite equivalence APIs.
The source library's relative-field ampleness notion is different and is not used.
The module compiled cleanly, including after removing both trial Mathlib imports.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_finite_affine_cover`
(node `lem-sc-ample-finite-affine-cover`).

No `sorry` remains in the item's module. No holes or new declarations were added.
This is a proof, not a decomposition into new unproved statements.

## No longer needed

None of the original imports, nodes, or modules is pruned. Both original proof
dependencies are used: `def-weil-pbc-ample-invertible-module` provides the pointwise
cover and compactness, and `def-weil-pbc-quasi-compact-scheme` is realized by
Mathlib's compactness API. Trial imports `Mathlib.Data.Fintype.EquivFin` and
`Mathlib.Topology.Compactness.Compact` were removed because the required
public declarations are already available through the original import
`Sheaf.AlgebraicGeometry.Ample`.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface fault found. The node's two steps were implemented
directly, so no DAG route update is necessary. The unit record
`dag/units/sk-thm-curveestimate.json` realizes its statement by
`thm-sc-proper-cohomology` and lists no realized steps; no unit route was bypassed.

The cited literature and blueprint text files are absent from this clone.
The existing node and declaration documentation were read; the cited source was
also checked online at [Stacks Definition 01PS](https://stacks.math.columbia.edu/tag/01PS)
and the opening proof paragraph of
[Stacks Lemma 01Q1](https://stacks.math.columbia.edu/tag/01Q1).
They give the pointwise ampleness condition and the finite affine nonvanishing cover
used here. No new sourced statement is required.


## Second reading by F2

1. **Interface unchanged — PASS.** Independently diffed the only delivered module
   against the repository. Only the body of
   `AlgebraicGeometry.Scheme.Modules.IsAmple.exists_finite_affine_cover` changes.
   The entire prefix through its signature, including imports, visibility and
   docstrings, is byte-identical. There are no definitions, new declarations,
   adapted modules or change records in this delivery. Matched the scheme,
   invertible module, ampleness hypothesis, positive powers, global sections,
   affine opens, exact germ predicate and covering clause against
   `lem-sc-ample-finite-affine-cover`.
2. **Proof and axioms — PASS.** Independently compiled the delivered file with
   `lcompile.py` (2.0 seconds, no errors or warnings). Compiled a scratch copy
   with `#print axioms`: the theorem uses exactly `propext`, `Classical.choice`
   and `Quot.sound`, without `sorryAx`. Scanned the module for `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern` and `debug.skipKernelTC`:
   none occurs. `choose` selects from the assumed pointwise ampleness condition
   inside a theorem proof; no data definition chooses an arbitrary witness of
   an unproved existence theorem.
3. **Split statements and small cases — PASS.** No statements are split off and
   no holes are added. Read the actual definition `Scheme.Modules.IsAmple`
   and both dependency nodes. The finite subcover retains the selected positive
   exponents and affine nonvanishing opens. For empty X, the point-indexed
   finset is empty and `Fin 0` is allowed; no nonemptiness instance is used.
   For a one-point affine scheme the same argument retains a covering open.
   Reindexing all data by the same inverse equivalence keeps the dependent
   section type exactly `(L.tensorPow (n i)).val.presheaf.obj (Opposite.op ⊤)`.
4. **Shortest route and pruning — PASS.** Read Mathlib's finite-subcover API
   and `Finset.equivFin`. Independently searched LeanFinder for point-indexed
   compact-space neighbourhood covers: `finite_cover_nhds` and
   `CompactSpace.elim_nhds_subcover` are alternatives, but introduce a
   neighbourhood conversion and still require the same finite reindexing.
   The current direct `IsCompact.elim_finite_subcover` route needs no helper.
   Searched the project's ampleness/finite-cover declarations and read
   `FiniteSectionsCover.lean`; that theorem requires global generation of
   one module and supplies neither varying powers nor affineness, so does
   not replace this argument. The sole public import `Ample` is required by
   the statement. Neither old proof dependency is unused: `hL.2` supplies
   the pointwise data and `hL.1` supplies the `CompactSpace` instance used by
   Mathlib. `## No longer needed` is complete. Read
   `dag/units/sk-thm-curveestimate.json`: its realized statement remains
   `thm-sc-proper-cohomology` and it has no realized steps to bypass.
5. **DAG and sources — PASS.** Read the existing node's `proof`,
   `proof_deps` and `proof_origin` and both cited definition nodes. Step 1 is
   implemented by `choose` and the cover witness `hx x`; step 2 by the
   compactness instance, finite subcover and equivalence with `Fin t.card`.
   Positivity, affineness and the exact locus equivalence are transported by
   `hn`, `hU` and `hmem`; the inverse-equivalence identity proves coverage.
   The existing DAG plan therefore agrees with the proof without changes.
   Independently read [Stacks Definition 01PS](https://stacks.math.columbia.edu/tag/01PS)
   and the first proof paragraph of
   [Stacks Lemma 01Q1](https://stacks.math.columbia.edu/tag/01Q1): the former
   supplies quasi-compactness and pointwise affine nonvanishing loci of
   positive powers, and the latter uses the resulting finite affine cover.
   No quasi-separatedness hypothesis is needed for this finite-cover step.

**Changes made by second reader:** appended this independent review only.
The Lean proof and DAG are correct as delivered and were retained unchanged.
One hole closed, zero holes added; no modules pruned.
