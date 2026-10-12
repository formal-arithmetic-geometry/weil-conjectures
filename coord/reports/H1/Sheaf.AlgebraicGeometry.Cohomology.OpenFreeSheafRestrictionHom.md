## What changed

Proved `AlgebraicGeometry.Scheme.Modules.H.openFreeSheaf_restrictionHom_bijective`
in `Sheaf.AlgebraicGeometry.Cohomology.OpenFreeSheafRestrictionHom` without changing
its signature or visibility. Added two proved private helpers: the standard
sheafification/free/Yoneda sections equivalence and its naturality. No public
imports, definitions, instances, options or signatures changed.

The proof constructs the naive restriction/direct-image adjunction from the
image/preimage adjunction on opens. At the image open its unit on sections is
invertible, because image(preimage(image(j))) = image(j). This proves bijectivity
of postcomposition with the unit; adjunction then gives bijectivity of naive
restriction. Naturality of Mathlib's open-embedding inverse-image isomorphism
transports this to the requested inverse-image map. Updated the existing node's
proof, proof dependencies and proof origin accordingly.

Source read: Stacks Tags [03DI](https://stacks.math.columbia.edu/tag/03DI),
[00A7](https://stacks.math.columbia.edu/tag/00A7), and
[01F7](https://stacks.math.columbia.edu/tag/01F7). The proof uses the direct
sections formulation rather than constructing extension by zero. Mathlib's
actual adjunction, whiskering, restriction and open-embedding APIs were read.
Searches ran through msearch: leanfinder (8 results, no direct match), loogle
for `Topology.IsOpenEmbedding.sheafPullbackIso` (1 matching API), and grep
(25 capped results). Local rg searches found the proved private sections
construction in `InverseImageOpenFreeSheaf`; the same standard construction is
needed locally because that helper is private. No unproved dependencies are used.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.H.openFreeSheaf_restrictionHom_bijective`
(lem-pc-open-free-restriction-hom).

No sorries remain in the delivered module. No holes were added and none were
split off. The private helpers are completely proved. Single-file compilation
passed cleanly through lcompile.py. The delivery dry run performs the axiom probe
and final preflight.

## No longer needed

The planned proof dependency `lem-weil-pbc-zariski-extension-by-zero-adjunction`
and its module `Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction` are no
longer needed by this item; removed that node from its proof dependencies. No
existing import was removed: the sole public import provides the represented
free-sheaf definition and the inverse-image convention. Trial explicit imports
of `Mathlib.CategoryTheory.Adjunction.Opposites` and
`Mathlib.CategoryTheory.Adjunction.Whiskering` were unnecessary and removed;
the needed APIs are already available through the existing public import.

No inverse-image free-sheaf isomorphism theorem, exactness of extension by zero,
or restriction-Ext theorem is needed. The node uses only the definitions supplied
by `lem-pc-free-mayer-vietoris-short-exact` and
`def-pc-flat-cohomology-comparison`, plus proved Mathlib results. It does not use
the former node's short-exactness theorem. No claim is made that another target
branch cannot still need these pruned dependencies.

## Where the brief, the DAG or earlier work was wrong

The DAG's extension-by-zero identification is a valid possible route but is
unnecessary: the unit at the image open gives the shorter argument directly.
No statement correction was needed. The unit record sk-thm-picard-rr has no
realized statement or step nodes; this item changes no unit or chapter route.
The empty-open case is covered by the same image/preimage identity and the
sections equivalence, including the unique section of the empty open. For the
top-open case the same unit calculation is invertible; no nonemptiness, extra
coefficient condition, or extra geometric hypothesis is imposed.

## Second reading by H1

1. **Visible changes and statements.** Compared the delivered module and node with the repository versions. The theorem signature and visibility are byte-for-byte unchanged; only its proof, imports, and DAG proof metadata changed. No definition or target statement changed.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds without warnings or errors. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The proof uses only the existing public import and proved Mathlib/library declarations; its expected kernel axioms are therefore within the project allowance.

3. **Split-off statements.** No statements were split off and no new nodes were added. The existing node remains the exact restriction-bijectivity statement. I checked the empty-open and top-open edge cases in the image/preimage identity used by the proof; no extra hypotheses are introduced.

4. **Shortest route and pruning.** The direct represented-sections plus open-map adjunction route closes the target without extension-by-zero. The removed extension-by-zero import and proof dependency are genuinely unused; no other existing import was removed. The module remains on the unit's recorded route and does not alter the unit record.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` describe the implemented adjunction, unit-isomorphism, and naturality steps. The report's proved/sorry counts match the file: one original hole closed, zero holes added, and no split-off theorem.

Changed during second reading: added this review section only; no Lean code or node content required repair.
