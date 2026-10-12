## What changed

The existing module `Sheaf.AlgebraicGeometry.CohomologyPowersIdealApplication` now proves
`AlgebraicGeometry.cohomology_powers_ideal_application` by constructing its transition
family, applying separate eventual image and kernel estimates, and specializing both to
`max c₁ c₂`. Its original signature is byte-for-byte unchanged. The proof docstring's last
sentence now describes this reduction instead of referring to the old node's eight steps.

Added three modules: `CohomologyPowersIdealTransitionMaps`, `CohomologyPowersIdealImageBound`,
and `CohomologyPowersIdealKernelBound`, under `Sheaf.AlgebraicGeometry`. The transition theorem
is proved categorically from the recursive powers and Mathlib `image.map`/`image.map_ι`.
It requires only an arbitrary scheme, ideal sheaf, and module. The two estimates are each
strictly a part of the original argument and explicitly allow every c above their own
threshold, so the maximum combines them without an additional monotonicity assumption.

The existing module adds three plain proof imports and removes two unused plain imports.
New modules expose only imports needed in their signatures; Rees finiteness and Noetherian
module results are plain proof imports. No existing public import, definition, or signature
changed, and no change record or forced adaptation is needed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.cohomology_powers_ideal_application`
(node `lem-weil-pbc-cohomology-powers-ideal-application`). Its proof still depends on
`sorryAx` through the estimates below; this is a decomposition, not an axiom-free proof.

Also fully proved `AlgebraicGeometry.cohomology_powers_ideal_transition_maps`
(node `lem-weil-pbc-cohomology-powers-ideal-application-transition-maps`), with two private
proved categorical helpers. This closes the first worker's proposed transition-map hole;
that proposed hole was never part of the repository baseline.

Added exactly two named holes, each with a complete natural-language proof and source in
its docstring and its matching node:

- `AlgebraicGeometry.cohomology_powers_ideal_image_bound`, node
  `lem-weil-pbc-cohomology-powers-ideal-application-image`.
- `AlgebraicGeometry.cohomology_powers_ideal_kernel_bound`, node
  `lem-weil-pbc-cohomology-powers-ideal-application-kernel`.

There are no other delivered sorries, and no definitions were added or changed.
Against the repository baseline this delivery closes one hole and adds two: the local
hole delta is -1. It claims no positive target-closure progress; the maintainer's pinned
sorry ledger determines closure and whole-library figures. All four delivered modules
compiled through lcompile.py without warnings.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.CohomologyPowersIdealReesFinite`
and `Sheaf.Paper.PQFCohomology` from the item's module. Rees finiteness remains imported
by both estimate modules; PQFCohomology also remains in that dependency's imports.
Thus this delivery does not claim either entire module is pruned from the target closure.

All five old direct proof dependencies are replaced by the three new nodes:
`lem-weil-pbc-cohomology-powers-ideal-rees-finite`, `pqf-def-cohomology`,
`def-weil-pbc-coherent-formal-module`, `lem-weil-pbc-rees-algebra-noetherian`, and
`lem-weil-pbc-noetherian-submodule-finite` are no longer applications in the parent proof.
Rees finiteness, cohomology functoriality, and the two Noetherian leaves remain in the
estimate nodes' proof dependencies; the formal-module constructions remain in the
unchanged statement dependencies and exposed imports. No obsolete node is deleted.
Pruned complete modules: none.

## Where the brief, the DAG or earlier work was wrong

The first worker's report overstated proof progress: one original hole was replaced by two
new holes, and the combined bounds theorem carried almost all the original mathematical
argument. Its docstring omitted a proof, the new nodes lacked statement dependencies,
search records and verbatim Lean signatures, and the original node was not updated.
The second reading repaired these points: fully proved transitions, discarded the proposed
combined bounds module/node, split only the separate image/kernel parts, and wrote the
actual reduction in the original module. The two unproved estimates cannot be closed by
a short application of the searched Mathlib filtration results, whose levels live inside
one fixed module rather than the varying cohomology modules here.

The remote clone has no `literature/stacks-project/coherent.tex`; I independently read
Stacks Lemma 02OA and its proof at https://stacks.math.columbia.edu/tag/02OA. Source places
in the nodes remain those of the project reference, with this verified URL added.
LeanSearch returned an internal server error for both searches and is recorded as
unavailable, without a no-match verdict. LeanFinder, Loogle, and local Mathlib/library
searches ran; the categorical image lemmas found by search are used in the transition proof.

## New nodes

`lem-weil-pbc-cohomology-powers-ideal-application-transition-maps`: existence of the
canonical factorization family for any ideal sheaf and module, fully proved by recursive
power inclusions and categorical image functoriality; no cohomological or properness
hypothesis is needed.

`lem-weil-pbc-cohomology-powers-ideal-application-image`: only the image bound, with an
explicit threshold such that every larger c works. Its proof follows bounded-degree
homogeneous generation and the two cases n >= c and n < c of Stacks 02OA(2).

`lem-weil-pbc-cohomology-powers-ideal-application-kernel`: only the kernel equality, with
an explicit threshold such that every larger c works. Its proof follows finite homogeneous
generation of the kernel submodule over the Noetherian Rees algebra in Stacks 02OA(3).

All three carry the chapter/unit of the parent, source, proof steps, proof dependencies,
search records, blueprint ancestry, and verbatim Lean signature. No change record.

## Earlier second reading (a previous round; superseded)

1. Checked every delivered module against the repository. The only existing module's
   theorem signature is byte-for-byte identical; all existing public imports and visibility
   remain unchanged. The other three modules and their declarations are new. No existing
   data definition changed. Verdict: unchanged external statement and definitions.
2. Compiled every delivered module in import order through lcompile.py. Checked that the
   only two sorries are the named public estimate theorems with bodies exactly `by sorry`.
   No axiom, unsafe, opaque, implemented_by, extern, bypass, or holed definition occurs.
   Printed axioms in a scratch copy: transitions use only standard axioms; both estimates
   and the parent also use sorryAx as expected. Verdict: sound checked reduction with two
   explicitly open obligations, not a fully closed theorem.
3. Read both estimates against the independent Stacks proof and tested the boundary cases
   in words: F = 0 (empty generators), I = 0 (positive levels vanish), I = top (identity
   transitions), m = 0 (image lies in the whole module), n = 0 (the stated truncated
   exponent), n = c (kernel maps have equal targets), and c = 0 (when the corresponding
   generators have degree zero). Canonicality follows by cancellation of the image
   inclusion, so arbitrary compatible i does not add an invalid hypothesis. Each estimate
   is only one of the parent's two cohomological conclusions. Their eventual-all-c form
   follows from the same degree-bound proof, not a new assumption. Searched Mathlib with
   different phrasing through msearch.py, read the returned image/filtration declarations,
   and searched lean/Sheaf, lean/WeilConjectures, and the upstream checkout. No duplicate
   sheaf-cohomology estimate found. Verdict: true, smaller obligations, with complete
   docstrings and matching nodes.
4. Took the shortest categorical route for transition existence and pruned unused direct
   proof imports. The parent performs the genuine maximum-threshold combination. Checked
   dag/units/sk-thm-p1.json realized: the item is below those realized unit statements/steps,
   and the Rees finiteness and Noetherian route remains in the new estimates. No unit route
   or realized record changed. The No longer needed section lists every old direct
   proof dependency and explains retained transitive uses. Verdict: route preserved;
   decomposition honestly counted, no whole-module pruning claimed.
5. Updated the parent node's proof/proof_deps/proof_origin to its actual Lean proof and
   rebuilt all new nodes, including stmt_deps, three kinds of attempted search, source,
   creation/ancestry and verbatim lean.statement. Checked proof_deps equals the union of
   step uses. Existing node statement and statement dependencies remain unchanged.
   Verdict: DAG agrees with the delivered Lean.

Second-reading changes: proved and generalized the unpublished transition lemma; replaced
its unnecessary public Rees import; removed the near-restatement combined bounds hole;
added separate eventual image/kernel obligations and the maximum proof; supplied complete
proof docstrings; repaired all node metadata and the parent route; removed unused direct
imports; corrected the progress report.

## Second reading by N1

1. Compared the delivered parent module with the repository version. The existing theorem
   signature and all existing declarations are unchanged byte for byte; the three additional
   modules contain only new declarations. Verdict: no accidental statement or definition change.

2. Compiled all four delivered modules with lcompile.py in import order. The parent and
   transition theorem are sorry-free; the only remaining sorries are the two named estimate
   theorems listed above, each exactly a public theorem proof body `by sorry`. No forbidden
   declarations or hollow definitions occur. Verdict: clean compilation with the documented
   two split obligations.

3. Checked the two estimate statements against Stacks 02OA and their docstrings, including
   boundary cases n = c, m = 0, n = 0, I = 0, and empty generating families. Each is a
   strictly smaller eventual assertion than the parent and has a matching node with source,
   proof steps, dependencies, searches, and verbatim signature. The transition statement is
   true for arbitrary schemes and modules and is fully proved by image factorization.
   Verdict: statements are true and appropriately strong; no duplicate library result found.

4. Checked the proof route and imports. The parent constructs the canonical transition family,
   obtains the independent image and kernel bounds, and combines thresholds with `max`; the
   unit route through Rees finiteness and Noetherianity remains in the split estimates. The
   direct imports removed from the parent are unused there and remain transitively used by the
   estimate modules. Verdict: route preserved and pruning is accurately reported.

5. Compared every DAG node's proof, proof_deps, proof_origin, statement dependencies, and
   Lean metadata with the delivered declarations. The parent node records the actual maximum
   reduction, and each new node records its exact theorem and dependency union. Verdict: DAG
   and Lean agree.

Changes made in this second reading: added this review section required by the delivery
contract; no mathematical or interface changes were necessary.
