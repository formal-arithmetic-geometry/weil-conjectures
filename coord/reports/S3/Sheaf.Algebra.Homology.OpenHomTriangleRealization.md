## What changed

Replaced the sorry in `SheafOfModules.open_hom_triangle_realization` by a complete
Lean reduction to `SheafOfModules.open_cover_adjunction_triangle`, a strictly smaller
geometric statement in `Sheaf.Algebra.Homology.OpenCoverAdjunctionTriangle`.
The original public theorem signature and the definition `openHomRestriction` are unchanged.

The private, proved helper `restriction_has_left_adjoint` specializes the localized-site
exact adjunction and lifts the cochain-complex adjunction using Mathlib localization.
The left adjoint and its adjunction are unique up to the compatible natural isomorphism,
which is the equality used downstream: the geometric theorem allows every chosen
adjunction to the fixed right adjoint. No arbitrary mere-existence object is used.

The private generic helper `assemble_open_triangle` constructs the biproduct Hom
additive equivalence, the overlap additive equivalence, and the shifted Hom equivalence.
It proves the counit map identity using the adjunction triangle identities. The helper
`nested_transpose` proves the nested-map identity by naturality of the comparison iso,
so the negative second component yields the required difference. Keeping this calculation
abstract avoids expensive unfolding of localized module categories and compiles quickly.
All added imports in the parent are proof-only.

## Proved and sorry left

Closed: `SheafOfModules.open_hom_triangle_realization`
(node `lem-sc-open-hom-triangle-realization`), one of one original holes.
No sorry remains in the original module.

Added: `SheafOfModules.open_cover_adjunction_triangle`
(node `lem-sc-open-cover-adjunction-triangle`), exactly one named sorry in its new module.
This is a decomposition (one hole closed, one added; net zero), not an unconditional proof.
The new statement concerns only the geometric triangle with explicit canonical arrows;
it has no F, Hom equivalences, shifted Hom identification, or Hom map identities.
Those parts are proved in the parent. Its docstring contains the complete termwise/stalk
proof and the transport to arbitrary adjunctions.

Both modules compile without warnings through the required compiler.
Edge cases checked mathematically: U empty or V empty makes that extension zero;
U=V=top gives the split sequence m↦(m,-m), (m,n)↦m+n; E zero gives zero terms.
The mate formulas and adjunction triangle identities apply in all these cases.

## No longer needed

No original imports were removed: each original public import supports the existing
statements or their instances, and the public interface was preserved.

The parent's proof no longer needs nodes `lem-sc-derived-mayer-vietoris-triangle`,
`lem-sc-derived-open-mayer-vietoris-ses`, or
`lem-sc-derived-open-shriek-derived-adjunction`, or their modules
`Sheaf.Algebra.Homology.DerivedMayerVietorisTriangle`,
`Sheaf.Algebra.Homology.OpenExtensionMayerVietorisShortExact`, and
`Sheaf.Algebra.Homology.DerivedOpenShriekAdjunction`.
They were not imported by the original module and are not imported by this delivery.
Their geometric role is replaced by the explicit canonical-mate triangle interface.
This is pruning from this proof route; other users may still need those modules.
`lem-weil-pbc-exact-functor-derived-factorization` remains used.

## Where the brief, the DAG or earlier work was wrong

All three planned geometric modules reach the item through
`OpenRestrictionAdjunctionExact` → `DerivedHomMayerVietoris` → the item.
Importing them would create a cycle. The DAG already acknowledged this in its searches
but still listed them as the parent's proof dependencies. The new route avoids the cycle
through `LocalizedModuleAdjunctionExact`, which does not reach the item.

The short exact sequence interface only asserts existence of component maps whose
composites with counits agree. It does not identify their adjunction mates with nested
restriction, so it cannot alone justify the difference formula. The new geometric
statement explicitly fixes these mates rather than using an unspecified witness.

The unit `sk-thm-picard-duality` has no realized nodes or proof steps affected here.
Blueprint searches for Mayer Vietoris and extension by zero found no identical imported
statement. The new node retains the parent's nearest blueprint ancestor and geometric
Hom Mayer–Vietoris place. The current ancestor tool reports None for the parent even
though its existing blueprint.from record names `lem-sc-finite-duality`; this inconsistency
was not silently changed.

## New nodes

`lem-sc-open-cover-adjunction-triangle` in
`dag/nodes/sec-picard-framework/lem-sc-open-cover-adjunction-triangle.json` states the
canonical geometric triangle expressed using arbitrary left adjoints to the fixed
restriction functors, with arrows uniquely specified by their adjunction mates.
Its module is `lean/Sheaf/Algebra/Homology/OpenCoverAdjunctionTriangle.lean`.
Searches recorded are the actual leanfinder, loogle, grep and unavailable leansearch queries in `searches.jsonl`.
No definition or existing statement changed, and no change record is required.


## Second reading by S3

1. PASS: Compared the full parent diff with the repository. The existing
   `openHomRestriction` definition (including its body) and the complete
   `open_hom_triangle_realization` signature are byte identical. Only private
   proved helpers, proof-only imports, a local unused-binder linter setting and
   the theorem proof were added. No existing statement or definition changed.
2. PASS: Compiled both modules through `lcompile.py --all` without warnings.
   Separate scratch copies printed the axioms of all nine declarations: only
   `propext`, `Classical.choice`, `Quot.sound` and expected `sorryAx` occurred.
   In particular `assemble_open_triangle` and `nested_transpose` have no sorry
   dependency. The adjoint-existence helper still uses the already open
   `localizedModule_adjunction_exact`; this is an existing dependency, not an
   added hole. Exactly one new named theorem contains `sorry`; no definition
   does, and no forbidden declarations or attributes occur.
3. PASS: Read the entire geometric theorem and its docstring. Checked its
   mate formula against the unit/counit formulas and the nested natural iso.
   The termwise stalk argument proves the displayed triangle; transport by
   the unique adjunction-compatible left-adjoint isomorphisms justifies all
   chosen adjunctions. Empty opens, zero E, U=V and U=V=top satisfy the formulas;
   for coincident covering opens the maps are (id,-id) and addition, up to
   the displayed adjunction identifications. The new theorem isolates geometry
   and is strictly a part of the original argument, with no F or Hom equivalences.
   Repeated leanfinder, loogle and grep with different queries, and inspected
   Mathlib's sheaf-cohomology Mayer-Vietoris module: it concerns abelian sheaf
   cohomology, not this module-sheaf geometric triangle. No reusable match found.
   Verified the source at [08BU](https://stacks.math.columbia.edu/tag/08BU),
   [08BT](https://stacks.math.columbia.edu/tag/08BT), and
   [08BW](https://stacks.math.columbia.edu/tag/08BW); the local source is absent.
4. PASS: Read the proof downward, including the abstract helpers. All four
   added imports supply used declarations and are plain imports. Existing public
   imports retain the original interface and instances. Confirmed the three
   removed old proof dependencies are all listed under No longer needed.
   Their planned modules reach the parent through OpenRestrictionAdjunctionExact
   and Sheaf.Paper.DerivedHomMayerVietoris, preventing their use here. The unit's
   `realized` has an empty statement list and one empty step list, so this
   reduction bypasses no realized unit step. No whole module is claimed globally
   pruned. This remains a one-for-one decomposition, net zero holes closed.
5. PASS: The existing node changes only proof, proof_deps and proof_origin;
   its steps match the derived adjoint construction and abstract Hom assembly.
   The new node records the geometric proof plan, its dependencies, source,
   searches, creation, blueprint, unit, chapter and exact Lean signature.
   Its proof_deps equal the union of the uses in its proof steps.

Changed only this report and the new node's search records to preserve the
independent search evidence. No Lean repair was necessary. Scratch axiom probes
were removed before delivery; no additional holes were closed or added in this reading.
