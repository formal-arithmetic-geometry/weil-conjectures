## What changed

The original declaration `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_properties`
keeps its entire signature and visibility. Its proof now assembles the linearity, degree-zero,
identity and restriction clauses from separately named component declarations.

The identity component contains a complete cancellation and naturality argument: expand the
resolution formula, factor its horizontal homology map through the standard resolution descent,
cancel the vertical homology isomorphism, use naturality of the forgetful homology comparison,
and apply `InjectiveResolution.isoRightDerivedObj_hom_naturality`. The pending identity step is
isolated in `Sheaf.AlgebraicGeometry.IdentityResolutionHomology`: it is a factorization on the
homology of sections complexes, before any right-derived resolution transports. Its conclusion
is strictly a part of the identity argument, not the original identity statement renamed.

The three other clauses are pending named component theorems, in
`BasicPropertiesLinearity`, `BasicPropertiesDegreeZero`, and `BasicPropertiesRestriction`.
Restriction's component statement omits the original theorem's unrelated X, h, F and phi
parameters; the original declaration is unchanged. All new modules have source citations,
complete natural-language proofs and matching DAG nodes. No definition or existing interface
was changed, and no other group's module was adapted.

## Proved and sorry left

Closed one original hole, by decomposition:
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_properties`
(node `lem-weil-pbc-module-cohomology-fmap-basic-properties`). No sorry remains in that module.

Also implemented the complete proof combining the identity resolution factorization with
Mathlib naturality:
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_identity`
(node `lem-weil-pbc-module-cohomology-fmap-basic-identity`). This is a reduction using the
pending resolution factorization, not a claim of an independent sorry-free result.

Four new holes remain, each the whole proof of a public theorem in its own module:

- `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_linearity`
  (`lem-weil-pbc-module-cohomology-fmap-basic-linearity`).
- `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_degree_zero`
  (`lem-weil-pbc-module-cohomology-fmap-basic-degree-zero`).
- `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_restriction`
  (`lem-weil-pbc-module-cohomology-fmap-basic-restriction`).
- `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_identity_resolution_homology`
  (`lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology`).

Hole accounting for this delivery: one old hole closed, four added, net minus three.
This is a decomposition. Existing sorries in imported library modules are not newly added holes.
All delivered modules are compiled in import order by lcompile.py and checked by the delivery
script's axiom probe and stage-3 preflight. No additional axioms are introduced; the pending
named statements still use sorry as recorded above.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`
- `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.Paper.PQFCohomology`

The main proof needs only the four component modules beyond its existing public statement
imports. The component statements obtain tensor pullback and cohomology definitions through
`ModuleCohomologyFMap`'s public imports. The pending proofs retain the relevant original
comparison nodes in their own proof dependencies, so their transfer is not global pruning.
No original comparison node is claimed globally unnecessary. The dependency on the bundled
`PQFCohomology.sheafCohomologyAndHigherDirectImages` theorem is unnecessary for the conjunction
proof: only the already defined module cohomology functors are used.

The identity proof needs neither the h-map functoriality module nor its independence theorem.
That functoriality module imports this item; importing it here would create a cycle. The new
resolution factorization gives a direct route avoiding that cycle. None of these component
nodes is a unit's realized statement or step; the route of unit `sk-thm-p1` is retained.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox contained placeholder component node statements, placeholder proof
arguments, generic `new-*` identifiers, redundant imports, and a second-reading placeholder.
Replaced the placeholders with self-contained mathematical statements, specific node names,
and full arguments following the original node's steps. Removed the second-reading section;
only the independent reader writes it. The earlier report claimed the comparison imports were
not directly imported even though they were still present; they are now actually removed.

The previously reported SSH fetch failure no longer occurs: the initial dry run succeeded.
No mathematical error in the original statement was found. Edge cases inspected: p = 0,
zero sheaves, the empty scheme, and U empty or all of Y. Linearity still concerns the specified
restricted scalar action; degree-zero comparisons come from augmentations, with no boundaries
in negative degrees; the identity factorization works for every system D of resolution choices;
and restriction uses uniqueness of adjoints including for the empty and whole open. No proper,
flat, nonempty or finite-type hypotheses were added.

Searches: LeanFinder returned elementary scheme-module pushforward and section lemmas, not
these cohomology statements. Loogle located `Homotopy.homologyMap_eq`; local Mathlib searches
located `isoRightDerivedObj_hom_naturality` and right-derived comparison formulas. LeanSearch
returned HTTP 500, recorded as unavailable. Searches in the source library and project found
no applicable identity h-map theorem outside the cyclic functoriality module. Blueprint
searches for module cohomology, degree zero, restriction/pullback, identity/cohomology and
linearity found no matching blueprint statement to reuse; the incidental linearity matches
concern integration and zero-dimensional étale cohomology.

The local Stacks TeX files are not installed here. Read the authoritative Stacks pages for
[Remark 01FB](https://stacks.math.columbia.edu/tag/01FB),
[Lemma 01F8](https://stacks.math.columbia.edu/tag/01F8), and
[homotopy uniqueness 013S](https://stacks.math.columbia.edu/tag/013S), and the full original
DAG proof. The source locations in new nodes retain the project's canonical literature paths.

## New nodes

`lem-weil-pbc-module-cohomology-fmap-basic-linearity` is exactly the linearity clause.
Its proof transports the linear maps on sections complexes and the inverse vertical map
through restriction-of-scalars and forgetful homology comparisons.

`lem-weil-pbc-module-cohomology-fmap-basic-degree-zero` is exactly the degree-zero clause.
Its proof uses kernel preservation, augmentation identifications and the defining square
for beta evaluated on global sections.

`lem-weil-pbc-module-cohomology-fmap-basic-identity` is the identity clause with a complete
Lean proof from the next node and Mathlib resolution-comparison naturality.

`lem-weil-pbc-module-cohomology-fmap-basic-restriction` is the restriction clause, quantified
only over Y, G, p and U. Its proof compares adjunction units and resolutions directly using
K-injective lifting and homotopy uniqueness, then cancels vertical quasi-isomorphisms.

`lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology` isolates the horizontal
factorization inside the identity proof. It quantifies over arbitrary pinned resolution data
D, asserts an equality on sections-complex homology only, and contains no right-derived
resolution isomorphisms. Its proof uses the pushforward-identity comparison, augmentation
compatibility and homotopy uniqueness. This delivery adds no change records because no
existing statement, definition, visibility or public import was changed.

## Second reading by W2

1. Compared the delivered main module with the repository version. The target theorem's
   signature is byte-for-byte unchanged; only its proof and proof-only imports changed.
   Verdict: passed.
2. Compiled all six delivered Lean modules with `lcompile.py --all`. The main theorem has
   no `sorry`; the four component declarations and the resolution factorization retain only
   the named `sorry`s listed above. No forbidden declarations or definitions were added.
   Verdict: passed.
3. Checked each split-off statement against its node, docstring, and edge cases (zero sheaves,
   degree zero, identity morphisms, and empty/full opens). Each is a strict subclaim needed by
   the decomposition and has no duplicate declaration in the library or Mathlib. Verdict: passed.
4. Reviewed the proof route and imports. The conjunction proof uses exactly the four component
   declarations; removed imports are recorded under `No longer needed`, and the identity route
   avoids the cyclic functoriality module. Verdict: passed.
5. Checked all delivered node records: declarations, statements, proof dependencies, sources,
   proof origins, and unit metadata agree with the Lean files. The unit route remains intact.
   Verdict: passed.

Changed only the main proof/imports, added the four component modules and resolution-factorization
module plus their node records, and appended this independent second-reading report.
