## What changed

Replaced the rejected duplicate Core theorem with a genuine local-to-global proof of
`AlgebraicGeometry.selfTor_conormal_dual_chart_iso`, keeping its signature and the
`selfTorAffineComparisonFunctor` definition unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.SelfTorChartSquareDualization` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.

The main proof constructs the affine inverse-image cover, applies the existing proved
`SheafOfModules.existsUnique_hom_of_cover`, converts its over-top morphism into a global
module morphism, and proves that every local component is the supplied comparison.
A second new module proves the entire dualization/restriction step by explicit
precomposition of local linear maps. Both inverse identities and the coordinate-square
composition equality are proved, with no additional holes.

Added `SelfTorCompatibleAffineMaps`, containing the real predicate
`IsAffineSelfTorChartMap` and a single remaining theorem for the affine constructions
and their overlap compatibility. Its statement concerns local maps only, before
any global morphism or dual square. This is strictly the affine part of the argument;
the gluing and dualization above are real Lean proofs, not a renamed upper statement.

Updated the original DAG proof and added matching nodes for both new modules.
No existing statement, definition, public import, or unit realization was changed.

Validation: all three modules compile cleanly in import order with lcompile.py:
compatible affine maps 3.4 s, chart dualization 11.8 s, assigned module 17.2 s.
The two new node records now contain their complete Lean signatures, including
the let-bound objects; the earlier records were truncated at the first let binding.
The delivery dry run passed, with only the second reader section pending.
No files were pushed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.selfTor_conormal_dual_chart_iso`
(node `new-r4-self-tor-conormal-dual-chart-iso`).

Also proved the new theorem
`AlgebraicGeometry.selfTor_affine_chart_square_dualization`
(node `new-n1-self-tor-chart-square-dualization`), including all of its private helpers.

Added exactly one hole:
`AlgebraicGeometry.exists_compatible_affine_selfTor_maps`
(node `new-n1-self-tor-compatible-affine-maps`). Its entire proof is `:= by sorry`;
its docstring describes the resolutions, coordinate identifications, localization,
and overlap argument. No hole remains in the assigned module or in a definition.

This is a decomposition, not a complete proof from standard axioms: one upper hole
closed, one strictly local lower hole added (net zero). Existing upstream holes in
the normalized algebraic comparison and derived tensor interfaces were not modified.

Edge cases: the local construction imposes no regularity, no finite generation,
no nonemptiness, and no bound on n. Empty charts, zero quotient, zero ideal and n=0
use the same statements. Dualization is proved for arbitrary module sheaves and
an arbitrary scheme morphism; no finite presentation or dual-stalk identification
is used. The affine inverse-image cover proof also works when Z is empty.

## No longer needed

No existing import or transitively needed affine dependency is pruned. The old
proof_deps `lem-sc-affine-quotient-resolution-sheafification`,
`lem-sc-affine-open-kernel-conormal-sections`, and
`new-r4-self-tor-conormal-comparison` are no longer direct proof dependencies of
the assigned theorem: they are retained by the new local-construction node.
The second reader removed the unused public import
`WeilConjectures.AlgebraicGeometry.Modules.Dual` from the new compatible-map module;
the dualization module imports it publicly because its statement uses duality.
The rejected sandbox-only `SelfTorConormalDualChartIsoCore` and the unrelated copied
modules from the previous attempt were removed from the delivery; none was a landed
module or node, so this is not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The previous attempt was a verbatim restatement under a new name and had no matching
new-node documentation. It did not reduce the argument. This delivery replaces it
with compatible local maps, an actual cover-gluing proof, and a proved dualization
step. The claimed lack of usable gluing interfaces was incorrect:
`SheafOfModules.existsUnique_hom_of_cover` is already proved in the library.

The original source calls Tag 062I the conormal identification, but that tag proves
H1-regular implies quasi-regular. The nonregular conormal calculation needed here
is Tag 01R3 (1),(2); the new local node and docstrings cite it. Tag 0096 is the
pullback/pushforward adjunction, while the direct local-Hom description used in the
proved dualization is Tag 01CM. No statement was weakened to fix these references.

The inherited final proof treats the middle module map abstractly in a private
generic square lemma, then instantiates it once. The earlier attempt reported slow
compilation; this run did not reproduce it: all three files compile within 18 seconds.
The definitions of the actual affine functor and comparison remain unchanged.

The generic cover-gluing lemma belongs to another unit and is used as a proved tool.
The assigned unit's `realized` lists contain no node bypassed by this delivery.
Blueprint searches for self Tor, conormal Tor, and dual coordinate found no duplicate.
LeanSearch returned an unavailable-service error; LeanFinder and source searches
were performed and are recorded in the two new nodes.

## New nodes

`new-n1-self-tor-compatible-affine-maps`, in
`dag/nodes/sec-picard-framework/new-n1-self-tor-compatible-affine-maps.json`, records
only the undualized affine comparisons and their componentwise overlap compatibility.
It keeps the original three affine proof dependencies. Its Lean module is
`Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps`.

`new-n1-self-tor-chart-square-dualization`, in
`dag/nodes/sec-picard-framework/new-n1-self-tor-chart-square-dualization.json`, records
the proved precomposition/restriction argument for one local coordinate square.
Its Lean module is `Sheaf.AlgebraicGeometry.SelfTorChartSquareDualization`.

No interface-change record or forced adaptation is required.


## Second reading by N1

1. Interface preservation — PASS. Read the complete diff against the repository's
   assigned module: the two added imports are plain proof imports and the only
   other change is the original theorem's proof body. The theorem signature and
   `selfTorAffineComparisonFunctor` definition are byte-for-byte unchanged.
   There are no changed existing modules besides the assigned module, no target
   changes, and no interface-change records are needed.
2. Proof and trust — PASS as a decomposition. Recompiled all three modules in
   import order after the import repair: 3.8 s, 12.2 s, and 17.6 s, without errors
   or warnings. Scanned every delivered Lean file: the only `sorry` is the entire
   body of `AlgebraicGeometry.exists_compatible_affine_selfTor_maps`; no prohibited
   declaration, attribute, kernel-check bypass, or holed definition occurs.
   A scratch copy with explicit `#print axioms` compiled in 18.8 s. The original
   comparison functor has only `propext`, `Classical.choice`, and `Quot.sound`;
   the original theorem, both new theorems, and the coordinate predicate have
   only those axioms plus `sorryAx`. The predicate and proved dualization also
   reference the existing normalized algebraic comparison, which is selected
   by its unique-normalization theorem. The new local existence theorem is used
   inside a theorem proof, never to define an arbitrary chosen data object.
3. Split-off statements — PASS. Read the local construction and its complete
   proof docstring against Stacks Tags 09PQ, 01R3 (1),(2), and 06YH, and read
   Tag 01CM for the explicit local precomposition proof. Checked n=0 (quotient
   unit), I=0 (identity immersion, higher Tor and higher conormal exterior
   powers zero), I=A (empty closed chart), empty opens, and nonregular ideals.
   The coordinates are isomorphisms of source and target objects; they do not
   assert invertibility of the comparison. No missing regularity or finiteness
   hypothesis emerged. The remaining hole is strictly the undualized local
   construction and overlap argument. It does not assert the global map or the
   dual square. Independent LeanFinder searches used sheafification/localization
   and precomposition/restriction wording, Loogle searched Tor/exterior power,
   and source searches covered both project roots and Mathlib. No matching
   proved comparison theorem or ready-made local module-duality square was
   found. Existing gluing is correctly reused. Closing the remaining theorem
   requires the genuine affine derived-Tor comparison and localization work;
   it is not a few-minute consequence of the stated interfaces.
4. Route and pruning — PASS after report/import repairs. Traced the main proof
   from the original hole through the affine cover, proved HomCoverGluing,
   explicit over-top/global conversion, and the proved local dualization.
   Read every private dualization helper, including both inverse identities.
   This is an actual reduction, not a renamed application of the old hole.
   Read `dag/units/sk-thm-picard-duality.json`: its `realized.statement` and sole
   realized step are empty, and no fixed unit route is bypassed. All three old
   proof dependencies remain in the local-construction node and are now listed
   explicitly as moved direct dependencies under No longer needed. No existing
   module is pruned. Removed the unused public Dual import from the new
   compatible-map module; Dual remains a public import of the dualization
   module because its public statement needs it. Existing public imports remain
   unchanged.
5. DAG agreement — PASS. The only changed fields of the existing node are
   `proof`, `proof_deps`, and `proof_origin`. Checked all three proof-dependency
   lists against the unions of their steps' `uses`. Both new nodes have the
   required source, search, creation, blueprint, chapter, unit, and Lean records;
   their complete theorem signatures, including all let bindings, match their
   Lean `statement` fields verbatim. The proved dualization node records the
   componentwise elementary argument and the local node retains the three
   original affine dependencies. No new declaration is presented as a fully
   closed target: the report correctly counts one closed hole and one added
   hole, net zero.

Second-reading changes: removed one unused public import from the new local-map
module and made the dependency movement/pruning account explicit. No proof,
statement, definition, node, or unit realization needed repair.
