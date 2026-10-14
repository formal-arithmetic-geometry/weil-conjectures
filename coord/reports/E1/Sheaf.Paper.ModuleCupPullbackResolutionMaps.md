## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_resolution_maps`
with a complete proof from augmented sheaf cochain maps. The proof constructs all three additive
global section maps, applies a single general class comparison to the left and right maps,
and combines that comparison with target coefficient naturality for the tensor map.
The theorem's signature and existing public imports are unchanged. Added proof-only imports
of `Sheaf.Paper.ModuleCupPullbackAugmentedPairings` and
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`.
Local transparency settings keep the existing class and pullback constructions folded during
elaboration; no existing definition or interface was changed.

Added `Sheaf.Paper.ModuleCupResolutionFMap`: its sections isomorphism and global map are actual
constructions, and its general theorem `cupResolution_class_fmap` is proved. The proof keeps
both stored injective resolutions, constructs the auxiliary injective replacement and lift,
proves the augmentation comparison by an explicit inductive homotopy, transports concrete
cycles across the two scalar rings, and cancels the homology and resolution isomorphisms.
It reuses the proved private nonnegative replacement and lift helpers through a proof-only
`import all` of `ModuleCohomologyFMap`. All private helpers in the new file are proved.

Added `Sheaf.Paper.ModuleCupPullbackAugmentedPairings` for the remaining simultaneous Godement
construction. It states sheaf cochain f-maps, their degree-zero augmentation squares, and the
strict pairing equation. It does not assert any cohomology-class equation. Updated the parent
DAG proof to match the Lean combination and added nodes for the two new modules.

All three sandbox modules compiled without errors or warnings under the standard file limit.
The final compilation took 45.1 seconds for the general comparison, 4.8 seconds for the remaining
construction statement, and 12.6 seconds for the item. No global build was run.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_resolution_maps`
(node `lem-sc-module-cup-pullback-resolution-maps`). Its proof body has no sorry.

Proved `AlgebraicGeometry.Scheme.Modules.cupResolution_class_fmap`
(node `lem-sc-module-cup-resolution-fmap`), including the concrete sections isomorphism,
the additive global map, and all private homotopy and cycle helpers. No sorry is left in this module.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_augmented_pairings`
(node `lem-sc-module-cup-pullback-augmented-pairings`). Its body is exactly `:= by sorry`.
It is the construction part of the argument and has its source and full natural-language
construction in its docstring and node. Empty schemes, zero coefficients, and degree zero
are covered by the same germ, coordinate, and augmentation equations.

Relative to the dispatched version this is a decomposition: one original hole closed and
one smaller hole added, hence a net change of zero holes before any pruning. The fetched
baseline lacks the original module; its ledger must account for the restoration separately. The general comparison part has been proved; the
whole target closure is not claimed to be sorry-free.

## No longer needed

No existing imports were removed and no modules are claimed globally pruned.
The parent's old Godement/model, flasque acyclicity, acyclic resolution, and injective
construction dependencies now belong to the remaining augmented-pairing construction.
They remain needed there. The parent directly uses only that construction, the new proved
general class comparison, the definition of cohomological pullback, and coefficient
naturality of the tensor comparison. The general comparison does not use Godement models,
flasqueness, an Alexander--Whitney pairing, quasicoherence, or flatness.

The construction dependencies no longer used directly by the parent's proof are:
`lem-sc-module-cup-godement-model-pairing-models-exist`,
`def-sc-module-cup-godement-model`, `def-sc-module-cup-godement-codegeneracies`,
`lem-sc-module-cup-godement-relations`,
`lem-sc-module-cup-godement-model-pairing-pairing`, `lem-sc-module-cup-godement-aw`,
`lem-sc-module-cup-godement-model-quasi-iso`,
`lem-sc-module-cup-godement-object-flasque`, `lem-sc-module-cup-flasque-acyclicity`,
`lemma-weil-pbc-leray-acyclicity`, and `def-sp-injective-resolutions`.
They remain in the construction node's proof_deps; injective resolutions also remain in
that of the proved general comparison. `def-pc-module-pullback` and
`def-sc-module-cup-resolution-data` supply statement data and are not discarded.
This is dependency relocation, with no claim that any of these modules is globally
unreachable. The vanished original parent node prevents an independent exhaustive diff
of its former proof_deps; the explicit current dependency accounting above is checked
against the delivered nodes.

## Where the brief, the DAG or earlier work was wrong

The dispatched module and node were present when this task began, but disappeared from the
shared checkout during the work. The required dry run fetched a baseline lacking both and
classified their restoration as a new interface. The restoration record documents this
baseline discrepancy. The theorem signature was checked against the copy read at dispatch;
it is unchanged. The parent node's restoration provenance and logged searches now satisfy
the new-node checks. No other holder's files were changed. In the fetched baseline the module
has no downstream users; it is supplied because it is the item explicitly dispatched here.


The listed one-scheme Godement existence and pairing declarations do not by themselves state
simultaneous cross-scheme f-maps preserving the chosen pairings. In particular, two independent
existential choices of pairings give no compatibility between them. The new construction node
isolates exactly that missing simultaneous construction. The original mathematical argument
is retained; no statement was disputed or weakened and no unit route was bypassed.

The class equations were not additional construction data: they follow for arbitrary computing
resolutions and arbitrary augmented sheaf f-maps. That portion is now proved once and used for
all three coefficients, with an explicit use of target coefficient naturality in the last case.

## New nodes

`lem-sc-module-cup-resolution-fmap`, in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-resolution-fmap.json`, records the proved
comparison for an arbitrary coefficient f-map and a cochain f-map of arbitrary computing
resolutions. Its module is `Sheaf.Paper.ModuleCupResolutionFMap`.

`lem-sc-module-cup-pullback-augmented-pairings`, in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-pullback-augmented-pairings.json`, records
the remaining simultaneous augmented Godement maps and strict section pairing compatibility.
Its module is `Sheaf.Paper.ModuleCupPullbackAugmentedPairings`. It has no cohomological conclusion.

Both retain the parent's chapter, unit, and theorem-of-the-cube blueprint ancestry. Searches
were run through the supplied search logger; LeanSearch returned an Internal Server Error,
and LeanFinder, Loogle and Mathlib grep supplied no replacement for either complete assertion.
No forced adaptation is required. The restoration change record is
`coord/changes/module-cup-pullback-resolution-maps-restore.md`.

`lem-sc-module-cup-pullback-resolution-maps` is also restored as a new node relative to the
fetched baseline, although it was the existing assigned node at dispatch. Its mathematical
statement and Lean signature are preserved. Its new proof records the combination actually
compiled, and its restoration provenance names E1. See
`coord/changes/module-cup-pullback-resolution-maps-restore.md` for the baseline discrepancy.

## Second reading by E1

1. Interface preservation: read all three delivered modules and attempted `diff -u`
   against each repository path. All three paths are absent in the current read-only
   repository, including the assigned parent. This is the documented restoration case,
   not an independently available before/after diff. The parent's complete signature is
   byte-identical to both the Old and New signature blocks in the restoration record;
   its scratch snapshot agrees as well. No existing repository module, target statement,
   or definition is edited. Verdict: the restored interface agrees with the preserved
   dispatch record; comparison against the vanished original cannot be independently
   repeated. The change record correctly makes this an interface/restoration delivery.

2. Proof and data: compiled the three delivered modules in import order with lcompile.py:
   41.6 s, 4.1 s, and 13.3 s, with no errors or warnings. Inspected the inductive homotopy,
   cycles-to-homology transport, sections naturality square, cancellation, and the final
   tensor coefficient naturality argument. The only textual hole is the whole proof of
   `moduleCup_pullback_augmented_pairings`; the other two theorem bodies and every private
   helper are complete. No forbidden declaration or option occurs. The two public data
   definitions construct the presheaf restriction isomorphism and its composite directly;
   no new definition chooses arbitrary data from an unproved existence assertion. The
   auxiliary injective replacement and lift are chosen inside a proof from proved lemmas.
   Verdict: a real reduction, with one construction hole remaining, not an axiom-free
   completion of the whole item. Axiom checks are recorded below.

3. Split statement: the remaining theorem asserts sheaf cochain maps over the three
   specified coefficient maps, augmentation squares, and strict pairing compatibility.
   It assumes no cohomology equations, unlike the parent. The separate proved general
   theorem establishes those equations for arbitrary computing resolutions and arbitrary
   augmented coefficient f-maps. Thus the hole isolates the construction part of the
   argument; it does not restate the parent's hypotheses and conclusion under another name.
   Read its full coordinate/Godement/Alexander--Whitney proof and corresponding node.
   Checked the empty scheme (empty coordinate products and zero sections), zero sheaves,
   degree zero (germ tensor equation), and arbitrary nonflat f (no tensor exactness used).
   The tensor coefficient uses the composite of its pullback unit with pushforward of
   the section-normalized tensor comparison, in the correct direction. No false edge
   case or extra hypothesis was found. Fresh LeanFinder search for “Naturality of the
   multiplicative flabby resolution under a continuous map of ringed spaces”, Loogle
   search `CategoryTheory.Injective, Homotopy`, and grep for flabby/flasque/cosimplicial
   naturality found supporting infrastructure but no replacement. The initial unqualified
   Loogle query was rejected for an unknown identifier and was retried qualified. Searched
   lean/ for resolution pairings, coefficient maps, and cross-scheme Godement maps;
   existing coefficient naturality constructions work on one scheme, so they do not close
   this cross-scheme construction. Verdict: mathematically sound, strictly a construction
   subproblem, with its source, full proof docstring, and node; not a few-minute closure.

4. Route and pruning: the parent uses the three augmented cochain maps, two applications
   of the general class theorem for the input coefficients, and a third application
   followed by target coefficient naturality. These are the correct respective maps.
   Public imports provide signature data; the two new imports in the parent are
   proof-only. Tried dropping the general comparison's proof-only upstream injective
   resolution import in a scratch copy: exact-zero/exact-successor constants then become
   unknown, so retained it. Functorial imports supply independence and target naturality.
   No further removable import or shorter complete route was found. Read
   dag/units/sk-prop-av-cube.json: its realized arrays are already empty, and this delivery
   neither changes the unit nor removes or bypasses any recorded realization. No module
   is claimed globally pruned. Verdict: the decomposition preserves the mathematical route
   and correctly reports net zero holes relative to dispatch.

5. DAG agreement: checked all three node files against their Lean statements byte for
   byte; checked that each proof_deps is exactly the union of the proof steps' uses and
   every dependency node exists in the repository or delivery. The parent records the
   augmented construction, general class comparison, and target coefficient naturality
   actually used. The new nodes carry their sources, complete proof steps, searches,
   creation provenance, chapter/unit/blueprint ancestry, and verbatim Lean records.
   Verdict: the Lean and nodes agree; the existing parent is a restoration relative to
   this machine's current baseline, as declared.

Changes by the second reader: expanded the dependency accounting in No longer needed and added this
independent review, its fresh searches, and scratch verification. No delivered Lean
statement, definition, proof, import, or node was changed: no mathematical repair was needed.

Axiom verification: compiled scratch copies of all three modules with `#print axioms`
for all seven private helpers, both public data definitions, and all three public
statements. Every helper, `cupPushforwardSectionsIso`, `cupResolutionGlobalMap`, and
`cupResolution_class_fmap` uses only `propext`, `Classical.choice`, and `Quot.sound`.
The remaining construction and parent use exactly those axioms plus `sorryAx`.
No unexpected axiom was found. The scratch set compiled without warnings in
45.7 s, 4.1 s, and 14.4 s per file. The parent remains conditional on the explicitly
reported construction hole; the general comparison is axiom-clean under the project
standard.
