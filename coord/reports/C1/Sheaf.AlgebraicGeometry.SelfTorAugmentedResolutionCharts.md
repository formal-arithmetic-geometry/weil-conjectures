## What changed

Replaced the sole sorry in `AlgebraicGeometry.exists_selfTor_augmented_resolution_charts`
by a complete Lean assembly proof, with its original statement and visibility unchanged.
The proof obtains ambient charts on Y, pulls each local isomorphism back to Z using
canonical adjunction-unit normalization, moves the restriction before the unit by
naturality, applies the ambient chart equation, and reverses the target normalization.
The explicitly specified homology map q is unchanged.

Added three modules, each with one public statement:

- `SelfTorAmbientResolutionCharts`: the remaining ambient derived self-Tor comparison,
  before any pullback to the closed subscheme. This is the only new sorry.
- `TensorPullbackLocalIsomorphism`: proved that a map invertible over U remains invertible
  after tensor pullback over its inverse image. The proof uses the existing natural
  restricted stalk comparison, base change of a linear equivalence, and stalk detection.
- `TensorPullbackOverIsoUnit`: proved a normalized pullback comparison for arbitrary
  local sheaf isomorphisms. It uses localization into the right adjoint of overFunctor,
  the preceding local-isomorphism lemma, naturality on U intersect V, and naturality of
  the canonical pullback unit. It reuses the private counit-isomorphism theorem of
  `TensorUnitOpenLocalization` through a proof-only `import all`, without copying it.

All old public imports stay unchanged. Added imports of the two assembly dependencies
are proof-only. The ambient residual module also imports the four modules named by
its proof plan, using proof-only imports. No existing definition, statement, instance, or visibility changes.
The two backward elaboration options on the item's theorem are declaration-scoped.
No forced adaptations or change records are required.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_selfTor_augmented_resolution_charts`
(node `new-p4-self-tor-augmented-resolution-charts`).

Added one remaining hole:
`AlgebraicGeometry.exists_selfTor_ambient_resolution_charts`
(node `lem-pc-self-tor-ambient-resolution-charts`).
It contains no pullback to Z and no pullback-unit assertion: its output is the affine
self-Tor comparison with the ambient homology sheaf on Y. This is a decomposition,
not a net decrease in holes (one closed, one added).

The two new public helpers
`AlgebraicGeometry.Scheme.Modules.tensorPullback_map_over_isIso` and
`AlgebraicGeometry.Scheme.Modules.exists_tensorPullback_over_iso_unit`
are proved without sorry. There is no sorry in any definition or in the assembly proof.
The independent axiom probe shows both new pullback helpers depend only on
propext, Classical.choice and Quot.sound. The ambient comparison and original
theorem additionally depend on sorryAx, as expected for this decomposition.

The full sandbox was compiled in dependency order with lcompile.py. Each module
compiled below the 60-second limit, with no warnings. The delivery dry run also checks
the axiom probe and static preflight before READY is reported.

## No longer needed

Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification` and
`Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`.
Their declarations do not prove the assembly step, so they are not imported there.
They remain relevant to the proof plan of the ambient residual theorem; this is
relocation of the unresolved calculation, not a claim that those nodes can be deleted
or are globally pruned. The original DAG node had no recorded proof_deps to prune.
No module is claimed to leave the targets' import closure in this delivery.
No chosen-resolution comparison above this item is imported: that would create a cycle.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof was one sentence with no dependencies, although the module's
prose requires an affine derived comparison and its naturality. Its imported
sheafification theorem only supplies an augmented quasi-isomorphism, and the K-flat
criterion only supplies K-flatness; neither states the chart comparison being used.
The new ambient node makes that missing part explicit, and the original node records
the actual Lean assembly route.

The original prose says the ideal-annihilation calculation is needed before tensor
pullback. For this reduction, an isomorphism already constructed on Y can simply be
pulled back, so no annihilation theorem is needed in the pullback step. The ambient
calculation itself still has to be proved from its chosen resolutions.

The inherited immediate blueprint.from record points to another created node rather
than the blueprint ancestor. New nodes use the ancestor `lem-sc-finite-duality` recorded
on the parent of this item, with the intervening chain; the unit realization is not
changed. Searches across blueprint nodes for affine derived tensor and open pullback
returned no duplicate. LeanSearch returned HTTP 500 and is recorded as unavailable,
not as a successful search with no matches.

Checked the source statements at Stacks Tags 08DX(2), 06YG, 00LS, 0096, 0097, and 0098.
The remaining ambient claim includes n=0, zero quotient rings, and empty basic opens:
its proof uses exact functors and augmented resolutions, with no division by a
nonzero localization element. Both proved pullback helpers apply to all scheme maps
and all module sheaves, without flatness, quasi-coherence, or nonempty-open assumptions.
The stalk argument for an empty inverse image is vacuous, as required.

## New nodes

`lem-pc-self-tor-ambient-resolution-charts` states precisely the unresolved affine
comparison on Y and its compatibility with all supplied augmented tensor comparisons.
It is strictly the ambient part of the argument, and does not repackage the pullback
conclusion or assume charts on Z.

`lem-pc-tensor-pullback-local-isomorphism` records the proved generic preservation of
local isomorphisms. Its proof uses `new-e1-restricted-tensor-pullback-stalk` and existing
Mathlib and upstream stalk/equivalence APIs.

`lem-pc-tensor-pullback-over-iso-unit` records the proved generic normalization of the
pullback of a local isomorphism on canonical unit sections. Its only project-specific
proof inputs are the preceding helper and the existing counit-isomorphism proof from
`lem-sc-tensor-unit-open-localization`.

No change record was created because no existing interface changed.

## Second reading by C1

1. Compared the delivered existing module with the repository using diff and compared
   the complete theorem signature as bytes: identical. The original docstring and
   all public imports remain unchanged. No existing definition, instance or
   declaration visibility changes. No change record is needed.
2. Compiled all four modules in dependency order using lcompile.py, without errors
   or warnings, each under 60 seconds. Recompiled the ambient module after the
   import repair. A separate scratch module printed axioms for all four delivered
   declarations: the two generic pullback helpers use only propext, Classical.choice
   and Quot.sound; the original theorem and ambient residual additionally use
   sorryAx. Static inspection finds exactly one sorry, the whole proof of the named
   ambient theorem, and no forbidden declaration or hollow definition. Removed
   the scratch source before delivery.
3. Read each new statement and proof. The only residual hole is the ambient
   affine derived-Tor calculation, a strict part of the original argument: it
   contains neither pullback nor canonical pullback-unit normalization. The
   original theorem proves the omitted pullback step with the two fully proved
   generic helpers, so this is a decomposition, not a renamed application.
   The ambient docstring supplies the resolution construction and naturality
   argument and its node records the missing comparison. Checked degree zero,
   identity and empty basic inclusions, zero quotient rings, and empty inverse
   images: no nonzero element, flat map, or nonempty-open assumption is needed.
   Independently checked Stacks 08DX(2), 06YG and 0098. Fresh LeanFinder queries
   about sheafification of derived-tensor homology and preservation of neighborhood
   isomorphisms, a fully qualified Loogle isoLeftDerivedObj query, and rg searches
   of the library found supporting APIs but no duplicate statement. Existing
   affine derived-tilde homology comparison supplies only the exact-functor step,
   not the augmented self-Tor chart naturality. The ambient hole cannot be closed
   by one of these APIs in a few minutes.
4. Read the assembly downward: ambient charts, local-isomorphism pullback with unit
   normalization, unit naturality, then the ambient section equation. Every new
   helper is used. The old proof_deps was empty, hence there are no omitted old
   dependency nodes to list. The two removed direct proof imports remain in the
   ambient proof plan; no global pruning or net decrease of holes is claimed.
   Read dag/units/sk-thm-picard-duality.json: its realized fields are unchanged and
   the new nodes remain below that unit. No unit statement or step is bypassed.
5. Compared all four node proof plans and dependency unions with the Lean. The
   original node describes the actual assembly; both generic nodes describe their
   fully written proofs; the ambient node records its unresolved resolution proof.
   The new node Lean declarations and statements agree with their modules and all
   required provenance, source, search, chapter and unit fields are present.

Changed the ambient module to import the four existing modules named in its
proof_deps, all proof-only: AffineQuotientResolutionSheafification,
BoundedAboveFlatRingedSpaceKFlat, AffineDerivedPullbackTensorTilde and
KFlatDerivedTensorComparison. A source-import traversal confirms none reaches
SelfTorAmbientResolutionCharts, so this introduces no cycle. Updated this report
with the actual axiom results and the import repair. No proof or signature repair
was necessary; one original hole is closed and one ambient hole is added (net zero).
