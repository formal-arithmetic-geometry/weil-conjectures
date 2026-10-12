## What changed

Proved `AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_affine_bijective_iff`
with its signature and visibility unchanged, by reducing the affine identifications to the new
module `Sheaf.AlgebraicGeometry.FlatBaseChangeAffineDictionary`.

The proof chooses compatible restricted resolutions using the existing
`flatBaseChangeMap_sections_choices`. The new theorem supplies the source and target linear
identifications, their bijectivity, and their normalizations on cohomology classes. The existing
`flatBaseChangeResolutionBeta_sections`, the adjunction unit formula, and restriction naturality
then prove the comparison square on pure tensors. Tensor induction extends this equality to all
tensors; cancellation of the two bijections proves the iff. This part is fully checked Lean.

Added three proof-only imports: `FlatBaseChangeAffineDictionary`,
`FlatBaseChangeResolutionSections`, and `FlatBaseChangeOpenChoicesExist` (all under
`Sheaf.AlgebraicGeometry`). Preserved every public import. Raised the theorem's elaboration
heartbeat limit, with an explanatory comment; the module compiles within the single-file limit.
Updated the original DAG node's proof, proof_deps, and proof_origin to the actual argument.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_affine_bijective_iff`
(node `lem-weil-pbc-flat-base-change-resolution-affine-sections`). No sorry remains in the item.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_affine_dictionary`
(node `lem-weil-pbc-flat-base-change-affine-dictionary`), in its own new module, with its whole
proof `by sorry`, source, and a complete natural-language proof. This is a decomposition:
one hole closed and one added, net zero at the level of these declarations.

The new theorem is independent of `t` and `ht` and does not mention
`flatBaseChangeResolutionBeta` in its Lean statement. It identifies the two spaces separately
and normalizes the identifications against the explicitly defined sourceClass, targetClass,
moduleCohomologyFMap, and H.baseChangeLinear. It does not assert that either base-change map is
bijective. The lift-dependent calculation is proved in the original module from the existing
section formula (which is itself an existing stage-3 dependency with sorry).

Both delivered modules compile together without warnings with `lcompile.py --all`.
The empty-open, zero-module, and degree-zero cases require no exclusions in the new statement;
its proof sketch accounts for them. No separatedness hypothesis is introduced. Existential data
are unpacked only inside the proof of a proposition; no definition chooses arbitrary data from
an unproved existence theorem. No existing definition or signature changes.

## No longer needed

No original imports were removed, and no module is claimed pruned. Every added proof import is
used. The original node's direct proof dependencies for affine geometry, qcqs higher-image
quasi-coherence, affine vanishing, Leray, higher-image presheaves, tensor-pullback sections, and
module/abelian comparison now belong to the normalized-dictionary node's proof plan. They remain
needed there and are not claimed as pruning.

## Where the brief, the DAG or earlier work was wrong

The plan's existing module/abelian natural comparison states naturality in the coefficient
module, not the needed compatibility with a change of scheme. The new theorem specifies that
missing normalization against moduleCohomologyFMap and H.baseChangeLinear. The source-library
higher-image sections theorem assumes separatedness, so it does not directly prove the qcqs
statement here; its proof and the qcqs ordinary-higher-image theorem informed the reduction.

LeanSearch was unavailable with Internal Server Error. LeanFinder and grep found pullback
adjunction/unit results but no matching normalized cohomology dictionary. Blueprint searches for
'affine sections', 02KH, and 03FD found no duplicate blueprint statement. No statement was
marked disputed or changed. The unit's realized statements and steps are untouched.

## New nodes

`lem-weil-pbc-flat-base-change-affine-dictionary`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-base-change-affine-dictionary.json`, records
`AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_affine_dictionary` in
`lean/Sheaf/AlgebraicGeometry/FlatBaseChangeAffineDictionary.lean`. It isolates the geometric
and cohomological affine identifications, before any resolution lift is chosen, from the
lift-dependent section-map calculation. Its source is Stacks 02KH with 01XJ, 01E4, 03FD,
01F7, and 01FB, and its proof follows the common-resolution and affine Leray argument.
No change record is needed: existing signatures, definitions, and public imports are unchanged.

## Second reading by U2

1. I compared the delivered target module with the repository version. The theorem signature,
   visibility, and all existing declarations are unchanged; only proof imports, the heartbeat
   annotation, and the proof body differ. The added dictionary is a new declaration with its
   own node and is recorded as a split-off hole.
2. I compiled both delivered modules with `lcompile.py --all`. They compile without errors or
   warnings. The only remaining `sorry` is the named theorem
   `Scheme.Modules.exists_flatBaseChange_affine_dictionary`; no definition contains `sorry`,
   and no forbidden declaration form was added.
3. The split-off dictionary statement is a genuine intermediate affine identification: it is
   independent of the resolution lift and of `flatBaseChangeResolutionBeta`, asserts the
   required bijective linear maps and their normalizations, and is strictly simpler than the
   target. Its docstring gives the source and a complete proof plan, and its DAG node matches
   the Lean statement and dependencies. Small empty-open, zero-module, and degree-zero cases
   are covered by the stated complex construction.
4. I checked the proof route against the imported declarations and the node records. The proof
   uses the restricted-resolution choices, the normalized dictionary, the section formula,
   naturality, tensor induction, and cancellation exactly as recorded. The affine unit route
   and the realized unit steps are preserved; no shorter existing declaration was found.
5. The new imports are proof-only imports and the public interface imports are unchanged. The
   dictionary node records the split and its source searches; no existing node statement or
   definition was altered. No imports or modules can be pruned from this delivery.

I changed only the target proof and its proof-only imports, added the split dictionary module
and node, and added this second-reading report. The target hole is closed and the dictionary
hole remains as reported above.
