## What changed

Reduced `AlgebraicGeometry.schemeMV_image_composition_localization_core` to two
independent normalization equations. Its proof composes the left normalization with
the symmetry of the right normalization. Both existing theorem signatures and the
existing final theorem's proof are unchanged.

The common expression is explicit: Q of the complex composition comparison, the open
direct-image unit, and open derived direct image of the restricted-direct-image unit,
the inverse exact X-restriction factor, and the inverse derived restriction comparison.
The left equation involves the h-localization unit and derived composition comparison,
but no image component or exact Y-restriction factor. The right equation involves the
image component and exact Y-restriction cancellation, but no h-localization unit or
derived composition comparison. Thus neither is the original assertion renamed.

Two supporting ingredients are fully proved in their own modules: the underived image
isomorphism cancellation and transport of the homotopy composition-unit equation to
complexes. Their nodes are used in the plans of the two remaining normalization nodes.
No existing definition, statement, instance, or visibility is changed; no adaptations
of other modules are required.

All five delivered Lean modules compile through lcompile.py. The new left and right
normalization statements take about seven seconds each and the core module about four
seconds in that check. No compile limit was raised.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.schemeMV_image_composition_localization_core`.
Its closure is a decomposition, not a net proof: two strictly separate obligations are
added, each with proof exactly `by sorry`:

- `AlgebraicGeometry.schemeMV_composition_left_normalization`.
- `AlgebraicGeometry.schemeMV_composition_right_normalization`.

These are every sorry left in the delivered modules. The net change is one hole added
(one original hole closed, two added), before any pruning accounting.

Fully proved new supporting declarations:

- `AlgebraicGeometry.schemeMVImageIso_composition_factor`.
- `AlgebraicGeometry.schemeMVOpenComposition_complex_localization`.

`AlgebraicGeometry.schemeMV_image_composition_localization` retains its complete proof
from the core. The existing upstream `schemeMVOpenComposition_unit_normalization`
remains a planned dependency of the left normalization, not a claim of this delivery.

## No longer needed

No mathematical DAG node or module is permanently pruned. The direct proof import of
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisOpenCompositionNormalization` is removed
from the core module; its role moves to the left normalization's proof plan through
the proved complex-localization helper. The core imports only the two normalization
statements, in addition to its unchanged public restriction-localization-chain import.

The two proved ingredient modules are delivered for the next proofs and referenced by
the new nodes; the sorry-only normalization modules do not import unused proof modules.
Temporary generic pasting helpers and experimental Mathlib `import all` lines are not
included. No K-injectivity lemma, resolution lemma, or restriction-unit normalization
is required by this route.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. Empty and full opens, identity morphisms,
and arbitrary complexes obey the same naturality and inverse-isomorphism identities.
No assumptions are added. The earlier attempt had not closed the core; this delivery
makes its two remaining complete normalization calculations explicit and separately
reviewable, rather than treating unchecked conversions as a proof.

The dry-run restatement heuristic initially classified the two-theorem transitivity term
as one application of the left theorem. The proof now names both input equations
explicitly before combining them, making the two independent obligations visible.

## New nodes

`lem-pc-mayer-vietoris-image-component-composition-factor` records the fully proved
underived image cancellation. Its module is
`Sheaf.AlgebraicGeometry.MayerVietorisImageComponentCompositionFactor`.

`lem-pc-mayer-vietoris-open-composition-complex-localization` records the fully proved
transport of the existing homotopy normalization to complexes. Its module is
`Sheaf.AlgebraicGeometry.MayerVietorisOpenCompositionComplexLocalization`.

`lem-pc-mayer-vietoris-composition-left-normalization` records normalization of the
left-hand composite by the composition-unit equation and naturality of the exact
X-restriction factor. Its module is
`Sheaf.AlgebraicGeometry.MayerVietorisCompositionLeftNormalization`.

`lem-pc-mayer-vietoris-composition-right-normalization` records normalization of the
right-hand composite by image cancellation, naturality of the open direct-image unit,
and cancellation of the exact Y-restriction factors. Its module is
`Sheaf.AlgebraicGeometry.MayerVietorisCompositionRightNormalization`.

All four nodes have exact Lean statements, source references, complete proof plans,
search records, and provenance from the existing core node. There are no definition or
statement change records and no forced adaptations.

## Second reading by F3

1. Compared the delivered item module with the repository version. Existing declaration signatures and statements are byte-for-byte unchanged; only the core proof and its proof-only imports changed.

2. Compiled all five delivered modules with `lcompile.py --all`. Compilation succeeds with no errors. The only remaining `sorry`s are the two named normalization theorems, each public, documented, and represented by a DAG node; no forbidden declarations or hollow definitions occur.

3. Read each new statement and its node. The two normalization statements are strictly separate reductions of the core identity, while the image-factor and complex-localization helpers are fully proved and used by those reductions. Their hypotheses and conclusions match the displayed Lean types and are mathematically valid in empty, full, and identity-open cases.

4. Checked the proof route and pruning. The core now uses only the left and right normalization declarations; the former direct import of `DerivedMayerVietorisOpenCompositionNormalization` was removed from the core and retained only as a proof import of the complex-localization helper. No unused proof import remains in the new modules, and no unit route is bypassed.

5. Checked DAG agreement. The four new nodes record the exact declarations, proof dependencies, source and provenance; the core node records the composed proof and its two normalization dependencies. The unit realization remains unchanged.

Changed during second reading: added this review section to satisfy the delivery contract; no Lean statements or proofs required repair.
