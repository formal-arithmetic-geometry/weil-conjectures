## What changed

Proved `AlgebraicGeometry.generic_fibre_affine_ring_models` with its signature and public
imports unchanged. Added proof imports for Mathlib localization and quotient base change,
and the new, fully proved module `Sheaf.AlgebraicGeometry.AffineFibreSectionsTensor`.

The helper `AlgebraicGeometry.affine_fibre_sections_tensor` identifies sections on the
preimage of any affine open in any fibre with its residue-field tensor product, including
the restriction equation. Its proof pastes the restriction and fibre squares, applies the
affine global-section pushout theorem, transports the four ring maps through canonical
isomorphisms, and compares with the tensor-product pushout.

For the closed fibre, tensor the canonical maximal-ideal quotient/residue-field equivalence
with the affine ring and apply quotient base change. Transport reducedness through the
resulting ring equivalences and identify the maximal ideal with the uniformizer ideal.
For the generic fibre, DVR factorization shows every nonzero denominator divides a power
of the uniformizer. Change the fraction-ring localization to localization away from the
uniformizer, tensor it with the affine ring, and use the helper's restriction equation.

Both modules compile without errors or warnings. `#print axioms` for both public theorems
reports exactly `propext`, `Classical.choice`, and `Quot.sound`. No target or existing
interface changed; no forced adaptations are needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.generic_fibre_affine_ring_models`
(lem-sbc-generic-fibre-affine-ring-models).

Also proved `AlgebraicGeometry.affine_fibre_sections_tensor`
(lem-sbc-affine-fibre-sections-tensor) in the new module. No holes added, no holes split
off, and no `sorry` remains in either delivered module. This is a complete proof, not a
decomposition into unfinished lower statements.

## No longer needed

None. All original public imports remain needed for the statement's objects or instances.
The three planned Mathlib dependency nodes remain used, with the affine fibre-product
node now reached through the proved section-ring helper. No originally required node or
module becomes unnecessary. The experimental redundant import
`Mathlib.Algebra.Category.Ring.Constructions` was removed from the new helper before delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original module had no proof-dependency imports even
though its node planned three Mathlib leaves; the required proof imports are now explicit.
The affine open must first be handled by a restricted pullback; the affine-square global
section pushout theorem makes that step shorter than manually constructing spectrum
isomorphisms. Existing finite-affine-fibre section lemmas were not used because they impose
finiteness and address stalks, which this statement does not require.

Read Stacks 055J in `more-morphisms.tex` and the affine pullback and open restriction
lemmas 01I4, 01JQ, and 01JR in `schemes.tex` from the available local literature copy.
The proof keeps the original affine/localization/quotient route and the unit route.

## New nodes

`lem-sbc-affine-fibre-sections-tensor` records the proved general affine-open comparison
in `Sheaf.AlgebraicGeometry.AffineFibreSectionsTensor`. This is the geometric first step
only; it has no DVR or reducedness assumptions and asserts neither localization nor
uniformizer-quotient reducedness. It is fully proved and introduces no future proof item.
Its dependencies are the existing affine fibre-product, open fibre-product, and spectrum
residue-field identification Mathlib leaves. Search found no identical blueprint statement;
LeanSearch was unavailable, while LeanFinder, Loogle, and source searches were recorded.

Edge cases: empty affine open (all tensor/section rings zero), zero and unit images of the
uniformizer (zero localization or quotient as appropriate), and arbitrary prime in the
helper. The arguments use pushout and localization universal properties valid for zero
rings; no nonemptiness, flatness, connectedness, or finite type assumption was introduced.
No change record is needed because no existing statement, definition, or visibility changed.

## Second reading by S1

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body changed. The helper is a new module and its declaration is recorded by the new node.
2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. The modules contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`. The proof uses only the permitted foundational axioms, as recorded in the preceding report.
3. Checked the helper statement against the affine fibre-product construction and the target statement against the original node. The helper is a strictly more general intermediate comparison, with no DVR or reducedness assumptions, and its restriction equation is exactly the property used by the target. No weaker or altered target statement was introduced.
4. Read the proof downward from the target. It uses the helper, the localization base-change and tensor-quotient results, and Mathlib's affine pullback pushout theorem. No shorter existing declaration was found in the local library or Mathlib searches recorded in the node. The original public imports remain needed; the redundant experimental import was removed from the helper.
5. Verified that the target and helper nodes retain the unit `sk-prop-normal-form` and the planned affine-fibre route. The helper realizes the affine section comparison step, while the target applies it at the closed and generic points and performs the DVR localization and quotient transports. The node proof dependencies and proof origins match the Lean proofs.

I changed only this report section; no Lean declarations, interfaces, definitions, or DAG statements were changed during second reading.
