## What changed

Reduced `exists_external_constant_sections_tensor_comparison` to the general balanced
presheaf morphism construction and the two existing geometric section comparisons.
The original declaration signature and public imports are unchanged. Added the proof-only
import `ExternalConstantSectionsTensorMap` and Mathlib's module restriction API.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_external_constant_sections_tensor_comparison`.
Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_external_constant_sections_tensor_map`
(node `lem-sc-external-constant-sections-tensor-map`). This is a decomposition (one closed,
one added), not a sorry-free proof. The new statement constructs a morphism on ALL opens
without geometric assumptions; it does not assert the target's affine isomorphism.
The target proof establishes affine bijectivity using the existing open comparison and
proved affine-right global-section theorem, then assembles the component isomorphisms.

## No longer needed

No original module import is pruned. The old direct proof dependency
`def-sc-scalar-global-sections-comparison` is no longer invoked directly; its definitions
remain transitively needed through the section-comparison modules. No basis or coproduct
lemma is used. Removed the unused public import
`Mathlib.AlgebraicGeometry.Morphisms.Affine` from the new helper module.

## Where the brief, the DAG or earlier work was wrong

The original elementary scalar-extension step hid the construction and O_Y-linearity of
a presheaf morphism. The existing section comparison is only k-linear, so its bijectivity
alone cannot directly supply PresheafOfModules.isoMk. This algebraic bridge is isolated
as the new node; the geometry and affine bijectivity remain in the original proof.
The unit record sk-prop-av-cube has empty realized lists, and no unit step is bypassed.
Edge cases checked in the argument: empty opens, zero coefficients, and arbitrary
non-quasi-coherent coefficients (the new statement asserts no isomorphism in that case).

## New nodes

`lem-sc-external-constant-sections-tensor-map`: a balanced O_Y-linear section morphism
on every open, together with its bijectivity criterion. Its full construction is given
in the docstring; the remaining source is Tag 0BED's degree-zero canonical cup map.
Searches were actually run and logged (LeanFinder, Loogle, Mathlib grep); no exact
presheaf morphism was found. The blueprint search for external tensor returned no match.
No definition, existing statement, or target signature was changed; no change record is needed.

## Second reading by J3

1. Diffed the delivered comparison module against the repository version. The target
   declaration signature is byte-for-byte unchanged; only proof-only imports and proof
   text were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The comparison theorem
   compiles cleanly; the only remaining `sorry` is the named split theorem
   `exists_external_constant_sections_tensor_map`. No forbidden declarations or hollow
   definitions occur. Scratch-copy `#print axioms` for both theorems returned only
   `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`. Verdict: pass.
3. Read the split statement and node. It is a genuine lower-level presheaf-morphism
   construction, strictly weaker than the affine comparison target, and its source,
   proof description, and Lean declaration agree. Checked empty opens, zero coefficients,
   and arbitrary coefficients: only a morphism is asserted, with bijectivity conditional
   on the explicit section map. Independent LeanFinder, Loogle, and grep searches found
   tensor balance (`AlgebraTensorModule.cancelBaseChange`) and presheaf tensor ingredients,
   but no existing geometric morphism with this specification. Tag 0BED was checked
   directly for the canonical degree-zero cup map. Verdict: pass.
4. Checked the proof route and imports. The existing open-section and affine-right
   comparisons are used, and `PresheafOfModules.isoMk` assembles the component
   isomorphisms; no unit step is bypassed and no removable planned dependency was found.
   Verdict: pass.
5. Checked DAG metadata and report consistency, including `proof`, `proof_deps`,
   `proof_origin`, and the new node's fields. Verdict: pass.

Removed the unused affine-morphism public import from the new helper module and
corrected the pruning report to name the removed direct DAG dependency. No proof or
statement repair was needed.
