## What changed

Filled `AlgebraicGeometry.Scheme.coherent_hom_ideal_power_extension` in
`Sheaf.AlgebraicGeometry.CoherentHomIdealPowerExtension`, with its original signature,
visibility and docstring unchanged. Added proof-only imports for existing tensor extension,
image lifting, the ideal zero locus, affine ideal-power sections, free-generator section
naturality, the quasi-coherent unit, and the quasi-coherent unit. No public imports were removed.

The extension and image-lift lemmas already implement the main steps of Tag 01YB.
The delivered proof supplies the remaining Lean glue: derive the support complement from
hU, conjugate the local map through overFunctorEquiv, identify recursive and ideal-data
powers by their affine ranges, transport the product image, and compose the lift with
the tensor extension. Faithfulness and naturality transport the final equality back to
exactly the original overFunctor statement. Private, fully proved affine-basis and
image helpers follow the existing proofs in ClosedImmersionIdealPowerImage and
ModulePullbackIdealPowerProductImage; those unrelated geometric modules are not imported.

Single-file lcompile.py succeeded without warnings. The unit sk-thm-p1 route is preserved:
this item is below its realized steps, and the proof follows the same 01YB argument.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.coherent_hom_ideal_power_extension`
(node `lem-weil-pbc-coherent-hom-ideal-power-extension`).
No sorry remains in the delivered module; no new sorry or new module is added.
All five private helpers are proved. Existing geometric dependencies may still rest on
sorry, as allowed in stage 3; this is a proof from existing declarations, not a claim
that the full transitive axiom closure is already sorry-free.

## No longer needed

Removed the redundant added proof-only import `Mathlib.CategoryTheory.Subobject.Limits`
during the second reading; its image lemmas are already available. All original imports
are public and support the signature.
Globally pruned modules: none claimed, since the original node's lower theory is still
used transitively by the existing tensor extension and image-lift lemmas.

The following former direct proof dependencies are no longer invoked directly by this
module; their roles are subsumed by the existing geometric lemmas (this is a dependency
record simplification, not a claim of global pruning):

- `def-pur-sheaf-hom`
- `def-weil-pbc-coherent-formal-module`
- `def-weil-pbc-module-finite-type-presentation`
- `lem-weil-pbc-coherent-artin-rees`
- `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-module-finite-type-submodule-extension`
- `lem-weil-pbc-module-tensor-hom-adjunction`
- `lem-weil-pbc-noetherian-acc-quasi-coherent`
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`
- `lem-weil-pbc-quasi-coherent-module-kernel`
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`
- `lem-weil-pbc-sections-annihilated-by-ideal`
- `lem-weil-pbc-sections-over-quasi-compact-open`
- `lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent`
- `pqf-lem-coherent-ft-locnoeth`

## Where the brief, the DAG or earlier work was wrong

The DAG did not name the already existing `lem-pc-coherent-open-map-tensor-extension`
and `lem-pc-ideal-power-tensor-image-lift`, which package its main geometric steps.
Their statements fit without changing any signature. The missing bridges were between
ideal-data and recursive powers, and between restrictFunctor and overFunctor, and are
fully proved here. No mathematical error or disputed statement was found.

The local literature/stacks-project/coherent.tex copy is absent on this machine;
Tag 01YB was checked at its official Stacks page. No new source-dependent statement
was introduced. No definition, public interface, consumer module or unit was changed.

## Second reading by E1

1. The delivered module was diffed against the repository version. The target
   declaration and all existing signatures are unchanged; only proof-only imports,
   private proof helpers, and the target proof were added.
2. The module compiles cleanly with `lcompile.py`; it contains no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`. A scratch copy with
   `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` from existing dependencies. The proof uses only existing declarations
   and private proved helpers.
3. The target statement is unchanged and the five private helpers are true, strictly
   intermediate facts needed by the proof. No split-off statements or new holes were
   introduced. Similar affine and power helpers in the two modules cited in the
   comments are private, so importing those modules would not expose these helpers.
4. The proof follows the shortest available route through the existing tensor-extension,
   image-lift, and affine ideal-range lemmas. Unused former dependencies are recorded
   above; all added imports are proof-only. Removal probes show FreeGenerator is
   needed for app_presheaf_map and Quasicoherent for isQuasicoherent_unit; the
   Subobject.Limits import is redundant and was removed. The unit record was read:
   this item is below its realized steps, and the unit route is kept.
5. The DAG node proof, proof dependencies, and proof origin match the delivered Lean
   proof, with the original target statement preserved byte-for-byte.

Changed the report and removed the redundant proof-only Subobject.Limits import.
The first worker already synchronized the node metadata; no further DAG or
mathematical change was needed.
