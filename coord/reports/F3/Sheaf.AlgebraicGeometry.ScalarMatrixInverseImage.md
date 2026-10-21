## What changed

Wrote a complete proof of `AlgebraicGeometry.ProEtale.scalarMatrix_inverseImage` in
`Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage`. The proof identifies scalar
endomorphisms with inverse images of the same condensed scalar endomorphism,
uses naturality of `upperStarFromPointComp`, applies the existing
`Mod.regularExtensionIso_naturality`, and passes to finite biproducts and cokernels.
The canonical regular-module and finite-free comparison definitions and all
public statements are unchanged. Identity transport is compared to the canonical
unit-comparison inverse by cancellation, avoiding expensive inverse unfolding.

Updated the assigned DAG node's proof, proof dependencies and proof-origin note
to match this argument. All helper lemmas are private and proved. The argument
uses biproduct universal properties for arbitrary finite ranks, so empty ranks,
the zero matrix, zero coefficient ring and empty schemes require no extra
hypotheses. The unit's local-coefficient-model route is preserved.

The interface check requests a record for the added file-local proof commands:
`coord/changes/F3-scalar-matrix-proof-commands.md`. This records the unchanged
public interface and the private helper commands; no definition repair is made.

## Proved and sorry left

Closes one hole: `AlgebraicGeometry.ProEtale.scalarMatrix_inverseImage`
(node `lem-sfb-scalar-matrix-inverse-image`). Added zero holes; split off zero
statements. No `sorry` remains in the delivered module, and no other Lean module
is changed.

Validation: the complete module compiled remotely in 46.6 seconds against the
current published library. Its axiom probe reports exactly `propext`,
`Classical.choice` and `Quot.sound`. The profiling option used for that check
has been removed from the delivery. Compared all existing public signatures and
both comparison definition bodies against the current shared source: unchanged.
The initial busy-server attempts pushed nothing; subsequent real compiler
checks established the proof. The delivery tool runs the final compilation and
preflight checks.

## No longer needed

Removed the redundant private imports `Sheaf.CategoryTheory.SheafTensor`,
`Mathlib.CategoryTheory.Monoidal.Bimod` and
`Mathlib.CategoryTheory.Adjunction.Limits`. Added the proof import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` for the preserved-cokernel
comparison API. All original public imports are retained.

Removed the direct proof edges to `lem-sfb-mixed-bimodule-right-unitor` and
`lem-weil-pbc-left-adjoint-preserves-colimits`: the regular-module comparison and
its naturality are already proved by
`lem-weil-pbc-regular-extension-comparison`, and the existing module-pullback
instances already supply finite-colimit preservation and additivity. No entire
module is withdrawn, and no adopted source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is valid. Its explicit balancing-coequalizer and
mixed-bimodule calculation can be replaced by the already proved regular-module
comparison API. The DAG now records that reuse. During development, implicit
object arguments in the naturality application
caused expensive conversion checks through the geometric pullback functors.
Specifying both objects as Λ fixes that conversion. Identity transport and an
explicit cancellation equation also avoid unfolding the monoidal comparison's
inverse. No definition repair was needed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
