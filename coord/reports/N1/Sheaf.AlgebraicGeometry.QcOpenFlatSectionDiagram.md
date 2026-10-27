## What changed

Completed `AlgebraicGeometry.Scheme.qc_open_flat_section_diagram`, retaining all existing
statements and definitions. A proved private helper constructs each section algebra
isomorphism from Mathlib's flat qcqs section pushout and the tensor-product pushout,
transporting the spectrum section rings by `ΓSpecIso`. The two coprojections determine
the pure-tensor formula. The main proof constructs singleton and union bounds, proves
compactness of the finite intersections, obtains quasi-separatedness and compact inverse
images, and proves the restriction square on pure tensors by comorphism naturality and
algebra-homomorphism compatibility with scalars.

Validation: the final single-file `lcompile.py` check passes without errors or warnings.
Delivery preflight additionally checks every declaration for unsupported axioms.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.qc_open_flat_section_diagram`
(`lem-a1-qc-open-flat-section-diagram`), the module's one original hole.
Added holes: none. No `sorry` remains in the sandbox Lean source.
The added helper `qcOpen_component` is private and has a complete proof.

## No longer needed

No dependency nodes or modules are withdrawn. The proof uses the existing Mathlib
flat-section theorem directly on opens, so no new open-subscheme comparison is stated.
Removed private imports `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
`Mathlib.AlgebraicGeometry.Morphisms.Separated`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, and
`Mathlib.AlgebraicGeometry.Limits`. The affine instances are already publicly
available through `Mathlib.AlgebraicGeometry.Morphisms.Flat`; the other three
imports are unused. Dropped `lem-weil-pbc-open-immersion-base-change` and the
step-3 use of `def-pc-fibre-product` from proof dependencies because the
Mathlib section theorem already works with inverse-image opens of the original
cartesian square. The fibre-product definition remains a statement dependency;
no assertion that either node is globally unnecessary is made.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The source proof in Stacks Tags 0APJ and 02KH and the
unit record `sk-p-real-rankin` were checked. The finite-intersection index is
nonempty even if every chosen open is empty, and the compactness proof does not
assume that the ambient scheme is compact. The zero ring and empty opens require
no extra hypotheses. The saved draft had not yet been validated because earlier compiler requests received
no answer. On resumption the service responded; fixed the draft's identity-map,
tensor coercion, and pure-tensor restriction proof gaps and cleared all linter warnings.
The theorem statement and every existing definition remain unchanged.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
