## What changed

Proved `AlgebraicGeometry.ProEtale.OpenInverseTranspose.canonicalRefinement_existsUnique`
in `Sheaf.SecSmoothPurity.IntrinsicCtfRefinementComparison`, preserving every existing
statement, definition, public import and docstring. Added one private, fully proved
categorical descent helper and a private proof import of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`.

The proof constructs the natural comparison at all bounded-below etale origins from the
specified support presentation, site comparison and etale common-refinement isomorphism.
The existing finite-ring origin theorem supplies antecedents for every intrinsic Dctf
input. Fullness gives naturality and independence from every antecedent; component
extensionality gives uniqueness. Updated the existing node's proof, proof dependencies
and proof origin to record this argument. No interface or consumer adaptation is needed.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.ProEtale.OpenInverseTranspose.canonicalRefinement_existsUnique`
(node `def-sp-intrinsic-ctf-refinement-comparison`). The private helper `descendIso` is
also proved. There are zero remaining `sorry` occurrences in the item and zero added
holes or split-off statements. Existing imported proof obligations remain with their
own declarations.

Validation: the complete proof compiled with the required remote compiler. Its final
component calculation now uses the compiler-suggested explicit simplification lemmas;
delivery preflight supplies the final compilation and axiom check.

## No longer needed

No imports removed and no module withdrawn. The proof uses the original specified
etale/support/site comparisons and the finite-ring origin theorem. The fixed-module
etale-origin comparison `def-pur-origin-compactification-comparison` is not used as a
proof dependency: its intrinsic presentation and all-origin normalization are built
directly from the comparison factors already appearing in `refinementModel`. Its
statement reference remains because it describes the construction being presented.
No unit statement or proof step is bypassed, and no dependency module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The declaration's existing mathematical proof sketch is sufficient. The definition node
had empty `proof` and `proof_deps`, even though its existence-and-uniqueness theorem had
a hole; these fields now record the actual proof. The needed full bounded-below derived
Hom bijection already exists with a proved source-library declaration and the node
`lem-weil-pbc-fixed-module-derived-hom-bijection`; no replacement lemma is needed.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
