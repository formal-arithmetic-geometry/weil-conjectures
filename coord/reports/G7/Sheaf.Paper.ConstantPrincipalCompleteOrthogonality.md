## What changed

Proved `CategoryTheory.ConstantCompletion.constantPrincipalComplete_of_orthogonal`
inside its original module, with its signature and public import unchanged. Added
four proved private helpers for kernel-section divisibility, invertibility on
localizations, transport of orthogonality to a slice, and internal-Hom vanishing.
Only proof imports were added. The DAG proof now records this argument.

The proof uses the existing constant quotient kernel description, the exact left
adjoint of slice restriction, and the existing native symmetric derived tensor
and its tensor-Hom adjunction. The two exact functors' adjunction is descended
from complexes through the standard derived localizations directly. This avoids
assuming exact countable products or boundedness. No shared interface changed.

Tools from other units are `new-localized-restriction-extension-exists` (the exact
slice left adjoint), `lem-sf-ringed-derived-native-tensor` (the symmetric tensor)
and `lem-sf-ringed-derived-tensor-hom-adjunction` (its recorded right adjoint).
The assigned unit's declared local completeness and constant quotient interfaces
do not provide these general categorical constructions. They supply tools for
the local orthogonality argument without replacing any unit-level proof step.

## Proved and sorry left

Closed the original one hole in
`CategoryTheory.ConstantCompletion.constantPrincipalComplete_of_orthogonal`
(node `lem-sfb-constant-principal-complete-orthogonality`). No holes added or split
off. All four private helpers are proved. Zero textual `sorry` remains in the
item. Existing dependencies may themselves rest on unfinished proofs, as allowed
by stage 3; their holes are not claimed closed here.

Validation: the item compiled through `lcompile.py` with no errors or warnings in
11.2 seconds. Its public signature is byte-for-byte unchanged. All lines are at
most 100 characters. The delivery tool runs the final compile and preflight.

## No longer needed

No existing import, node or module was pruned. Both original dependencies remain
needed: the constant coefficient and kernel interface, and the local completeness
definition. The old plan's explicit telescope construction, shifted free generators
and descent argument are unnecessary: tensor-Hom adjunction with the internal-Hom
object itself tests its identity, and the existing kernel description supplies
sectionwise divisibility. These were unstated planned steps, not modules to withdraw.
No unit-level statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original two declared proof dependencies do not themselves state the
orthogonality comparison. Existing library declarations supply its missing
categorical steps, so no further split of this obligation was needed. The stated
regularity hypothesis is retained verbatim; this argument does not need it beyond
the original statement. The zero ring, unit scalar and zero scalar are covered:
localization inversion, exact adjunctions and the identity-zero criterion remain
valid in those cases. An empty site requires no local tests.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
