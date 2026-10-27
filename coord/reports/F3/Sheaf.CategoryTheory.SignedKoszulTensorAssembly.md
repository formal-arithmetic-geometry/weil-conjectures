## What changed

Proved `CategoryTheory.isColimit_ringedNegativeKoszulTensor_of_basis` in
`Sheaf.CategoryTheory.SignedKoszulTensorAssembly`, with its statement unchanged.
For every pair of degrees, tensor preservation transports the supplied basis
coproduct. Its universal map uses the right unitor and the degree equation
p+n=q to send a supported subset to the corresponding coefficient term.
`HomologicalComplex.mapBifunctorDesc` assembles these maps. Factorization follows
from the two coproduct factorization identities and cancellation of the right
unitor. Uniqueness follows from total-tensor extensionality, followed by
extensionality for the transported basis coproduct and the same degree equation.

Corrected the two blueprint tags in the module to its own attached node,
`lem-cbc-signed-koszul-tensor-assembly`. The proof follows that node's existing
plan; no new statements or dependencies are needed.

## Proved and sorry left

Closed the sole hole:
`CategoryTheory.isColimit_ringedNegativeKoszulTensor_of_basis`
(`lem-cbc-signed-koszul-tensor-assembly`). Zero holes remain in the item and zero
holes are added elsewhere. This is a proof, with no split-off statements.
The supplied hypothesis is used directly; the separate recursive basis theorem
remains the responsibility of its existing module.

## No longer needed

None. Kept the public import of `SignedKoszulBasisCoproduct`: besides providing
the model definitions, it supplies `isColimit_ringedNegativeKoszulBasis_succ`
to the existing direct importer `SignedKoszulTensorCoproduct`. No module or DAG
node is withdrawn. No differential, boundedness, tensor-coordinate, or completion
lemma is required by the assembly proof.

## Where the brief, the DAG or earlier work was wrong

The original docstrings cited the parent coproduct node instead of the module's
own assembly node; corrected those tags. The mathematical statement and existing
proof plan needed no repair. The universal-property proof makes no nonzero-ring,
nonempty-site, or boundedness assumption; empty supported index types are handled
by the same preserved coproduct universal property.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
