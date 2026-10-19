## What changed

Filled both proofs in `Sheaf.Paper.ProjectionFormulaIdentityCompactification`.
Retained the proof-only import `Sheaf.Paper.ProjectionFormulaCompactified` and added
private identity-coefficient, module-pushforward, derived-pullback and
derived-open-extension isomorphisms. The coefficient map is fixed by adjunction conjugation and its unit
identity, rather than chosen from mere existence. Specializing the compactified
formula to `(1_X,f)` proves invertibility at the extended object; first-variable
mate naturality transports it to E. The final four conjuncts use the functor left
unitor, reflexivity and preservation of identities. Existing public signatures,
definitions and docstrings are unchanged. The node proof now records this argument.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Scheme.IdentityProjectionCompactification.mate_isIso`.
- `AlgebraicGeometry.Scheme.IdentityProjectionCompactification.identity_compactification`.

Both belong to `lemma-weil-pbc-projection-formula-identity-compactification`.
No `sorry` remains in the delivered module; no holes or split-off modules were added.
The proof uses the existing stated `proEtaleProjectionFormula_compactified` and
`derivedProjectionFormulaMate_naturality`; their outstanding proofs remain upstream
obligations, as required by stage 3.

## No longer needed

Removed redundant direct proof-only imports `Sheaf.Paper.OpenImmersionTensorPiece`,
`Sheaf.Paper.ProEtaleProjectionFormulaArrows` and
`Sheaf.Paper.ProjectionCompactification`; the retained compactified-formula import
already supplies their APIs. No module is withdrawn. The open-piece node
`lemma-weil-pbc-projection-formula-open-piece` is no longer a direct proof dependency:
the normalized identity theta is definitionally identity, and invertibility comes
from the compactified formula. Its module `Sheaf.Paper.OpenImmersionTensorPiece`
remains a transitive dependency of `Sheaf.Paper.ProjectionFormulaCompactified`;
this delivery does not claim it is globally pruned. The compactification definition,
compactified formula and projection arrows remain used. The existing operations and
first-variable naturality nodes are recorded as direct dependencies of the concrete
identity construction and transport argument. The unit's statement and realized
proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing normalized identity-open presentation is retained. The DAG's informal
substitution did not supply the isomorphism from the actual chosen extension-by-zero
functor to the identity; this proof constructs that isomorphism using the coefficient
unit equation, module pushforward congruence and adjoint uniqueness. Naturality is
needed to transfer the compactified theorem from that chosen extension of E to E.
No mathematical statement repair or consumer adaptation is needed.

The resumed dry run flagged the added public `open Opposite` command as an
interface change. Removed it and qualified the opposite-category rewrite lemmas;
the original public command environment is retained.

Validation: on resumption, checked the retained module against the current source
and dependency signatures. The single-file server compile passed in 5.2 seconds
with no diagnostics. The module has zero textual `sorry` tokens, all lines are at most 100
characters, and the updated DAG dependencies have no path back to the item. Earlier
compile-server response failures were retried without changing the tools.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
