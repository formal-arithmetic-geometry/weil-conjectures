## What changed

Completed both original proofs in `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`.
Degree preservation uses induction on powers of the inclusion range. Degreewise base change
uses the existing symmetric-algebra section tensor equivalence and homogeneous decomposition.

Repaired the return for head `5ca6a902a38`: removed the duplicate private theorem
`exists_sectionTensorEquivForGrading` and its private helpers `symmetricCongrForGrading`
and `symmetricCongrForGrading_ι`. Made the existing proved `exists_sectionTensorEquiv`
public in the unclaimed `Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineSectionComparison`,
with its type and proof unchanged, and imported and used it in the item. Added its source
and proof docstring and attached the existing helper to that module's existing DAG node.
No new declaration or new node is introduced by this promotion.

The item adds two private proof imports: `SymmetricAlgebraAffineSectionComparison` and
`Mathlib.RingTheory.GradedAlgebra.TensorProduct`. One proved private helper remains:
`graded_bijective_degree`. Existing public signatures, definition bodies, instances and
public imports in the item are unchanged. The comparison module changes only the existing
helper's visibility and docstring. No source-library file changed. No consumer needs an
adaptation. `coord/changes/P5-symmetric-section-tensor-api.md` documents the API promotion;
`coord/changes/P5-canonical-symmetric-tensor-notation.md` documents the notation scope.
The construction node records the actual proof route and its dependencies.

Remote `lcompile.py --all` compiled both modules cleanly with exit code 0:
comparison module 48.8 seconds; item 14.0 seconds.

The argument covers degree zero, zero modules, equal opens, empty affine opens and modules
without finite-generation or flatness assumptions. No basis or freeness assumption is used.

## Proved and sorry left

Closed 2 of the original 2 holes, both attached to
`def-trf-canonical-symmetric-graded-algebra`:

- `AlgebraicGeometry.SymmetricAlgebraSheaf.restriction_mem_symmetricDegree`.
- `AlgebraicGeometry.SymmetricAlgebraSheaf.gradedRestriction_isGradedBaseChangeAlong`.

No holes remain in the item or adapted comparison module. No holes were added or split off.
Every helper is proved. The existing section tensor equivalence retains its complete proof.

## No longer needed

Removed the duplicate private `exists_sectionTensorEquivForGrading` and its two private
congruence helpers. Reusing the original theorem replaces their entire construction.
Removed the retained delivery's direct private imports of
`WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange` and
`WeilConjectures.RingTheory.SymmetricAlgebraBaseChange`; these remain used inside the
original comparison module. The item therefore no longer has direct proof dependencies on
`lem-weil-pbc-quasi-coherent-affine-section-base-change` or
`lem-weil-pbc-symmetric-algebra-base-change`; it uses the existing comparison node instead.
These dependencies remain needed transitively and are not withdrawn.

No library module or node is withdrawn or globally pruned. No existing public import is
removed. The definition node originally had no proof plan; its containing unit's route
is preserved. The explicit section rings, grades and restrictions remain constructed data.

## Where the brief, the DAG or earlier work was wrong

The retained delivery repeated the existing private section tensor equivalence instead of
exposing and using the original result. This repair removes that duplication. The existing
statement is identical, including its explicit scheme, module and affine-open binders.
The original declaration could not be imported while private, so its visibility is changed
in place, with the consumer and change records included in the same delivery.

The construction node previously had no proof steps despite two named well-definedness
holes; its updated plan now records the actual Lean proof. Its mathematical statement
has not changed. No new commutator-ideal or symmetric-power theory is needed.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
