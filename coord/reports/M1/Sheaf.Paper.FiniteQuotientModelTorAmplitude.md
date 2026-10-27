## What changed

Proved `AlgebraicGeometry.Scheme.finiteQuotient_model_torAmplitude` from a new, narrower
geometric residue-model statement and the existing
`CochainComplex.exists_projective_lift_of_nilpotent` theorem (Stacks 09AR).
The original statement and both public imports are unchanged. The new imports of
`FiniteQuotientModelResidueProjective`, `NilpotentProjectiveComplexLift`, and the tensor/quotient
identification are private proof imports.

The algebraic argument is complete Lean: for B=A/I^(n+1), the image J of I has zero
(n+1)st power. Lift the prescribed bounded projective residue complex to a projective
B-complex F representing Q(P). Its actual termwise reduction is the prescribed residue
complex. A proved private helper shows any module N with N/JN=0 is zero, since
N=JN=...=J^(n+1)N=0. This retains both endpoints of the residue interval on F.
Projective terms are flat, and the existing bounded-flat Tor theorem finishes.
The zero-complex alternative is proved directly by preservation of zero objects.
No new definitions, instance changes, or edits of other existing modules are made.

Validation: the new residue-model module compiled in 9.6 seconds. The final item
compiled in 4.0 seconds with no warnings or errors. The unchanged theorem signature
covers arbitrary original complexes P and arbitrary tensor test modules.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finiteQuotient_model_torAmplitude`
(node `lem-weil-pbc-finite-quotient-model-tor-amplitude`).
There are zero holes in the item module. Its private helper
`zero_of_nilpotent_reduction` is fully proved.

Added one hole:
`AlgebraicGeometry.Scheme.finiteQuotient_model_residueProjective`
in `Sheaf.Paper.FiniteQuotientModelResidueProjective`
(node `lem-weil-pbc-finite-quotient-model-residue-projective`).
It supplies a bounded projective model only for the algebraic DERIVED RESIDUE,
not for the original complex or its Tor amplitude. The remaining nilpotent lifting,
both support bounds, projective-to-flat conversion, isomorphism transport, and
zero-complex branch are proved in the item.

This is a decomposition: one original hole closed and one strictly smaller hole
added, net zero. No claim of an unconditional proof or net hole reduction is made.
The delivery relies on the existing projective-lifting declaration as intended by
stage 3; it does not introduce any replacement hole for that declaration.

## No longer needed

No existing Lean imports were removed; both original public imports remain because
they support the statement. No module is withdrawn, and no global pruning is claimed.

The old direct dependency `def-pc-perfect-ring-complex` is not used as a proof step:
we need only projective residue terms, not a perfectness predicate.
`prop-weil-pbc-site-comparison-finite-level` is not needed in this branch because
the input already provides the actual coefficient identifications and the local
isomorphisms on the pro-etale site. Its finite-coefficient comparison theorem is
neither imported for this proof nor invoked by the new residue-model plan.
The old explicit ideal-filtration/long-exact-sequence step
(`lem-sf-derived-homology-long-exact`) is replaced here by the existing nilpotent
projective-complex lifting theorem. That theorem may itself use cohomological
arguments; this is removal of the direct step, not a claim that its infrastructure
is unused elsewhere.

The six other old proof dependencies (constant realization, adic coefficient data,
derived restriction, tensor pullback, tensor descent, weakly-etale localization)
remain in the geometric residue subproblem. They are recorded on its new node,
rather than unnecessarily imported into the item's completed algebraic proof.

## Where the brief, the DAG or earlier work was wrong

The statement is preserved. The node's proposed coefficient-filtration proof is
mathematically valid, but the available projective-lifting theorem gives a shorter
formal route after the geometric residue identification.
The existing abstract TorAmplitudeResidueIdeal theorem cannot directly replace
that step: it also requires exact tensoring between residue modules (a semisimple
residue condition), which is not supplied here. No such hypothesis was added.

The new geometric statement was checked on n=0, the zero ideal, the zero ring,
zero and contractible complexes, and reversed intervals. It assumes a nonempty
chart; arbitrary empty-chart models would invalidate constant-stalk recovery,
and the original zero-complex alternative is handled separately. Its universal
derived functor is specified with its counit and IsLeftDerivedFunctor property;
no arbitrary witness is used to define data.

## New nodes

`lem-weil-pbc-finite-quotient-model-residue-projective` records precisely the
geometric first step of the original node. It identifies the algebraic derived
residue of the given constant model with a bounded projective complex, using a
pointed refinement of the residue cover and the normalized scalar and quotient
squares. Its source, full proof in words, searches, Lean statement, and edge cases
are recorded in the new node and module. The item node now records the actual
nilpotent lifting and support argument. No change record is needed because no
existing signature or definition is changed, and no other existing module is edited.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
