## What changed

Filled `AlgebraicGeometry.Scheme.coefficientProEtaleTor_interval_shift` without changing its
statement or the tensor-test definition. Added three proved private helpers: amplitude
invariance under isomorphism, forward interval translation using bounded flat models, and
zero amplitude. The main proof constructs the natural tensor shift isomorphism from the
published `CommShift₂Int`, composes it with the Mathlib cohomology shift isomorphism, and
assembles both directions of interval translation. The zero tensor clause uses a flat-term
K-flat representative of the degree-zero coefficient and the fixed-tensor triangulated
functor's preservation of zero objects.

The node proof and proof dependencies now follow that argument. The existing proved
`CategoryTheory.coefficientModelTorAmplitude_iff_flatModel` is used as a generic tool;
`siteSheafTensorRightIso` translates monoidal flatness to site flatness. All new imports
are private proof imports. Public imports and existing public declarations are unchanged.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.Scheme.coefficientProEtaleTor_interval_shift`
(node `lem-weil-proetale-tor-interval-shift`). Added 0 holes and split off 0 statements.
No `sorry` remains in the delivered module. This proof uses the existing stated theorem
`SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`, whose proof remains
an independent item; no claim of closing that dependency is made.

Validation: `lcompile.py` compiled the complete final module cleanly in 16.6 seconds
(exit 0, no warnings). The required delivery tool additionally probes declarations for
axioms before allowing a push. Only the project-server compilation interface is used.

## No longer needed

Removed redundant private imports
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Mathlib.Algebra.Homology.BifunctorShift`, and
`Mathlib.CategoryTheory.Shift.ShiftSequence`; the required APIs remain available through
the retained dependencies. No module is withdrawn. The old direct proof dependency `lem-pc-kflat-resolution` is
replaced by the already proved flat-K-flat representative existence in
`lem-pe-coefficient-tor-flat-model`; K-flat resolution remains needed transitively by
that theorem. Removed the obsolete direct `lem-pc-kflat-resolution` tool-use entry.

The original planned cohomology-test argument for interval bounds is replaced by the
proved bounded-flat-model criterion. `def-pc-tensor-complex-sheaves` and
`def-weil-derived-tensor` need no separate direct proof dependency: the published tensor
bifunctor and its fixed-tensor theorem already expose the required interfaces. Their
statement dependencies are retained, and their modules are not withdrawn or declared
unnecessary to other consumers. The zero calculation uses triangulated functors preserving
zero objects instead of unfolding total tensor terms.

## Where the brief, the DAG or earlier work was wrong

The recorded mathematical statement is unchanged and is consistent with the checked
edge cases: positive, zero and negative shifts, singleton intervals, zero coefficients,
and the empty scheme. The proof plan was longer than necessary for the amplitude
clauses: a proved bounded-flat-model criterion already exists. The definition actually
quantifies over K-flat representatives, so its isomorphism invariance follows directly
by composing representative isomorphisms rather than comparing tensor functors.

The compile server initially returned its busy response; no local Lean or Lake command
was used.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
