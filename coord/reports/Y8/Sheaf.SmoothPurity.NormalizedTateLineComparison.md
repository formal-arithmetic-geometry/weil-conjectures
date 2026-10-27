## What changed

Proved `AlgebraicGeometry.Etale.nonempty_normalizedTateLineComparison` without changing
its signature. The proof constructs the normal integral universal base Spec Z[1/N],
compares the two lines over its generic field, descends the sheaf isomorphism through
the actual adjunction units, and pulls it back to X.

Added two fully proved public intermediate theorems in separate Sheaf modules:
`nonempty_normalizedTateLineOverField` and `isIso_normalGeneric_locallyConstant_unit`.
The first cancels a common zero-section exceptional complex using the existing
co-projection and the abstract and concrete Kummer normalizations. Scalar-extension
uniqueness and the existing root-level-independence isomorphism identify the concrete
model with the published finite-root line. The second extends the existing constant
unit theorem to locally constant module sheaves using etale base change and a
trivializing cover. It requires neither finite values nor a Noetherian hypothesis.

All new proof imports are private. Existing public imports and signatures are
unchanged. No adopted-source file was edited. The existing node's proof and proof
dependencies now describe the implemented route. Every new Lean module has a matching
node. All three files compile through lcompile.py --all without warnings; the last
compile returned exit code 0. Temporary profiler options were removed.

Edge cases checked: N=1 still gives the integral universal base Spec Z, while its
annihilator hypothesis forces the coefficient ring to be zero. No nontriviality of
that ring is used. The proof also works for an empty X; trivializing-cover members
may be empty. The generic-unit result permits arbitrary constant module values.

## Proved and sorry left

Closed the assigned module's sole hole:
`AlgebraicGeometry.Etale.nonempty_normalizedTateLineComparison`
(node `lem-sp-normalized-tate-line-comparison`). Thus 1 of 1 original sorries is closed.

Both new declarations are proved, not split-off holes:
`AlgebraicGeometry.Etale.nonempty_normalizedTateLineOverField`
(node `lem-sp-normalized-tate-line-over-field`) and
`AlgebraicGeometry.Etale.isIso_normalGeneric_locallyConstant_unit`
(node `lem-sp-normal-generic-locally-constant-unit`).

Zero sorry left in the delivered files; zero sorry added; zero split off. This is
one original hole closed, not a decomposition. Existing dependencies may themselves
still depend on project holes; no assertion of whole-target axiom closure is made.

## No longer needed

The assigned module originally imported only its statement dependencies. No original
public import is removed. Removed exploratory proof imports
`Mathlib.RingTheory.Localization.Submodule` and
`Sheaf.AlgebraicGeometry.FiniteEtaleTateLocalLine` from the field helper; the main
module still uses the latter for local triviality. The generic-unit helper uses the
smaller OpenImmersion.Conservative module instead of LocallyTrivialInverse.

The old direct proof dependency `lem-fin-normal-generic-constant`
(`Sheaf.AlgebraicGeometry.NormalGenericConstant`) is replaced by the stronger existing
module-valued normal generic constant unit and its proved local-constancy extension.
This helper is not in this proof's Lean import closure.

The old direct dependency `thm-amb-p1-adjunction`
(`Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction`) is unnecessary: the existing
concrete Tate Kummer normalization and the co-projection identify the two lines over
a field. This module is not in the resulting import closure. No declaration or
module is withdrawn.

The old direct nodes `lem-asd-etale-finite-twist-pullback` and `lem-kun-0f0g` are no
longer directly applied here: the finite-line pullback comparison is used instead,
and tensor cancellation uses the co-projection. However their modules remain
transitive dependencies of adopted-source concrete normalization code; they are
not claimed as pruned from the import closure. No upstream declaration was removed
or weakened to change that closure.

## Where the brief, the DAG or earlier work was wrong

The prescribed dependencies do not directly state either the abstract-to-concrete
field comparison or the generic-unit theorem for locally constant module sheaves.
Both gaps can be filled from existing adopted-source proofs, rather than split into
new sorry obligations. The descent argument needs no fundamental-group construction
or identification of generic fibres of arbitrary cover members: etale base change
and its actual unit equation suffice. The same construction works uniformly for
N=1, so there is no need for a separate zero-ring proof branch.

## New nodes

`lem-sp-normalized-tate-line-over-field`, in
`dag/nodes/sec-smooth-purity/lem-sp-normalized-tate-line-over-field.json`, is the proved
field-only coefficient comparison in Sheaf.SmoothPurity.NormalizedTateLineOverField.
It has no arbitrary-base descent conclusion. Its private scalar-extension helpers
are complete proofs adapted from the private helpers of FiniteEtaleTateLocalLine.

`lem-sp-normal-generic-locally-constant-unit`, in
`dag/nodes/sec-smooth-purity/lem-sp-normal-generic-locally-constant-unit.json`, is the
proved generic adjunction-unit theorem in
Sheaf.SmoothPurity.NormalGenericLocallyConstantUnit. It involves no Tate datum or
Kummer normalization. No change record is needed: existing statements and definitions
are unchanged, and no consumer is adapted.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
