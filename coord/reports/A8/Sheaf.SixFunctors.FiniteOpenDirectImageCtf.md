## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.finiteOpenDirectImage_constantModel_torAmplitude`
in `Sheaf.SixFunctors.FiniteOpenDirectImageCtf` from the existing
`finiteCtfInternalEtaleRealization` and `finiteEtaleOpen_uniformTorImage` declarations.
The natural-number bound is chosen before the input interval and complex. The proof
lifts the input via the inverse realization equivalence, applies the etale result,
uses bounded constructibility to place that antecedent in D+, and composes the specified
natural direct-image comparison with the input isomorphism. It transports both output
properties to the specified total internal direct image. The theorem signature and all
public imports remain unchanged. The docstring and DAG proof now describe this assembly.
No definitions, statements, source-library modules, or consumers are changed.

Validation: the item compiled cleanly through `lcompile.py` (exit code 0, 10.6 seconds).
A source comparison also confirms the original theorem signature and public imports
are verbatim unchanged, all Lean lines are at most 100 characters, and the DAG
proof dependency list is exactly the union of the proof-step uses.

The finite-discrete encoding is the already constructed normalized section-action
encoding (`encoding_exists`), rather than an arbitrary chosen module or coefficient
object. Zero coefficients, zero complexes, empty schemes, identity immersions and
degenerate ordered intervals are admitted by the two invoked declarations. In
particular the proof assumes neither a nonzero coefficient ring nor a separably closed
base field. The internal Tor predicate continues to test every degree-zero module.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.finiteOpenDirectImage_constantModel_torAmplitude`
(node `lem-sfb-finite-open-direct-image-ctf`). There are zero remaining holes in the
item and zero added holes. No new intermediate statements are introduced. The proof
uses existing declared dependencies; their pending proofs are not claimed as closed.

## No longer needed

Removed direct private imports:

- `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients`
- `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.OpenDirectImageClassicalAmplitude`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`
- `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`
- `Sheaf.Paper.OpenTorBoundArbitraryField`
- `Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`

The proof directly needs only the internal-etale realization and uniform etale
open-image interfaces, together with the normalized encoding and isomorphism
invariance already exported by the retained public imports or new private imports.
The old coefficient/projection/cohomological-dimension/comparison steps remain inside
the auxiliary nodes. Their modules and nodes are not claimed to be globally obsolete.
In particular removal of a direct import here does not withdraw an adopted source
library declaration or any dependency its proof still uses.

The node no longer directly needs `lem-weil-pbc-qcqs-over-affine` or
`lem-weil-pbc-qcqs-morphism-permanence`: the realization interface already assumes only
the displayed finite-type structure maps, and an open immersion is quasi-separated
by Mathlib instances. The same qcqs results can remain needed inside the realization
proof. The old top-level tool approvals removed as obsolete direct uses are:

- `cor-fin-deligne-open-finite-coefficients`
- `def-kun-cd`
- `det-geo-open-finiteness-ii-amplitude`
- `det-pe-finite-tor-comparison-noetherian`
- `lem-pd-module-ringed-topos-derived-comparison`
- `lem-sf-module-object-ordinary-coefficient-equivalence`
- `lem-sf-open-tor-bound-arbitrary-field`
- `lem-sf-projection-finite-constant`
- `lem-sfb-ordinary-proetale-direct-image-plus-comparison`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-qcqs-over-affine`
- `sk-thm-pe-constructible-comparison`

No modules are withdrawn, and no unit statement or proof step is bypassed. The
finite-coefficient open-image route is the same classical-image/comparison route.

## Where the brief, the DAG or earlier work was wrong

The module docstring still described the old seven-step plan, whereas the reviewed
DAG already exposed the two auxiliary statements. It has been updated to the actual
assembly. The zero-ring special case is unnecessary in the assembly because both
auxiliary declarations explicitly include zero coefficients, using the same uniform
natural-number bound. The item only asks for existence of a nonnegative bound and
never requires choosing zero for zero coefficients. No mathematical statement repair
is needed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
