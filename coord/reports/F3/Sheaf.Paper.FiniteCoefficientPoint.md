## What changed

`Sheaf.Paper.FiniteCoefficientPoint` now constructs the unique common-stage fibre
functor by a proved private quotient-descent lemma. It checks the quotient relation
by moving equivalent representatives to a common later stage, proves identities
and composition by cancellation at a common stage, and proves uniqueness by
morphism induction and functor extensionality.

The concrete further-extension equation is isolated in
`Sheaf.Paper.PointFibreRepresentativeTransport`. Its source, normalization and
complete argument in words are in its docstring and DAG node. It is strictly
smaller than the original assertion: an equality for one transported stage map,
with no functor construction, functor laws, or uniqueness in its statement.

The finite, integral, rational, and representative constructions were extracted
verbatim into `Sheaf.Paper.FiniteCoefficientPointStages` and publicly reexported
from their original module. This avoids a circular import for the transport lemma.
All 53 old public declaration signatures remain available and all non-theorem
bodies are unchanged; a source comparison checked both. Exactly 51 public
declarations move to the dependency module. All old public imports remain. The extraction was made for the
mathematical dependency, before any timeout. The corresponding record is
`coord/changes/F3-point-fibre-stage-extraction.md`.

All three delivered modules compile through `lcompile.py`. Two unchanged direct
consumers also compile against the new modules: `Sheaf.Paper.PointFibreEquivalence`
and `Sheaf.Paper.PointRationalFamilyCommonStageNaturality`. Their validation copies
are excluded from the delivery.

## Proved and sorry left

Original module: one hole before, zero holes after.
Closed: `WeilConjectures.pointQbarFibre_existsUnique`
(node `def-weil-finite-coefficient-point`), by the complete quotient construction
and the named transport theorem.

Added: one hole, `WeilConjectures.pointQbarFibreRepresentative_transport`
(node `lem-weil-point-fibre-representative-transport`), in its own module, exactly
`:= by sorry`. The stage-construction module contains zero holes.

This is a decomposition, not a net proof: one original hole closed and one
strictly smaller hole added, net zero. No hole is placed inside a definition,
private theorem, or partial proof. The chosen functor is still determined
uniquely by its object map and every common-stage morphism formula.

## No longer needed

None of the original mathematical dependencies or modules is pruned. The original
private proof imports accompany the constructions into the stage module; the
main module no longer imports those proof dependencies directly. They are still
needed for the relocated proofs. These moved imports are:

- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`
- `Mathlib.Algebra.Category.ModuleCat.Descent`
- `Sheaf.CategoryTheory.ScalarLocalizationNaturalIso`
- `Mathlib.RingTheory.Flat.Localization`
- `Sheaf.Algebra.Homology.FieldComplexCohomologySplitting`
- `Mathlib.RingTheory.Finiteness.Small`
- `Mathlib.Algebra.Module.Shrink`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `all Sheaf.CategoryTheory.ScalarLocalizationTriangulated`
- `all Sheaf.Paper.IntegralScalarExtensionWellDefined`
- `all Sheaf.Paper.PointSectionsScalarExtension`
- `all Sheaf.Paper.CoefficientComplexRationalization`

The original public imports are retained for
compatibility. No module is withdrawn and no source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The old DAG proof still said that the algebraically closed existence assertion
retained its original hole, although the rest of the stage construction was
already proved. The new final step records the actual quotient argument and
its one-step transport dependency.

The current blueprint places this material in `sec-six-functors-basics` and
formulates the algebraically closed target as the ordinary derived category,
with finite-stage descent as a consequence. The assigned library retains its
specified literal-pair model, realized by scalar extension in the ordinary
derived category. This delivery proves the assigned construction without
changing that public model or target statements. The transport lemma records
the compatibility required by its existing representative formula.

Edge cases checked: reflexive coefficient extensions, repeated stages, zero
objects, and source transitions which are not faithful. The quotient proof
uses eventual equality and the transport equation, never transition injectivity.
The generic proof also permits an empty directed indexing type; the functor and
its uniqueness are then vacuous.

## New nodes

`def-weil-point-fibre-stage-constructions` records the relocation of the existing
finite-stage constructions and their literal object/representative formulas.
It introduces no second definition of any notion and carries zero new holes.
Its Lean declaration inventory is transferred from the original node.

`lem-weil-point-fibre-representative-transport` states the equality for one
coefficient enlargement. Its proof uses the normalized sections tower equation,
the Shrink square, source associators and the target tensor-tower pentagon.
The main node now depends on it and has a fully written quotient-descent proof.

Change record: `coord/changes/F3-point-fibre-stage-extraction.md`.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
