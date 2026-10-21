## What changed

The original `WeilConjectures.pointFibreDerivedTensor` statement and the canonical-system
structure are unchanged. Its proof now constructs the four-stage system and all its
canonical fields from three genuinely separate stage results: finite comparisons
including all quotient squares; integral completion including scalar squares; and
conditional rational/common-field descent from a given integral family. The field
result constructs neither of the first two families. Its common-stage normalization
quantifies over an arbitrary finite family because the formula never mentions it.
The assembly explicitly supplies the finite family already constructed.

Moved `PointFiniteSourceConstraints` and `PointIntegralTensorScalarSquare` verbatim
into the publicly re-exported compatibility module to avoid circular imports. The
change record is `coord/changes/S7-point-tensor-compatibility-location.md`.
No source-library declaration or target changed.

Validation: `lcompile.py --all` compiled all five delivery modules in import order
with exit code zero. Maximum reported single-file time: 14.2 seconds. The unchanged
compatibility bodies were also compared textually against the original declarations.

## Proved and sorry left

Closed the original hole in `WeilConjectures.pointFibreDerivedTensor` by a complete
Lean assembly of all finite, integral, rational and common-field canonical fields.
This is a decomposition, not a completed proof of the mathematics: one upper hole
is replaced by three strictly stage-specific holes, net minus two holes closed.
The original module has zero remaining `sorry` occurrences.

Every added hole:

- `WeilConjectures.pointFiniteTensorComparisons`,
  `lem-sf-point-finite-tensor-comparisons`: finite stage and quotient compatibility.
- `WeilConjectures.pointIntegralCompletedTensorComparisons`,
  `lem-sf-point-integral-completed-tensor-comparisons`: completed integral stage and scalar square.
- `WeilConjectures.pointFieldTensorDescent`,
  `lem-sf-point-field-tensor-descent`: localization and common-stage descent for an
  already supplied integral family and its scalar diagrams.

Each is in its own new module, has a sourced complete natural-language argument,
and has the exact `by sorry` body. No hole occurs in any definition. The split
contains no synonym for the original all-stage statement. Identity quotients,
identity coefficient embeddings, exponent n+1 at n=0, and independence of the
finite family in the field formulas were checked against the definitions.

## No longer needed

The assembly uses its three stage-lemma proof imports and retains
`Sheaf.Paper.FiniteTorAmplitudeSites` as the unit-route import required by preflight. Removed direct proof
imports from the original module:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.GeometricStalkToposPoint`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CoefficientFrobenius`
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.Paper.FiniteCoefficientPoint`
- `Sheaf.Paper.FiniteCoefficientTensorCtf`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Paper.IntegralResidueTor`
- `Sheaf.Paper.PointProEtaleSectionsExact`
- `Sheaf.Paper.PointSectionsDerivedReduction`
- `Sheaf.Paper.PointSectionsFiniteness`
- `Sheaf.Paper.PointSectionsScalarExtension`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`

These are removed as direct assembly imports, not claimed as globally pruned
mathematics. The original fourteen planned mathematical dependencies remain in
the proof plans of the new finite, integral and field nodes. Their declarations
were read; they are not imported merely to expose unused names in a `sorry` body.
No existing module or node is withdrawn. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The four-step DAG is mathematically the right route but does not directly assemble
at the types of the recorded functors. The ringed-point theorem produces the
section-ring tensor model, whereas the finite comparison uses the specified
lifted coefficient restriction and fixed finiteIntrinsicClosed constraints.
Its derived comparison quantifies over resolving tensor models; the requested
normalization also includes arbitrary K-flat representatives. Those transports
and constraint comparisons remain in the finite specialization.

The perfect Roos theorem concerns ordinary bounded finite-projective models, and
must be connected to the actual good-complex completed tensor, including both
Roos coordinates and the coefficient-size transport. The conditional localization
lemma uses its generic indexed integral/field package, not the recorded point
functors and their universe lift. The integral and field specializations make
these obligations explicit rather than pretending the generic declarations have
the final point signatures. No statement is marked disputed.

The first preflight rejected only the two relocated definition records because their
`lean.statement` fields included bodies. These records now contain signatures only.
Preflight also noted that parent `stmt_deps` additions are outside proof-only node
field delivery, so the parent keeps its original statement dependencies; the new
definition nodes are reached through the new stage nodes. The required unit-route
import `FiniteTorAmplitudeSites` is retained.

## New nodes

`lem-sf-point-finite-tensor-comparisons` isolates original proof step 1, finite
coefficient normalization and all quotient squares. It has no integral or field data.

`lem-sf-point-integral-completed-tensor-comparisons` isolates original steps 2 and 3,
the perfect completion argument and scalar/completion square. It assumes no field-stage result.

`lem-sf-point-field-tensor-descent` isolates original step 4, conditional on the
integral family and its actual scalar square. Its structure names the remaining
field-stage evidence used by the assembly.

`def-sf-point-finite-source-constraints` and `def-sf-point-integral-scalar-square`
record the two unchanged predicates relocated to the compatibility module.
Their new record ownership removes no mathematical condition.

Change record: `coord/changes/S7-point-tensor-compatibility-location.md`.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
