## What changed

Proved `CategoryTheory.ConstantCompletion.inverseImageData_exists` from a strictly
smaller ring-only constituent. Added `Sheaf.CategoryTheory.GeometricRingInverseImage`,
containing the ring-only `RingInverseImage` record and its coherent existence lemma.
The assigned module constructs module inverse image with the existing proved
`SheafOfModules.GeometricConstruction.imageFunctor` (via `import all`). Its private
`ringTransport_algebraic` proves the binary transport equations, addition, zero and
scalar-action graph laws, and preserves the supplied ring-underlying comparison.
The final proof assembles all fields of the original `InverseImageData` unchanged.
No existing signature, definition, attribute, public import, or source-library file
is changed. Other private proof imports are replaced by the two modules used here; the
inherited unit-route tower-comparison import is retained.

Validation: the new ring-only module compiled in 6.6 seconds, and the assigned
module compiled with no errors or warnings in 12.1 seconds through `lcompile.py`.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.ConstantCompletion.inverseImageData_exists`. The private theorem
`ringTransport_algebraic` is proved with no holes: it constructs all module data and
checks the generalized-section equations over the specified ring transport.

Added one hole:
`CategoryTheory.ConstantCompletion.coherentRingInverseImage_exists`, node
`lem-weil-pbc-coherent-ring-inverse-image`. Its conclusion contains only the coherent
ring functor, ring operations, ring-map naturality and constant-ring comparison.
It contains no module category, module functor, module action or module graph law,
so this is a proper constituent, not a renamed or repackaged target. Its docstring
and node give the source and complete argument. This is a decomposition (one hole
closed, one added), not a net proof-count improvement. The assigned module has zero
remaining holes; the delivery has one.

Edge cases: identity inverse image gives identity transport; zero coefficient rings
and degenerate sites are allowed. The ring-only lemma needs neither points nor
nontrivial rings. Module graph proofs use arbitrary test sheaves, including the
terminal test object for constants, and arbitrary sections, not just global ones.
The scalar-action proof explicitly cancels the two directions of the coefficient
isomorphism; no faithfulness of L is assumed.

## No longer needed

The following inherited private imports are unused by this existence proof and are
removed from the assigned module:

- `import WeilConjectures.CategoryTheory.NatTransFromResolvingClass`
- `import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`
- `import Sheaf.Paper.KFlatRingedToposPullback`
- `import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`
- `import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat`
- `import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
- `import Mathlib.RingTheory.Ideal.Span`
- `import Mathlib.RingTheory.Finiteness.Defs`
- `import Sheaf.Paper.RingedTopoiTensorSections`
- `import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison`
- `import Mathlib.CategoryTheory.Adjunction.Whiskering`
- `import Mathlib.CategoryTheory.Adjunction.Additive`
- `import Sheaf.Paper.RingedTopoiDerivedPullback`
- `import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
- `import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`
- `import Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`

The inherited private `import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
also stays because the preflight identifies it as a unit-route module. All inherited
public imports stay for existing importers. No globally prunable node
or module is claimed: the parent node also owns the other constant-completion
results. The completion, derived tensor, quotient-tower and Koszul dependencies
remain needed by those other results. The new module proof uses the proved
finite-product module construction, not the constant-left-module inverse-image
existence theorem: the latter is restricted to constant coefficient rings and
does not supply the varying-ring data required here.

## Where the brief, the DAG or earlier work was wrong

The maintainer split left `inverseImageData_exists` attached through the broad
constant-completion node rather than an existence-only proof step. Added a precise
step to that node without replacing its other seven proof steps or changing its
statement or unit route. The whole-ring/module lift was not available as a single
existing theorem. Objectwise algebraic presentation existence alone does not
provide the required functorial ring maps and natural constant-ring comparison.

## New nodes

`def-weil-pbc-ring-inverse-image`: the ring-only fragment of the existing algebraic
presentation. Its four operation graph conditions are unchanged in meaning from
the ring fields of `AlgebraicInverseImage`. It is a proof interface, and does not
replace any existing notion or give a new coefficient construction.

`lem-weil-pbc-coherent-ring-inverse-image`: coherent ring transport and constant
coefficients, from Stacks 00YV. The proof plan uses the existing internal-ring
transport and sheaf/internal-ring equivalence, then terminal coproducts for
constants. Searches in LeanSearch, LeanFinder, Loogle, Mathlib and both project
roots found the constituent APIs but no existing theorem with this conclusion.

No change record is needed: the only existing Lean module changed is the assigned
module, and all its public declarations and imports retain their interface.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.GeometricRingInverseImage": "907fb754f7a7e609567988100b4eef4759347585", "Sheaf.Paper.ConstantCompletionInverseImageExists": "f466df39841f8d9f78db27f62245b6a706c3cc56"}, "results": {"Sheaf.Paper.ConstantCompletionEquivalence": {"hash": "d1c42681af0d8d17deb982fbdd20171738a2637f", "status": "OK"}}, "seconds": 99, "time": "2026-10-28T00:03:54+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
