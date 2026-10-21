## What changed

Proved both declarations in `Sheaf.AlgebraicGeometry.ConstantFieldTorBounds` with unchanged
statements. The forward implication computes the total tensor with a degree-zero module
as termwise tensor, then uses exactness of tensor over a constant field to commute with
cohomology. It applies directly to every representative quantified over by the Tor predicate.
The converse chooses a K-flat resolution of a representative and tests with the coefficient
module, using the canonical total-tensor right unit isomorphism. The finite variant takes
existence of the same ordered endpoints.

Updated the existing node's proof, proof dependencies, proof origin and obsolete tool-use list
to describe this route. The unit `sk-lem-integral-models` and both theorem signatures remain
unchanged. No definitions, public declarations, or other modules are changed.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Scheme.constant_field_tor_bounds`
- `AlgebraicGeometry.Scheme.constant_field_finite_tor_amplitude_iff`

Added zero holes; split off zero statements. No `sorry` remains in the delivered Lean module.
Both declarations realize `lem-sfb-constant-field-tor-bounds`. Remote single-file
compilation passed after pruning the proof imports (9.2 seconds). `#print axioms` for each
declaration reports exactly `propext`, `Classical.choice`, and `Quot.sound`; neither depends
on `sorryAx`.

## No longer needed

The following original proof dependencies are unnecessary on this route:

- `lem-sfb-bounded-representative`: cohomology of any representative suffices, since tensor
  with every module is exact.
- `lem-weil-pbc-independent-bounded-flat-kflat`: the forward argument works for all complexes;
  it does not need to prove a degree-zero test complex K-flat.
- `lem-pur-kflat-tensor-quasiiso-independent`: no tensor localization or representative
  transport is required in the forward implication.
- `def-weil-derived-tensor`: the actual Tor predicate already specifies the total-tensor
  tests; the proof uses those tests directly. Its statement dependency is retained.

These are local dependency removals, not module withdrawals. Other consumers may still
need them. The coefficient-unit argument retains `lem-pc-kflat-resolution`.

Removed proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients`
- `Mathlib.Algebra.Homology.BifunctorShift`

Added private proof imports for the single-complex tensor comparison, exact-functor
cohomology comparison, and site/monoidal tensor comparison. Existing public imports
are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed repair. The DAG's longer forward route through bounded
representatives and a descended tensor functor is unnecessary: flatness of every test module
makes tensor exact on arbitrary complexes. This also directly handles the universal
quantification over K-flat representatives in `HasCoefficientModelTorAmplitude`.

Edge cases use the same proof: the zero complex, the empty scheme, singleton ordered
intervals, arbitrary fields, independent coefficient universes, and an unbounded object in
the converse. No finiteness, constructibility, or enough-points hypothesis is introduced.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
