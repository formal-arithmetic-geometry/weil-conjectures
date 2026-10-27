## What changed

The two remaining proofs in `Sheaf.Paper.FinitePullbackTensorComparison` are
reduced to the flat K-flat representative calculations in two new modules.
The existing public declarations, signatures, definitions, public imports,
composition proof and signed-braiding proof are preserved.

Associativity is expressed as equality of natural transformations of three
variables. Resolve each input, apply the representative equation, and cancel
the image of the product of the three resolving isomorphisms.

For the unit theorem, one representative unit isomorphism works for all flat
K-flat complexes. Tensor-comparison naturality, tensor interchange and unitor
naturality make each unit-equation path a natural transformation. Resolve the
input and cancel to extend both equations to all derived inputs. Uniqueness is
proved from the right-unit equation at the source tensor unit, by cancellation,
conjugation with the chosen unit isomorphism and left-unitor naturality.

The new proof imports are `Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives`
and `Sheaf.Paper.FinitePullbackTensorUnitRepresentatives`; neither is public.
The item node records the new proof steps and their dependencies.

Validation through `lcompile.py`: the final associativity representative module
compiled in 52.2 seconds, the unit representative module in 45.2 seconds, and
the final item module in 15.8 seconds. All are within the 60-second file limit.
No direct importer requires adaptation because no existing public signature,
public import, definition, instance or attribute was changed.

## Proved and sorry left

Two original holes closed by decomposition:

- `WeilConjectures.canonicalFinitePullbackTensor_associativity`.
- `WeilConjectures.canonicalFinitePullbackTensor_unit`.

No `sorry` remains in the item module. Two holes are added, each in a separate
public theorem with its source and full proof in words:

- `WeilConjectures.finitePullbackTensor_associativity_representatives`, node
  `lem-pur-finite-pullback-tensor-associativity-representatives`, in
  `Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives`.
- `WeilConjectures.finitePullbackTensor_unit_representatives_exists`, node
  `lem-pur-finite-pullback-tensor-unit-representatives`, in
  `Sheaf.Paper.FinitePullbackTensorUnitRepresentatives`.

This is a decomposition: two upper holes closed, two lower holes added, net
zero holes. It does not claim that the representative calculations are proved.
The new associativity theorem only covers localized flat K-flat triples; it
assumes neither arbitrary-derived associativity nor the extension argument.
The new unit theorem only asserts existence and the two representative
squares; it assumes neither arbitrary-derived unit coherence nor uniqueness.
All naturality, resolution transport and unit uniqueness in the item are
complete Lean proofs.

## No longer needed

None. All six original imports and all original proof dependencies remain
used by the retained construction, braiding, composition and resolving-flat
representative arguments. No node or module is withdrawn. The unit record
`sk-def-purity-conv` has no separate realized proof steps bypassed here.

## Where the brief, the DAG or earlier work was wrong

The old item node described associativity and unit as unfinished but did not
name separate representative calculations for them. The existing dependencies
supply the canonical maps and representative normalization but no ready-made
associativity or two-sided unit equation for this exact finite comparison.
The new nodes isolate those calculations; the resolution and cancellation
arguments have now been formalized. No existing mathematical statement,
shared definition, adopted source declaration or target was changed.

Edge cases checked in the representative statements: n=0 still uses the
positive exponent n+1; zero complexes, empty schemes and arbitrary negative
cochain degrees are retained. Associativity only reparents factors, so has no
extra Koszul sign. The coefficient unit complex is in degree zero. The same
unit isomorphism is quantified before P, and both equations use that same map.

The three search kinds were run through msearch.py and recorded in the new
nodes. Searches found native complex associators and unitors, and ordinary
module-pullback unit comparisons, but no theorem for the normalized finite
representative comparison. Blueprint search found no duplicate statement.

## New nodes

`lem-pur-finite-pullback-tensor-associativity-representatives` states the
three-complex calculation before the extension to arbitrary derived inputs.
Its plan uses flat K-flat total tensors, the ordinary pullback tensor formula,
the derived normalization square and the specified finite realization.

`lem-pur-finite-pullback-tensor-unit-representatives` states existence of one
unit isomorphism satisfying both equations on flat K-flat representatives.
Its plan localizes the rank-one ordinary coefficient pullback and checks both
scalar-action formulas. It does not assert uniqueness or the arbitrary-input
extension. No new definition or arbitrary witness chosen as definition data is
introduced. No change record is needed: existing interfaces are unchanged.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
