## What changed

Replaced the hole in `WeilConjectures.finitePullbackTensor_quotient_representatives`
by a derived diagram calculation from two strictly smaller intermediate results:
normalization of the intrinsic pullback tensor comparison at one coefficient level,
and the ordinary total-tensor quotient/pullback square. The item adds a private proof
import of `Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquare`.

The proof uses the existing quotient calculus tensor-model equations, preservation
of K-flatness, the given `he` on both inputs and their tensor total, and naturality.
It transfers K-flatness through `cc`, so no new flatness hypothesis on coefficient
quotients or quotient complexes is needed. Private proved helpers establish
quotient-counit naturality, tensor-model naturality, and the component equation
between the existing comparison family and its natural isomorphism. A proved private
categorical pasting lemma combines the equations without repeatedly rewriting
inside the concrete coefficient categories. Local reducibility settings keep the
large total-tensor and model-isomorphism implementations from unfolding during
this calculation; no shared definition is changed.

The item statement and all existing public imports and declarations are preserved.
No other existing module, definition, target, instance, attribute or public interface
is changed. New statements retain zero complexes, n=m and unbounded complexes.
The unit record has no realized statement or proof steps to bypass.

Validation: `lcompile.py --all` compiled the two new modules in import order
(10.2 s and 12.9 s). The final item source, with profiling removed, compiled
without warnings in 57.1 s. Every file is below the unchanged 60 s limit.
The original theorem signature was also compared byte-for-byte with the shared source.

## Proved and sorry left

Closed the original hole:
`WeilConjectures.finitePullbackTensor_quotient_representatives`
(node `lem-pur-finite-pullback-tensor-quotient-representatives`).
The item module contains zero remaining holes.

Added two named holes, one in each new module:

- `WeilConjectures.finitePullbackTensor_kflat_normalization`
  (`lem-pur-finite-pullback-tensor-kflat-normalization`): the representative formula
  for one pullback tensor comparison; there is no coefficient quotient square.
- `WeilConjectures.finitePullbackTensor_ordinary_quotient_square`
  (`lem-pur-finite-pullback-tensor-ordinary-quotient-square`): an equality of ordinary
  chain maps; there is no derived category, derived comparison e, or K-flat model.

This is a decomposition: one upper hole closed and two lower holes added,
not a net proof gain. Each new theorem has a source, full proof in words and DAG node.
The combination of those two statements into the original derived equality is
written in Lean in the item; no renamed copy of the original statement is assumed.

## No longer needed

The separate strong total-tensor lemma `lem-pur-kflat-total-tensor-model`
(`Sheaf.Algebra.Homology.KFlatTotalTensorModel`) is not needed by this proof.
The already proved `coefficientTotalTensor_isKFlat` from
`def-coef-ringed-tensor-hom-model` gives precisely the K-flatness used here;
flatness of every total term and a separately chosen associator are unnecessary.
Its former direct proof-dependency edge is removed.

No original Lean import is removed. The former direct edges to
`def-sp-proetale-ordinary-tensor-pullback-total` and
`def-weil-proetale-inverse-image` are represented in the smaller normalization
and ordinary-square nodes. Their modules remain transitively needed; this is
not a withdrawal or a claim that all uses of those nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The plan's sentence about cancelling model isomorphisms conceals several distinct
naturality squares. These are now proved explicitly in the item's derived argument.
The original proof-dependency list did not contain the ordinary chain compatibility
or the intrinsic representative-normalization equation as standalone declarations.
The supplied existing ordinary tensor and quotient normalizations do not themselves
state that square. The two new nodes isolate those missing steps, rather than moving
the whole derived obligation to a new name.

The current server queue row was a one-hole proof item, with no rework row or
module build-error file. No definition repair was assigned.

## New nodes

`lem-pur-finite-pullback-tensor-kflat-normalization`, in
`Sheaf.Paper.FinitePullbackTensorKFlatNormalization`, records the unit-generator
predicate and its compatible intrinsic derived tensor-model formula. Its proof
follows Stacks 07A4 and extends the flat-term formula to K-flat inputs by resolutions.

`lem-pur-finite-pullback-tensor-ordinary-quotient-square`, in
`Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquare`, records the generator
calculation before localization, using the actual iterated adjunction units.
No change record is needed: only the item, its node and new modules/nodes change.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
