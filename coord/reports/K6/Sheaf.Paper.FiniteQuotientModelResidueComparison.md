## What changed

Replaced the sole sorry in `finiteQuotient_model_residueComparison` by a composition
of isomorphisms, preserving its entire signature. The proof first identifies the
representative-based slice restriction with the exact derived restriction. It derives
composition for the actual `completedAdicDerivedChange` functors from the existing
derived coefficient adjunction and uniqueness of left adjoints. Epimorphism cancellation proves
the coefficient square from scalar compatibility and the existing limit-projection
composition, including the n = 0 case.
It then applies derived extension on the slice to the input local isomorphism and
composes the reduction, coefficient, algebraic-model, and representative comparisons.

Two independent general interfaces are stated in new modules: derived scalar extension
commutes with slice restriction, and the universe-lifted constant model commutes with
algebraic derived scalar extension and ring-equivalence transport. The former has
no constant model or algebraic residue; the latter has no completed object, local chart,
local isomorphism, adic ideal or finite-level identification. Neither restates the item.
The new slice functor is extracted from the existing universally characterized derived
scalar-extension pair on the actual slice site; no arbitrary existence witness or
unproved data is introduced.

Validation: `lcompile.py --all` compiled all three modules; the item took 30.5 seconds
and the new modules took 2.9 and 2.7 seconds. Development profiling options are removed.
The unused-variable linter is disabled only for the unchanged item signature, whose
`hφ` hypothesis the proof does not require. The delivery command repeats compilation
and runs the required preflight checks on the final files.

Only the item, its node, and the two new modules and their nodes are changed. All new
imports of the item are proof imports; its public imports remain unchanged.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.Scheme.finiteQuotient_model_residueComparison` (1 of 1).
Its composition proof, scalar-transitivity helper, finite coefficient-square cancellation,
and representative-restriction comparison are complete Lean proofs.

Added exactly two direct holes:

- `AlgebraicGeometry.Scheme.completedAdic_slice_scalarComparison`, node
  `lem-weil-pbc-completed-adic-slice-scalar-comparison`.
- `AlgebraicGeometry.Scheme.finiteModel_derivedScalarComparison`, node
  `lem-weil-pbc-finite-model-derived-scalar-comparison`.

No sorry remains in the item. This is a decomposition, not a sorry-free proof of the
mathematics: one original hole is replaced by two strictly separate general steps;
the direct-hole net change of this packet is +1. Both new holes are whole proofs of
public named theorems with source references and complete proof sketches.

## No longer needed

Removed a redundant proof import of `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`
introduced during this work: the new slice module already imports that interface publicly.
No original import was removed: the initial three public imports are used by the
unchanged statements. The item does not use
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` or import its module
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`. The binary tensor comparison
is unnecessary: the new slice scalar comparison can be established directly from
K-flat preservation and ordinary scalar/sheafification commutation on the slice.

`lem-sfb-constant-realization-derived-scalar-extension` is no longer a direct dependency
of the item, but remains needed in the new constant-model comparison; it is not
pruned from the argument. The exact ringed restriction and adic coefficient definitions
remain needed. No module is withdrawn and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The given proof dependencies supply the general ingredients but do not directly state
the concrete slice-scalar square or the comparison between the small algebraic module
universe and `finiteModelConstantComplex`. These are now explicit independent nodes,
while the original local-isomorphism argument is actually implemented.

The proof only needs the scalar-normalization part of `hcompat`, not its consecutive
compatibility part or invertibility `hφ`. Their binders remain unchanged. The finite
coefficient square is proved by cancelling the constant quotient epimorphism rather
than postulated. A first induction proof expanded the finite sheaf definitions during
kernel checking and timed out; cancellation uses the existing projection-composition
API and avoids that expansion without changing shared definitions.

The module universe-lift functor is fully faithful and exact, not an equivalence onto
all larger modules. The constant-model proof sketch therefore uses a filtered-free
resolution and explicit tensor/lift maps, rather than claiming an equivalence of
module universes. Ring-equivalence transport is an actual equivalence.

The blueprint ancestor utility returned no ancestor through the module-valued
`created.item` fields. Following the existing nodes' `blueprint.from` chain gives
`thm-weil-pbc-finite-extension`; the new nodes record that ancestor and intervening
residue-lifting nodes. No unit route or target statement is changed.

## New nodes

`lem-weil-pbc-completed-adic-slice-scalar-comparison` is the natural scalar-extension
square on an arbitrary pro-etale slice, with no adic or constant-model hypotheses.
Its proof uses flat-term K-flat resolution, preservation under ringed localization,
ordinary tensor/sheafification commutation and derived descent. The source is Stacks
06YY, 0G7E and 0D6D. It includes the universally specified actual slice functor.

`lem-weil-pbc-finite-model-derived-scalar-comparison` is the algebraic/constant
scalar-extension comparison for arbitrary B -> C and C ≃ D, with arbitrary supplied
total left derived pair. It isolates the coefficient-universe lift, canonical
representative and ring-equivalence transport from the local comparison argument.
Its source is Stacks 06YY, 0G7E, 0D6D and 093J, and it uses the already stated general
constant-realization comparison. Edge cases checked for both nodes: empty chart/site,
zero coefficient rings, identity coefficient maps, zero/unbounded complexes and n = 0
in the combining proof. No boundedness or nonemptiness assumption is added.

No change record is needed: existing public signatures, definitions, attributes and
public imports are unchanged.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
