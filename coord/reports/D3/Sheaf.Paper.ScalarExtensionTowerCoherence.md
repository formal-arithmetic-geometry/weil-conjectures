## What changed

Proved both halves of `WeilConjectures.ScalarExtensionTower.unit` from the
existing uniquely normalized scalar associator and action unitor. The proof tests
module morphisms with the actual pullback adjunction unit, cancels the inverse
scalar unitor, applies both section formulas, and lifts the resulting ordinary
natural-isomorphism equality termwise. Private proved helpers expose the pullback
adjunction extensionality, scalar unitor section and inverse-section formulas,
and pullback-section naturality. The tensor half is proved as
`WeilConjectures.scalarExtensionTensorUnit`, which only assumes a comparison's
homogeneous pure-tensor normalization at coefficient one. Its proof establishes
naturality of the sheafified tensor pairing and extensionality on homogeneous
total summands, then calculates the two unitor actions on their generators.
`unit` combines these with the existing `Comparisons.sigma_formula` and has no
remaining internal hole. No definition, existing signature, or public import changes.

On the latest resumption, `lcompile.py --all` compiled both delivered modules
against the current server snapshot without diagnostics (0.8 seconds reported for
each module). The previous uncached compile of the item took 42.8 seconds, within
the single-file limit. The import-direction check passed.
Both proved declarations still inherit `sorryAx` from the existing normalization
and model theorems used by their proofs; this delivery closes the local proof hole,
not the unfinished dependencies.

## Proved and sorry left

One original hole closed, no holes added; net hole reduction one.
The original module had eight holes.
Closed: `WeilConjectures.ScalarExtensionTower.unit`.
New and proved: `WeilConjectures.scalarExtensionTensorUnit`
(node `lem-pur-scalar-tensor-unit`). There are no holes in the new module.

The following seven original holes remain unchanged, all attached to
`lem-pur-scalar-extension-tower-coherence`:

- `WeilConjectures.ScalarExtensionTower.comparisons_existsUnique`
- `WeilConjectures.ScalarExtensionTower.square`
- `WeilConjectures.ScalarExtensionTower.composition`
- `WeilConjectures.ScalarExtensionTower.derivedSigma_existsUnique`
- `WeilConjectures.ScalarExtensionTower.realizationModels`
- `WeilConjectures.ScalarExtensionTower.scalarExtensionTowerCoherence`
- `WeilConjectures.ScalarExtensionTower.quotientModels`

## No longer needed

None. The original proof dependencies are retained for the seven unresolved
obligations. No modules or nodes are made unnecessary by this partial proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical disagreement. The whole-system scalar maps already have enough
normalization to prove their identity pullback equation directly by adjunction;
there is no need to reconstruct the geometric ringed-pullback presentation for
this part. Remote compilation intermittently returned no server response; retries
subsequently produced normal compiler diagnostics. The retained tensor proof hit its
heartbeat budget at a broad rewriting step. Replacing it with explicit congruence
on the two unitor section equations and direct use of the final unitor equation
avoids unfolding the tensor colimit choices; the revised helper compiled in 27 seconds. The smaller tensor lemma was
tested conceptually on zero complexes, empty sites, and modules concentrated in
degree zero: its generator proof and universal properties apply in each case.

## New nodes

`lem-pur-scalar-tensor-unit`, module `Sheaf.Paper.ScalarExtensionTensorUnit`,
is the tensor action-unitor step alone, for arbitrary pure-tensor-normalized sigma.
It has neither a scheme pullback nor the strict scalar square, composition laws,
quotient representative existence, or completed realization assertions. It is not
a renamed version of `unit`: the pullback half is proved in the delivered module,
and the tensor half is instantiated using the existing comparison normalization.
The new lemma is fully proved; no obligation is handed on. There are no change
records because no existing statement or definition changes.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
