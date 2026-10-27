## What changed

Replaced the body of
`AlgebraicGeometry.Etale.etaleSingleFunctor_monoidalCompatibility` with an assembly
of the canonical single tensorator equations. The arbitrary pairing associativity
and symmetry diagrams follow by tensorator naturality and functoriality. The
arbitrary pullback pairing square follows by naturality of the specified
single/pullback comparison, the canonical tensorator pullback square, and
functoriality. Existing public signatures and attributes are preserved. The definitions
and compatibility structure, including their bodies, are relocated verbatim to a public data module,
which
the item re-exports; its original public imports remain. This separates the measured
cost of checking the structure from checking the proof.

Four new tensorator modules isolate tensorator naturality, associativity, symmetry,
and pullback. All are proof dependencies, imported privately by the item. The existing
node records these four steps and their dependencies. Two further new modules
contain the fully proved generic cochain construction and the explicit flat
tensorator factorization, extracted so each file compiles within the limit. Two further proved modules contain the abstract associativity
and pullback assembly arguments; the item applies them to the canonical squares.

## Proved and sorry left

The original hole is
`AlgebraicGeometry.Etale.etaleSingleFunctor_monoidalCompatibility`
(`lem-pur-etale-single-functor-monoidal-compatibility`). Its combination proof is
complete. This delivery is a decomposition, not an unconditional proof of that
hole: the canonical pullback calculation below remains.

The following new declarations have direct proofs, with no new holes:

- `AlgebraicGeometry.Etale.singleFunctorObjTensorIso_hom_naturality`
  (`lem-pur-etale-single-tensorator-naturality`).
- `AlgebraicGeometry.Etale.singleFunctorObjTensorIso_associativity`
  (`lem-pur-etale-single-tensorator-associativity`).
- `AlgebraicGeometry.Etale.singleFunctorObjTensorIso_symmetry`
  (`lem-pur-etale-single-tensorator-symmetry`).
- `AlgebraicGeometry.Etale.singleFunctorObjTensorIso_factorization`
  (`lem-pur-etale-single-tensorator-factorization`).
- `CategoryTheory.flatPairing_associativity_assembly`
  (`lem-pur-flat-pairing-associativity-assembly`).
- `CategoryTheory.flatPairing_pullback_assembly`
  (`lem-pur-flat-pairing-pullback-assembly`).
- `AlgebraicGeometry.Etale.exists_singleCochainMonoidal`
  (`lem-pur-etale-single-cochain-monoidal`), with the explicit constructed
  `AlgebraicGeometry.Etale.singleCochainTensorIso`.

The sole remaining `sorry` added by this packet is
`AlgebraicGeometry.Etale.singleFunctorObjTensorIso_pullback`
(`lem-pur-etale-single-tensorator-pullback`), in its own new module. There is no
`sorry` in the original item or in any definition. Thus the local count is one
original hole closed, one strictly smaller hole added, and net zero holes closed:
this is a decomposition. The explicit cochain tensorator, its naturality,
associativity, both unit equations, and its strong monoidal structure are fully
proved, and no arbitrary monoidal isomorphism is chosen.

## No longer needed

No existing module or node is withdrawn and no existing public import is removed.
The original four data declarations are publicly re-exported under their original
names from the new data module; none is pruned.
The unit route is preserved. The original definition dependencies remain needed
in the statements and in the new tensorator modules. No pruning is claimed. An unused proof import of the source monoidal-functor transport API was removed
from the new cochain construction module; that API is used only by the derived
associativity proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The original node called the
single-complex coherence verification elementary, but its Lean implementation
needs explicit cancellation of the single tensor isomorphisms and the component
formulas for the total tensor inclusions. The source library supplies those
formulas and the lax monoidal localization coherence.

The first preflight rejected the data node's `lean.statement` because it included
structure fields. The record now contains only the structure signature, ending at
`Prop`; the full fields remain in Lean and in the node's mathematical statement.
The generic assembly nodes now also record LeanSearch results, separately from
Loogle/LeanFinder and source grep, as the checker requires.

## New nodes

`lem-pur-etale-single-tensorator-naturality` records naturality of the specified
canonical flat single tensorator in its two sheaves. Its cochain calculation uses
the sole degree-zero tensor summand; localization and the natural single/quotient
comparison transport it to the derived category.

`lem-pur-etale-single-tensorator-associativity` records just the canonical
associator equation for three single objects, with the left two sheaves flat.
It has no arbitrary pairing maps or ordinary associativity hypothesis.

`lem-pur-etale-single-tensorator-symmetry` records just the canonical braiding
square. The cochain sign is one in bidegree (0,0), and the derived braiding is the
specified signed braiding descended by Qh.

`lem-pur-etale-single-tensorator-pullback` records the canonical comparison square
for two single objects, with only the left sheaf flat. This is strictly one part
of the original three-field assertion: it has no arbitrary f, g, b, c, d, no
ordinary pullback-square hypothesis, and asserts neither associativity nor
symmetry. Its docstring specifies the degree-zero comparison and counit
factorization proof. The original third field is derived from it using
naturality, rather than being restated under a different name.

`lem-pur-etale-single-cochain-monoidal` records the explicit generic cochain tensor
isomorphism and the proved existence of a monoidal structure having exactly that
tensorator. Its naturality, associativity and unit proofs are component calculations.
It adds no holes; extraction avoids repeatedly elaborating the full structure in
the derived associativity file.

`lem-pur-etale-single-tensorator-factorization` records the proved component
expansion of the prescribed flat single tensorator through the cochain tensorator,
homotopy quotient and localization. This adds no hole. It permits symmetry to use
the defining comparison without rechecking its expanded isomorphism construction.

`lem-pur-flat-pairing-associativity-assembly` proves the general diagram chase from
naturality and the canonical associator equation to arbitrary pairing associativity.
It works with any predicate on objects closed under tensor and adds no hole.

`lem-pur-flat-pairing-pullback-assembly` proves the general diagram chase from a
canonical tensorator pullback square and naturality to arbitrary compatible pairings.
It adds no hole and requires no inverse maps.

`def-pur-etale-flat-single-tensor-compatibility-data` records the existing four data
declarations extracted verbatim to a public module. Their meaning, attributes and
names are preserved, and the original item re-exports them. The change record is
`coord/changes/etale-single-tensor-compatibility-data-extraction.md`. All seven direct consumer modules were checked. The unchanged
`FiniteTwistFlatEvaluationPullback`, `FlatSinglePairingSymmetricPullback`, and
`FiniteTwistDegreeZeroEvaluationPairing` were accepted against this packet.
A profiling-only copy of `PurEtaleClosedConstantTensor` was also accepted;
its initial check exceeded the limit, while its original-item baseline passed.
No profiling options or unchanged consumer copies are delivered.

Two unchanged consumers, `FiniteTwistShiftedFactorComparisons` and
`FiniteTwistDegreeZeroEvaluationPullback`, exceed the 120-second diagnostic cap
both against this packet and against the original item in controlled baseline
compiles. These are pre-existing timeouts; their sources are not adapted here.
The shifted-pairing consumer is discussed under forced adaptations below.

## Forced adaptations

`Sheaf.AlgebraicGeometry.FiniteTwistShiftedPairingPullback` is unclaimed in the local
claim record. Its unchanged version failed against the packet with
`NOT ACCEPTED: this compile took 72 s > 60 s`; its original-item baseline passed in
55.0 s. Profiling identified 48.7 s of kernel checking in the public theorem's
concrete helper instantiation. In `module_pairing_shifts`, the private parameters
`u`, `q`, `q'`, and `hq` now use the existing `ordinaryFinitePullback` and
`ordinaryFiniteTensor` aliases used by the supplied degree-zero square. Conversion
occurs on abstract objects inside the proved helper. The public signature and
proof, all imports, and all attributes stay identical. No definition or public
statement is changed, and no importer adaptations are required. The change record
is `coord/changes/finite-twist-shifted-pairing-helper-aliases.md`.

The final `lcompile.py --all` check accepted all eleven Lean files of this packet,
including the adapted shifted-pairing consumer, with no profiling options.

The first delivery's whole-source axiom probes exceeded 60 s for the item and
shifted consumer (nonfatal notes, to be retried by the merge). A separate temporary
module importing the compiled packet ran `#print axioms` for all seven new proved
lemmas and the four data declarations. Each has only the permitted axioms
`propext`, `Classical.choice`, and `Quot.sound` (the generic associativity assembly
uses only `propext` and `Quot.sound`). The item, the canonical pullback lemma and
the shifted consumer additionally print `sorryAx`, as expected for this
one-hole decomposition. No other axioms occur. The temporary audit module was
removed and is not delivered. The adapted consumer was again accepted in this
batch. No Lean source changed after the accepted sandbox compilation.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
