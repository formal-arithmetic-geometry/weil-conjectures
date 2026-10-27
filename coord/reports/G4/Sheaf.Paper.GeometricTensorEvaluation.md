## What changed

Prove `WeilConjectures.SemilinearSections.geometricTensorEvaluation` without changing
its signature or its public imports. The proved helper module
`Sheaf.Paper.TensorComparisonCochainSquare` establishes
the cochain square; private helpers in the item establish the four-model
square for arbitrary exact additive module functors and specialize it to geometric
pullback and evaluation. The calculation uses the existing proved summand-map and
tensor-model naturality helpers through proof-only imports. The item node records
the implemented proof dependencies. All existing public imports and declaration signatures
remain unchanged; instance suppression and irreducibility are confined to the
proofs and their private helpers.

A useful preparatory argument derives preservation of flat modules directly from
`TensorComparisonModel.kflat`: place a flat module in degree zero, apply the
bounded-above flat criterion, and use the converse K-flat single-complex criterion
after applying the functor. This supplies the flat-term hypotheses needed when
composing two model equations, without any new geometric preservation lemma.

Validation: `lcompile.py --all` compiled all three modules (2.9 s, 8.2 s,
and 58.3 s). The single reported long-line warning has been corrected. There
are no profiler options or diagnostic commands in the delivered files.

## Proved and sorry left

Closed: `WeilConjectures.SemilinearSections.geometricTensorEvaluation`
(`lem-coef-semilinear-geometric-tensor-evaluation`), the item's one original hole.
Added holes: none. Split-off obligations: none. Sorries left in the item: none.
Every private helper and both new public helpers have complete proofs:
`WeilConjectures.SemilinearSections.tensorComparisonCochainSquare`
(`lem-coef-semilinear-tensor-comparison-cochain-square`) and
`WeilConjectures.SemilinearSections.tensorComparisonModel_preserves_flat`
(`lem-coef-semilinear-tensor-model-preserves-flat`). Both are extracted for
compilation time and add zero holes.

## No longer needed

The item originally had only its statement import, which is retained. The temporary
proof import `SystemCochainTensorReduction` moved to the new proved helper module,
where its summand-map lemma is used.
The planned direct proof dependency
`lem-weil-pbc-ringed-topos-kflat-pullback`
(`Sheaf.Paper.KFlatRingedToposPullback`) is unnecessary: the supplied
model already records K-flat preservation, and its flat-module consequence is
proved using single complexes. The existence theorem
`lem-coef-semilinear-tensor-evaluation`
(`Sheaf.Paper.SemilinearTensorEvaluation`) is also unnecessary as a direct proof
dependency: the evaluation comparison models and their ordinary parts are fields
of the given `Data` structures. This delivery does not withdraw either module;
other consumers may still need them. No library module is pruned.

## Where the brief, the DAG or earlier work was wrong

The plan needs flat-term preservation as well as K-flat preservation to apply the
second model in a composite. Both are available from the supplied models: the
latter is a field, and the former follows by testing on single complexes. The
proof does not assume derived evaluation is faithful. No statement correction or
shared-interface change is required.

## New nodes

`lem-coef-semilinear-tensor-comparison-cochain-square`, in
`lean/Sheaf/Paper/TensorComparisonCochainSquare.lean`, proves the cochain comparison
step outright, with no `sorry`. The complete single-file proof took 64.4 seconds
after replacing broad summand rewrites with explicit maps and making the private
`twoFactors` definition irreducible. Extracting this self-contained proved step
keeps the delivered files below the 60-second limit. This is a code split, not a
split-off obligation. No change record is needed: no other existing module or
interface is changed.

`lem-coef-semilinear-tensor-model-preserves-flat`, in
`lean/Sheaf/Paper/TensorComparisonModelPreservesFlat.lean`, proves flat-module
preservation from the model's K-flat preservation by the single-complex argument
described above. It is fully proved, with zero holes. After extracting just the
cochain step the main file compiled in 59.0 seconds; this second extraction gives
the main file more margin under the unchanged 60-second limit.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
