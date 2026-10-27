## What changed

Restore the quarantined `Sheaf.Paper.FiniteCoefficientReductionFlatModel` module with all
public declarations, definitions, signatures, imports and docstrings preserved. Repair the
pro-etale Tor-amplitude comparison to use `KFlatFixedTensor.ordinaryTensor` for both the
termwise tensor and `mapBifunctorSingle₂Iso`. Prove an explicit equality using
`ordinaryTensor_eq_published` to connect the API total tensor to the native tensor tested
by `HasProEtaleTorAmplitude`, and transport the vanishing statement along that equality.
Register the existing tensor API's additive and totalization facts as local instances
inside the private-helper section. Move the existing irreducibility attributes for
`flatModelReductionData` and `flatModelReductionDerivedData` immediately after their
definitions so later selections do not unfold their universal construction. Supply
`GrothendieckTopology.W.monoidal` explicitly in the etale proof, avoiding the instance
search that exhausted its default budget. The private counit comparison now supplies the universal data's additive witness
explicitly for its selected ordinary functor. This avoids searching for additivity
through the finite-stage wrapper. The DAG records the explicit normalization
and its existing tensor API node as a direct dependency; the attachment stays.

Validation: an intermediate complete module compiled cleanly with `lcompile.py` in
35.3 seconds, but its delivery compile timed out. Continued diagnosis exposed an
additive-instance search for the raw selected functor; the final repair supplies
that existing witness explicitly and specializes the private helper to the exact
universal-counit property. The specialized version compiled in 59.5 seconds; the final
`let` binding shares the proof witness and removes the inlining warning. Final validation
is recorded below.

Final validation: `lcompile.py` compiled the complete module without warnings in
53.7 seconds.

## Proved and sorry left

This is a zero-hole rework repair, not a new proof count. The archive has zero `sorry`s;
the restored module has zero `sorry`s. Closed 0 holes; added 0 holes; split off 0 statements.
Both `AlgebraicGeometry.Scheme.finiteCoefficient_reduction_flatModel` and
`AlgebraicGeometry.Etale.finiteCoefficient_etale_reduction_flatModel` retain complete proofs
and their original statements (node `lem-sf-reduction-flat-model`).

## No longer needed

None. No import, node, module, public declaration or unit step is withdrawn. In particular,
the quarantine archive and the node's Lean attachment and dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The assigned file was absent because it was quarantined after the cluster-restore global
build, as recorded in `coord/rework.tsv`. It was not unused mathematics and is restored.
The archived proof implicitly converted the named ordinary-tensor API to `curriedTensor`
inside the total-complex comparison. This times out in the current compile environment.
Keeping the API tensor consistent and giving the native-to-API equality explicitly repairs
that conversion. The next full compile reached the etale proof in 54.3 seconds but
exhausted the default instance-search budget on `T.smallEtaleTopology.W.IsMonoidal`.
The proof now supplies Mathlib's named monoidality instance directly. No mathematical
statement, coefficient construction, or unit route changes.

Change record: `coord/changes/J1-finite-coefficient-reduction-tensor-rework.md`.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
