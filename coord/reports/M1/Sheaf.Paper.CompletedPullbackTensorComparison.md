## What changed

Reduced `WeilConjectures.pullbackTensorSystemComparison_associativity` to the
calculation on localized K-flat triples in the new module
`Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives`.
The proof forms the two natural associativity paths, uses the existing K-flat
resolution theorem for each input, and applies the already proved generic
triple natural-transformation extensionality helper from
`FinitePullbackTensorUnitRepresentatives`. Naturality along the product of
three representative isomorphisms and cancellation extends the representative
calculation to arbitrary derived inputs. The original theorem statement and
all public definitions are unchanged. The new import is proof-only.

The unchanged baseline exceeded the 60-second file limit (61.9 s). Profiling
identified repeated elaboration and kernel checking of the large operation
constructions. Scoped local irreducibility attributes seal the recorded
calculus within coherent associativity and seal the reference comparison in
later proofs. They leave exported transparency unchanged. Broader sealing was
tested and reverted because the finite evaluation and ordinary unit
constructions need the original definitional equalities. The scoped version
still took 62.4 s, so the already-proved coherent unit construction and its
application of `unit_from_tensor` were extracted to
`Sheaf.Paper.CompletedPullbackTensorUnitFromAssociativity`. The item applies
this proved helper to its associativity theorem. The helper adds no hole, no
shared definition changes, and no assumptions to the original public theorem.
The newer explicit instruction in the worker brief permits this split after
improving definitions and profiling, superseding the older blanket prohibition
in the standing stage document. Profiling options were removed.

Moved the existing private `coherentTensor_representatives` helper before its
new use; its statement and proof are unchanged. Updated the item's DAG proof
and dependencies to match this reduction. The item was initially absent from
`lean/` and was read from its `coord/rework.tsv` quarantine archive; that source
and all its declarations were preserved.

Validation: `lcompile.py --all` compiled all three delivery modules successfully
(exit code 0). All 32 original public declaration signatures match the archived
source exactly. The new files have no lines over 100 characters; all node
references exist and each proof-dependency list equals its proof-step union.

## Proved and sorry left

This is a decomposition, not a net proof gain: one original hole is reduced
and one strictly smaller representative obligation is added. The total number
of holes in this delivery remains five (four in the item, one in the new module).

Closed the body of `WeilConjectures.pullbackTensorSystemComparison_associativity`
by a complete proof from the new representative theorem. No new hole is hidden
inside this proof, a definition, or a private declaration.

Original holes left, all attached to
`def-pur-completed-pullback-tensor-comparison`:

- `WeilConjectures.pullbackTensorSystemComparison_evaluation`.
- `WeilConjectures.canonicalFinitePullbackTensor_quotient`.
- `WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique`.
- `WeilConjectures.canonicalIntegralPullbackTensor_scalar`.

New hole:

- `WeilConjectures.completedPullbackTensor_associativity_representatives`, node
  `lem-pur-completed-pullback-tensor-associativity-representatives`.

The new obligation only treats three localized K-flat cochain complexes.
Its source and complete generator/reassociation argument are in its docstring
and node. The extension from these representatives to all derived objects is
proved in the item. There are no additional hypotheses on the original theorem.

## No longer needed

No mathematical dependency, module, or unit step is pruned. The proof-only
imports `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree` and
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal` moved from the item
to the extracted unit helper, where their declarations are actually used.
They remain transitive dependencies. The associativity proof reuses the
existing generic helpers through the already present
`import all Sheaf.Paper.FinitePullbackTensorUnitRepresentatives`.

## Where the brief, the DAG or earlier work was wrong

The assigned source was quarantined rather than present at its normal path;
the current rework row supplied the archive. It has five existing holes.
The former proof plan described the reassociation calculation but did not
separate it from extension along K-flat resolutions. This delivery makes that
separation explicit without changing the unit route or any target statement.

## New nodes

`lem-pur-completed-pullback-tensor-associativity-representatives` states the
coherent associativity equation only on localized K-flat triples. It uses the
existing coherent comparison and tensor models; it does not import the item,
so the reduction is acyclic. The Stacks 07A4 total-tensor argument computes the
same triple pure generator along both paths, with no permutation or extra sign.
The new module has one public theorem and exactly one `:= by sorry` proof.
Mathlib searches (LeanSearch, LeanFinder, Loogle, and grep) and the whole-blueprint
search found no matching coherent normalization theorem. Empty schemes and zero
complexes cause no exceptions; no boundedness, termwise flatness, or coefficient
invertibility condition was added.

`lem-pur-completed-pullback-tensor-unit-from-associativity` records the proved
unit step extracted for compile performance. It assumes the associativity
equation, constructs an object isomorphism between the pulled-back ring unit
and the target ring unit using the single-functor model, and applies the
already-proved generic unit extraction theorem. Its public theorem has no
`sorry`; the item discharges its hypothesis with coherent associativity.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
