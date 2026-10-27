## What changed

Restored the assigned quarantined source at its original Lean path and preserved its
public import, declaration signature, docstring and DAG attachment. Replaced its
one-line hole by an assembly proof. No target, existing definition, or other existing
Lean module is changed.

The proof obtains the actual reduction/pullback model from the already stated
`integralReductionPullbackModel`. It constructs the open realization as the inverse
of limit applied to open extension of the actual reconstruction counit, followed by
limit of the actual open reduction mate and the inverse actual reconstruction unit.
The displayed normalization follows by cancelling the two inverse pairs. Normalized
reconstruction supplies the counit isomorphism at the given Good system.

The projection/exchange equation follows from the existing private categorical
`tensor_mate_coherence` theorem, imported with `import all`, applied to the actual
adjunctions and a left-adjoint tensor square. Completed proper/open gamma is
constructed as the inverse open-adjunction transpose of the prescribed lambda
inverse. Its naturality and adjunct equation are proved directly in Lean. Three private,
fully proved categorical helpers keep these calculations independent of the large
coefficient-site definitions; the generic calculations were compiled separately.
A private projection-component lemma removes the currying identity. File-local
irreducibility attributes prevent expensive unfolding of the coefficient-site
constructions during elaboration; no shared definition or global attribute is changed.

Three separate construction steps are stated in new modules: system operations and
left-adjoint square coherence; invertibility of the two actual open maps on the
original Good domain; and completed ringed models with ordinary open comparisons.
Each retains its actual map normalizations. The new modules import only the
lowest existing data module needed by their statement signatures. None asserts AmbientModels,
a full realization package, or the original existential statement under a different name.

Validation: all three new statement modules compiled through `lcompile.py --all`.
The final item compiled against them through `lcompile.py`, with exit code 0,
no warnings, and a reported 10.9 s compile time. The independent categorical
helper scratch module also compiled. The item signature is byte-identical to the
current source, and the new module and node names were checked for collisions.

## Proved and sorry left

The original hole in
`WeilConjectures.IntegralSystemRealization.integralCanonicalAmbientModels`
(lem-sf-integral-canonical-ambient-models) is discharged by a complete assembly proof.
This is a decomposition, not a complete mathematical proof: one upper hole is closed
and three strictly smaller holes are added. There are zero textual holes in the item.

The three added holes, each the entire proof of a public named theorem, are:

- `WeilConjectures.IntegralSystemRealization.integralCanonicalSystemCoherence`
  (lem-sf-integral-canonical-system-coherence).
- `WeilConjectures.IntegralSystemRealization.integralOpenReductionNormalizedLimit`
  (lem-sf-integral-open-reduction-normalized-limit).
- `WeilConjectures.IntegralSystemRealization.integralRingedModelExistence`
  (lem-sf-integral-ringed-model-existence).

The existing hole in `integralReductionPullbackModel` is used without being changed
or restated. No hole is placed in a definition. All selected data is used locally
inside the theorem's existential proof, not to define an arbitrary public object.

## No longer needed

The item's direct proof imports of `Sheaf.Paper.SemilinearDerivedSections` and
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting` are removed. They remain needed
for the separate system-construction argument, and are not claimed as pruned from
the library. `Sheaf.Paper.RingedExchangeTensorCoherence` stays as an `import all`
proof import to use its already proved generic tensor-mate calculation.

No module or mathematical node is withdrawn. The original system-construction
proof dependencies move to lem-sf-integral-canonical-system-coherence; reconstruction
and tensor mate coherence remain in the item's proof dependency list. The unit route
is unchanged. There is no net module pruning claim.

## Where the brief, the DAG or earlier work was wrong

The module was quarantined when the session started. Its rework row named the
archive, and the archive supplied the preserved source; absence from lean was not
interpreted as withdrawal. The live dependency sources were restored during this
session. No quarantine archive is edited or listed for deletion.

The original single proof step describes multiple construction tasks. Its cited
abstract calculus theorems do not themselves provide the instantiated operations,
normalized whole-system compositor tensor square, and completed ringed models in
one Lean declaration. The existing reduction/pullback-model theorem does provide
that sub-obligation and is reused. The existing integralOpenMateNormalization has
finite-field/invertible-characteristic and constructible-input restrictions; it
cannot be applied verbatim to this item's arbitrary schemes and Good systems.
The new open lemma retains both original Good hypotheses and only supplies the two
map-invertibility facts; the actual realization and normalization are proved here.

The new statements were checked on empty and identity opens, zero objects, equal
quotient indices, arbitrary scheme characteristic, and both normalized input/output
conditions. They impose no nonempty condition, add no target hypotheses, and do not
use conservativity to detect equality of arbitrary derived morphisms. The ringed
gamma construction is an actual adjunction transpose, not an arbitrary endomorphism.

## New nodes

`lem-sf-integral-canonical-system-coherence`, in
`Sheaf.SixFunctors.IntegralCanonicalSystemCoherence`, isolates ordinary/derived system
operations, their section-normalized compositors and intrinsic proper/open transport,
and the left-adjoint tensor square. It asserts neither reconstruction nor ringed
completion models. Its square is used by the existing generic tensor-mate theorem.

`lem-sf-integral-open-reduction-normalized-limit`, in
`Sheaf.SixFunctors.IntegralOpenReductionNormalizedLimit`, isolates invertibility of
the actual open reduction mate at the total limit and the output reconstruction
unit. It asserts no comparison isomorphism or normalization equation. Both are
constructed and checked in the item.

`lem-sf-integral-ringed-model-existence`, in
`Sheaf.SixFunctors.IntegralRingedModelExistence`, supplies only the normalized tensor
and pullback models and ordinary open comparisons. It omits proper/open gamma and
its adjunct, which the item constructs directly.

All nodes inherit the original chapter and unit and record the source, complete
proof in words, Mathlib searches and exact Lean signatures. No change record is
needed: no existing interface or definition is changed, and no consumer adaptation
is required.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
