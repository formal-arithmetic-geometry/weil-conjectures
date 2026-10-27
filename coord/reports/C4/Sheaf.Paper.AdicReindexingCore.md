## What changed

`Sheaf.Paper.AdicCoefficientRingReindexing` now proves the function-normalized
coefficient isomorphism theorem. `Sheaf.Paper.AdicReindexingCore` uses it, proves the inverse function formula, and constructs the ordinary module
identity and compositor with their actual section formulas. The ring comparison uses
the proved section-ring multiplication helper from `NativeScalarForgetting`. The module
coherences use Mathlib's sheaf-module pushforward comparisons. Generic proved private
helpers keep those constructions and their section equations abstract over the ring
sheaf; this avoids expensive unfolding of the native coefficient ring.

The unchanged statement `exists_normalized_reindexing_core` assembles these maps with
three strictly smaller obligations: integral comparison and common-stage descent for
one isomorphism, tensor reindexing on the supplied ambient K-flat models, and the source
identity unit for the specified common-stage compositor. The assembly keeps `C.data = d`
by reflexivity. Each new obligation is in its own module and has its own node, source
and proof in words. In particular, none asks for a FamilyCore or repeats the whole
existence theorem under another name.

The delivery also proposed an elaboration repair of the unclaimed module
`AdicRealizationFamilyData` (local transparency settings and irreducibility hints around
`integralRealizationAgreement`, file-level `Elab.async false`). The independent review
withdrew it as not forced: the published source compiles in 48 s under load, and every
module of this delivery compiles against the published, unchanged file. That module is
restored to its published bytes; the change record
`coord/changes/C4-adic-reindexing-family-elaboration.md` now records the withdrawal.

## Forced adaptations

None. No module outside the item and its new modules is changed.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.AdicQbarRealization.exists_normalized_reindexing_core` by a complete
Lean assembly from the three new statements. This is a decomposition, not a net
reduction in holes: one original hole closed, three holes added. The item itself has
zero holes. The new theorem
`WeilConjectures.AdicQbarRealization.exists_function_normalized_ring_reindex` is fully
proved, with no new hole (its `#print axioms` shows `sorryAx` only through the
upstream `LocallyFiniteAdicRealization.Realization`/`ring`, not through this delivery). The coefficient-ring construction, inverse function equation, ordinary
identity/composition isomorphisms and both section normalizations have complete proofs.
The canonical common-stage pullback unit assertion is extracted from the existing
`derivedPullbackTensorIso` theorem.

The complete list of remaining delivery holes is:

- `WeilConjectures.AdicQbarRealization.exists_integral_realization_reindexing`, in
  `Sheaf.Paper.AdicIntegralReindexingDescent`, node
  `lem-sf-adic-integral-reindexing-descent`.
- `WeilConjectures.AdicQbarRealization.exists_tensor_reindexing_models`, in
  `Sheaf.Paper.AdicTensorReindexingModels`, node
  `lem-sf-adic-tensor-reindexing-models`.
- `WeilConjectures.AdicQbarRealization.exists_common_pullback_identity_unit`, in
  `Sheaf.Paper.AdicCommonPullbackIdentityUnit`, node
  `lem-sf-adic-common-pullback-identity-unit`.

No definition contains a hole. The new existential data are normalized on sections,
K-flat/derived representatives or the specified compositor; the proof introduces no
public definition selecting an arbitrary witness.

## No longer needed

No original public import is removed and no module is withdrawn. The original planned
proof dependency `lem-fix-constructible-tensor-completion`
(`Sheaf.SixFunctors.ConstructibleTensorCompletion`) is not used by this reduction:
`SpaceData.tensor` already supplies the ambient tensor models needed by the tensor
reindexing argument. This does not withdraw that theorem or its module from other
routes.

The other original proof dependencies remain in the three subarguments where needed.
The integral descent node retains coefficient cartesianness, completed coefficients,
normalized/natural isomorphism comparison, finite-free completion, scalar extension,
rationalization and common-stage coefficients. The tensor node retains inverse-image
tensor compatibility, the exact monoidal total K-flat theorem and cochain coherence.
The source-unit node retains integral comparison composition and the specified
pullback compositor. They are not claimed as globally pruned merely because the
core's new proof invokes their smaller consumer nodes.

## Where the brief, the DAG or earlier work was wrong

The old build-error record names a bad import of `AdicRealizationFamilyData`. Both the
item source and that dependency are present in the current shared source; the item's
statement and its parent dependencies were retained. Compiling the current dependency
source exposed the 75--80 second elaboration problem. Profiling located about 40 seconds
in `integralRealizationAgreement`; with local elaboration hints the dependency compiled
in 31 seconds during debugging. (Review note: with lcompile the published source takes
52 s CPU / 48-54 s wall at load ~90, under the limit and already compiled in the
published build, so the repair was withdrawn as unforced.) No statement was weakened and no normalized map was
replaced. The current queue lists the item as a one-hole proof item.

Mathlib searches found generic site/module coherence operations, which the ordinary
part uses, but no native integral/common-stage realization normalization or ambient
ReindexTensor theorem. The searches and their actual results are recorded in the new
nodes and the sandbox search log. Blueprint searches for reindexing, pullback identity
and K-flatness found no exact native normalization duplicate. The item's ancestor
query returns no imported blueprint ancestor; the new nodes preserve its existing
native provenance and its unit.

The new statements were checked on the identity isomorphism, inverse reindexing,
empty geometric spaces and zero complexes. Their maps are fixed by the existing
normalizations. No nonemptiness, base-field linearity, or extra geometric hypothesis
is introduced. The tensor statement concerns ambient module models alone; the
integral statement asserts no tensor/coherence laws; the source-unit statement uses
the specified compositor rather than choosing a replacement. The unit record is
unchanged.

Validation (worker, before the review withdrew the family-data repair): the family-data source and all seven direct importers compile.
The six unchanged importer copies were removed after checking them. Their compilation
times were 8--33 seconds; family data took 39.5 seconds without profiler options. The
core compiled with zero holes in 54.4 seconds before extracting the fully proved ring
construction to its own module for additional timing margin. After extraction, the ring module compiled in 14.7 seconds and the core in 49.1
seconds. The final coefficient module, using default transparency settings, compiled
in 13.7 seconds. The three remaining statement modules also compile individually. Delivery
checks validate the final packet.

## New nodes

`lem-sf-adic-coefficient-ring-reindexing` is fully proved. It constructs just the
coefficient-ring sheaf isomorphism fixed on functions, without integral, tensor or
ordinary module data. Its source module separates the proved coefficient computation
from the rest of the core after generic coherence helpers had already removed the
expensive native unfolding.


`lem-sf-adic-integral-reindexing-descent` supplies only the balanced integral maps and
realization comparison for one scheme isomorphism, including their integral
representative agreement. It supplies neither the coefficient isomorphism nor module,
tensor or source-unit coherence.

`lem-sf-adic-tensor-reindexing-models` transports the already supplied ambient K-flat
models through the exact ringed-site equivalence, with homogeneous generator and unit
normalizations. It asserts no common-stage realization comparison.

`lem-sf-adic-common-pullback-identity-unit` supplies only the identity pullback unit
with its equation against the specified twice-identity compositor. It does not mention
realization data or an ordinary coefficient-ring presentation.

## Related modules compiled before delivery

6 related module(s) compiled against this delivery by deliver3.py: 6 OK.

```json
{"capped": false, "direct": 6, "left_out": 0, "own": {"Sheaf.Paper.AdicCoefficientRingReindexing": "a7ea36e4c7e2721ef700edef76c88a972fe8231f", "Sheaf.Paper.AdicCommonPullbackIdentityUnit": "47ab3aab223899a45be02f3b599a7a2e47bedff9", "Sheaf.Paper.AdicIntegralReindexingDescent": "b24a079f731179062be34087b84677a220957f60", "Sheaf.Paper.AdicRealizationFamilyData": "faf5d2ea5ec4fe88fd86ca9aee1425fa7ef0d535", "Sheaf.Paper.AdicReindexingCore": "1fbdf722b89e076b82fcc0dc369f866bd650b009", "Sheaf.Paper.AdicTensorReindexingModels": "c9d7f2ecb90709bbbfbccf5d9fe434e27eaf49e9"}, "results": {"Sheaf.Paper.AdicNormalizedPullbackRealization": {"hash": "108af08a4d8ad80518f1d0b3e8b84e366cbc8932", "status": "OK"}, "Sheaf.Paper.AdicQbarConstructibleRealization": {"hash": "7e2ce2076ec6ff2ae7f31dd670b20fca6d09af3f", "status": "OK"}, "Sheaf.Paper.AdicRealizationIsomorphismNormalization": {"hash": "f4c58479f8dbbb591db42a04868e8a7c91b7ceac", "status": "OK"}, "Sheaf.Paper.AdicReindexingFunctoriality": {"hash": "eda0c215c3c627353facc43b117e9b20b5bc14c2", "status": "OK"}, "Sheaf.Paper.AdicReindexingHom": {"hash": "53fef4c78e67428be212e86e68cce260d999f320", "status": "OK"}, "Sheaf.Paper.AdicReindexingTensor": {"hash": "6983f14d94803f4d874c8452687f5cff837070f1", "status": "OK"}}, "seconds": 67, "time": "2026-10-28T02:43:13+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
