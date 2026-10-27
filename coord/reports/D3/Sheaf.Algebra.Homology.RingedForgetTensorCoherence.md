## What changed

Replaced the body of `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_coherence`
with an explicit construction and transport argument. The unit is the composite of the
five isomorphisms specified in the original statement. Its normalization follows by
cancelling the inverse target unit-model isomorphism.

The four structural equations are transported from flat-term K-flat representatives
to arbitrary derived objects, using the existing independent-coefficient resolution
theorem. Associativity is transported as equality of two natural transformations;
the unit and symmetry equations use explicit naturality and cancellation. Every
private helper is proved. Existing statements and public imports are unchanged. The proof imports
`TensorColimitsIndependentCoefficients` for its site-flatness comparison API.

Three representative modules isolate the representative calculations: associativity, both unit
squares, and symmetry. These statements assert individual equations at localized
flat-term K-flat complexes. None asserts existence of a coherent comparison or the
original conclusion on arbitrary derived objects. The unit module also defines the
actual composite unit isomorphism; no data are chosen from an existence theorem.

The symmetry module checks the chain square using the coproduct summand law. Its
proof tests target summands after the inverse chain comparison, so it does not add a
coproduct-preservation hypothesis on U. Sheafification and local pure tensors identify
the signed swap as a sheaf morphism; additivity preserves the integer Koszul scalar.
The representative comparison squares then transfer the result through localization.

## Proved and sorry left

The original hole is replaced by the completed construction, normalization, and
transport proof of `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_coherence`.
This is a decomposition, not a claim that the original mathematical obligation is
fully discharged independently of all new lemmas. The packet closes one existing
hole and adds two strictly smaller holes (net -1); it is counted as a decomposition,
not as one completed proof of the original obligation.

The remaining named holes are:

- `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_associator_representatives`
  (`lem-sf-ringed-forget-tensor-associator-representatives`).
- `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_unit_representatives`
  (`lem-sf-ringed-forget-tensor-unit-representatives`).

The symmetry representative theorem is proved. No hole occurs in a definition,
private helper, or the original module. The associator, unit, signed-chain and
representative-symmetry modules pass remote compilation. The separate transport
check, including flat-representative existence, also passes and is excluded from
the delivery. The combined main module passes remote compilation in 14.1 seconds
without warnings; all delivered files satisfy the 60-second per-file limit.
The delivery tool performs the final independent mechanical checks.

## No longer needed

No existing module, declaration, or public import is removed or withdrawn. The
original total-tensor K-flat closure dependency is still needed by the new
associativity calculation; the K-flat resolution dependency is used directly by the
transport proof. The tensor structural model and exact-functor factorization
dependencies remain in use. There is no pruning claim.

## Where the brief, the DAG or earlier work was wrong

The original DAG grouped the representative calculations and their extension to all
derived objects into one hole. The delivery separates these genuinely different
steps, retaining the source's argument and the unit route. In particular, the unit
is constructed before its unit equations are asserted; its normalization is proved
without assuming any structural constraint.

The rework table lists an old quarantined version importing the withdrawn false-tail
module. The current item source is already restored with its original statement and
one `sorry`, and has no such import. This delivery starts from that current source,
preserves its Lean attachment and dependencies, and introduces no false-tail import.
No quarantine file is deleted or replaced.

## New nodes

`lem-sf-ringed-forget-tensor-chain-symmetry` records the proved compatibility of
signed chain swaps with a summand-normalized total-tensor comparison. This is
separate from localization and requires neither flatness nor coproduct preservation.
The symmetry file exceeded 60 seconds by one second after its proof was completed;
keeping totalization data behind its API and moving this independent calculation
into its own module avoids combining both expensive checks in one file. No hole
is introduced by this split.

`lem-sf-ringed-forget-tensor-associator-representatives` isolates step 2 of the original
proof: the associator equation on three specified flat-term K-flat representatives.
It uses the inner and outer model squares and total-tensor closure, and does not
assert unit, symmetry, or extension to arbitrary objects.

`lem-sf-ringed-forget-tensor-unit-representatives` isolates the two degree-zero unit
calculations from step 3. It records the explicitly constructed unit isomorphism and
its left and right equations on one flat-term K-flat representative.

`lem-sf-ringed-forget-tensor-symmetry-representatives` isolates the signed swap
calculation from step 3. The proof compares actual sheaf morphisms on summands and
then uses the two representative squares and the localization factor's naturality.

All four nodes inherit the item's chapter and unit. Their sources, complete proofs
in words, searches, and verbatim Lean statements are recorded. The item's proof and
proof dependencies now follow the construction and transport code. There are no
shared-interface changes, forced adaptations, or change records.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
