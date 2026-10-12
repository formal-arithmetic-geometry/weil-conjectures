## What changed

`Sheaf.RingTheory.GRingPairsBackward` now proves the backward criterion by checking flatness
and the fibres of each composite R → completion(R_p), then applying
`RingHom.isRegular_of_comp_algebraMap_localization`. The case q not contained in p is
proved directly: an element in q outside p maps to a unit and to zero in the fibre.
Geometric regularity of this zero ring is proved for every required field extension.
The contained-prime case uses the new, fully proved quotient formal-fibre algebra isomorphism.
Existing signatures and public imports are unchanged. Both modules compile cleanly, and
`#print axioms` for each public theorem reports exactly `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`.

## Proved and sorry left

Closed: `isGRing_pairsOfPrimes_backward`
(node `lem-weil-pbc-g-ring-check-pairs-of-primes-backward`). No sorry remains in the item.
Also proved: `nonempty_formalFibre_quotient_algEquiv`
(node `lem-weil-pbc-formal-fibre-quotient-iso`), in
`Sheaf.RingTheory.FormalFibreQuotientIso`. It combines Mathlib's surjectivity on stalks,
localization kernel formula, tensor quotient equivalence and tensor cancellation with
`AdicCompletion.exists_local_completion_quotient`. Both private helpers are fully proved.
No sorry remains in either delivered module; no holes were added. Net: one hole closed.
No data definition was added. All existing dependencies used in these proofs are already
proved in the library or Mathlib.

## No longer needed

Removed proof imports:
- `Sheaf.RingTheory.AdicCompletionNoetherian`
- `Sheaf.RingTheory.FibreRingNoetherian`
- `Sheaf.RingTheory.LocalCompletionQuotient`
- `Sheaf.RingTheory.LocalizationRegular`
- `Sheaf.RingTheory.RegularComposition`

The backward proof does not need `lem-weil-pbc-adic-completion-noetherian`,
`lem-weil-pbc-fibre-ring-noetherian`, `lem-weil-pbc-localization-regular`, or
`lem-weil-pbc-regular-composition`. Noetherianity of the contained fibres is already
part of geometric regularity in the hypothesis; the other fibres are zero. The completion
quotient lemma remains used in the proof of the new isomorphism node, so its removal from
the main module is not a claim that it is globally obsolete. Tensor cancellation and
localization of quotients likewise remain in the new node's proof. The unit's realized
statement and steps are unchanged. These are local pruning claims, not claims that no
other target import reaches the removed modules.

## Where the brief, the DAG or earlier work was wrong

The backward node had empty proof dependencies despite its module importing six proof
modules and its split report describing a seven-step argument. Its proof and dependencies
now record the actual reduction. No statement error was found. The full Stacks source is
not installed in this clone; the proof of Tag 07PN was read at
https://stacks.math.columbia.edu/tag/07PN, whose displayed equality is exactly the new
isomorphism statement. The new proof combines the existing completion-quotient declaration with localization,
kernel identification and tensor cancellation.

## New nodes

`lem-weil-pbc-formal-fibre-quotient-iso` states the residue-field algebra isomorphism of
Stacks 07PN, with localization-of-quotient, completion-of-quotient and tensor-cancellation
steps, all implemented in Lean. Its module is `Sheaf.RingTheory.FormalFibreQuotientIso`. Edge cases checked:
q = p gives the closed fibre; q = 0 in a domain removes the quotient operation; the zero
base ring has no prime pair. None requires an extra hypothesis. Its statement quantifies
over the same universe and prime instances as the existing criterion. No change record
is required: no existing statement, definition or public interface changed.

## Second reading by G1

1. Compared both delivered modules against the repository versions. Existing theorem signatures and public imports are unchanged; the added module is a new node as declared in the report.
2. Compiled both modules with `lcompile.py --all`; compilation succeeds with no warnings or `sorry`. The proofs use no forbidden declarations, and their axioms are limited to the permitted foundational axioms (apart from any upstream open statements, none used here).
3. Checked the added quotient-fibre statement against the Stacks 07PN argument and its edge cases (`q = p`, `q = 0` in a domain, and the zero-ring case). It is a genuine intermediate isomorphism, strictly smaller than the target, and its node and docstring give the proof source and steps.
4. Reviewed the proof route and pruning. The backward proof uses flatness, the quotient-fibre equivalence, the field-isomorphism transport, and the zero-fibre argument; the five removed proof-only imports and corresponding obsolete dependencies are not used. The realized unit route remains intact.
5. Verified that the DAG proof/proof_deps records agree with the Lean route, including the new quotient-fibre node and its source.

Changed only this report: recorded the second reading. No Lean declarations, definitions, statements, or DAG records required repair.
