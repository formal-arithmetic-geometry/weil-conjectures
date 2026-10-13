## What changed

Proved `AlgebraicGeometry.thickeningSystemPushforward_adjacent_isIso` with its
existing signature byte for byte unchanged. The proof computes the adjacent
immersion kernel, applies the existing normalized ideal-power quotient theorem,
and pushes that quotient through the ideal-power comparison. It transports the
quotient along eG and cancels its epimorphic projection to identify the pushed
adjoint as a composite of isomorphisms. Fully faithful closed pushforward then
reflects invertibility.

Added proof-only imports of `ClosedImmersionPowerQuotient` and
`CoherentFiniteTypeLocallyNoetherian`. Replaced the original direct import of
`ClosedImmersionUnitQuotient` by the former, which uses it transitively.
All existing public imports are unchanged. No definitions or statements changed.
Updated the item's existing DAG node to record the actual four proof steps and
their dependencies. No change record is needed.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.thickeningSystemPushforward_adjacent_isIso`
(node `lem-weil-pbc-thickening-system-pushforward-lifting-termwise`).
There are no holes left in the delivered module and no holes added anywhere.
Zero statements are split off in this delivery. This proves the item from existing
library lemmas, some of which remain open; it does not claim the global target
closure is axiom-free. The scratch `#print axioms` check reports only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx` from existing dependencies.
The ledger determines the net change in the targets' import closure.

The first reader's proposed
`AlgebraicGeometry.thickeningSystemPushforward_adjacent_pushforward_isIso`
was not accepted: it retained all target hypotheses and an equivalent conclusion.
Its unproved module and node are removed from the delivery, rather than counted
as a proof or as a new decomposition.

## No longer needed

Removed the direct proof import of
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient` and its direct dependency
`lem-weil-pbc-closed-immersion-unit-quotient`; both remain needed transitively
through `ClosedImmersionPowerQuotient`. The other two original proof dependencies
(ideal-power pushforward and full faithfulness) are used directly.
No existing library module is claimed to be pruned from the targets' closure.
The draft-only `ThickeningSystemPushforwardAdjacentPushforwardIsIso` module and
its proposed `lem-weil-pbc-thickening-system-pushforward-lifting-termwise-pushforward`
node are not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker missed the existing public theorem
`AlgebraicGeometry.closedImmersion_power_quotient`, which is available in the
compiled library and includes the unit normalization for any supplied adjunction.
The planned geometric reduction can therefore be written without any new lemma.
Its proposed pushforward-isomorphism helper was equivalent to the item, and lacked
a complete docstring proof. The first draft also omitted the item's docstring and
failed to update its existing DAG proof.

An initial attempt to use `quotient_unit_power` from the current source of
`ThickeningSystemPushforwardAdic` found that helper absent from the published
compiled version. No such proof was duplicated or adapted: the public
`closedImmersion_power_quotient` already supplies the required result.

## Second reading by H4

1. Compared the delivered file with the repository file by diff and separately
   asserted byte-for-byte equality from the existing theorem keyword through its
   complete signature. No existing statement, definition, visibility, or public
   import changed. Verdict: pass.
2. Compiled the final file with lcompile.py with no errors or warnings. Scanned
   the delivered Lean for sorry and forbidden declarations: none. Compiled a
   scratch copy with #print axioms: only the three permitted axioms and sorryAx
   from existing imported obligations. No data definition or arbitrary witness
   construction was added; the locally obtained quotient isomorphisms are
   uniquely determined by their projection equations. Verdict: pass.
3. Refused and removed the equivalent split-off theorem. Repeated semantic search
   for closed immersion direct image/pullback quotients, Loogle search for the
   adjunction unit equation, and rg searches for ideal-power quotient/unit
   comparisons in both source roots. These located ClosedImmersionPowerQuotient.
   There is no new statement to validate. For the used reductions, n=0 uses the
   positive exponent 1; zero modules, zero ideal, and unit ideal preserve the
   quotient identities and categorical cancellation. Arbitrary supplied
   adjunctions are handled by the existing normalized theorem. Verdict: pass.
4. The proof now derives the item from the existing geometric dependencies plus
   the existing ideal-power quotient theorem and the coherent/quasi-coherent
   criterion. Imports needed only for proofs are private. The original unit
   quotient dependency remains transitive. Read sk-thm-p1's realized statement
   and steps: this below-unit reduction bypasses none of them. Verdict: pass.
5. Updated the existing node's proof, proof_deps and proof_origin to match the
   kernel calculation, normalized quotient comparison, quotient transport and
   cancellation, and fully faithful reflection. No new nodes or changed
   statements remain. Verdict: pass.

Second reading changed: removed the equivalent helper module/node, restored the
original docstring, wrote the actual geometric and categorical proof, replaced
the direct unit-quotient import by the existing power-quotient import, added the
coherence criterion import, and corrected the DAG and this report.
