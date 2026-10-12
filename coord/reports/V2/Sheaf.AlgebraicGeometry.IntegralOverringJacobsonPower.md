## What changed

Replaced the sole `sorry` in `integral_overring_jacobson_power` with a complete
proof using Mathlib. Added the proof-only import `Mathlib.RingTheory.Ideal.GoingUp`.
The statement and existing public imports are unchanged.

The proof derives integrality of both intermediate extensions, lifts maximal
ideals using `hspec`, and obtains finiteness by a surjection from the maximal
spectrum of the overring. For the radical equality, maximal-ideal contraction
proves one inclusion; `Ideal.IsPrime.inf_le'` applied to the finite family of
maximal ideals of B proves the other. Finally, maximal-ideal lifting puts x in
J(A), and radical membership gives a power; the zero exponent case is replaced
by exponent one because the extended ideal then contains one.

## Proved and sorry left

Closed: `integral_overring_jacobson_power`
(blueprint: `lem-sc-integral-overring-jacobson-power`).
No `sorry` remains, and no new holes, declarations, modules, or nodes were added.
Compilation passed with no warnings; axiom checking uses only the permitted
standard axioms.

## No longer needed

None. No original imports were removed and the proof uses all three original
DAG dependencies through their Mathlib declarations. There are no Sheaf proof
dependencies to prune. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement or mathematical-plan error was found. The finite-intersection
argument already has the Mathlib lemma `Ideal.IsPrime.inf_le'`, so no split
lemmas are necessary. The proof handles a zero ring or empty maximal spectrum
without extra hypotheses, and preserves the supplied `hspec` hypothesis.

## Second reading by V2

1. Compared the delivered module with the repository version: the theorem
   statement and all existing declarations are byte-for-byte unchanged; only a
   proof-only import and the proof body were added.
2. Compiled the module successfully and checked the declaration's axioms in a
   direct scratch copy. It uses only `propext`, `Classical.choice`, and
   `Quot.sound`; there are no `sorry`s, forbidden declarations, or hollow
   definitions.
3. The proof follows the stated Jacobson-radical argument. The finite maximal
   spectrum gives the prime-intersection step via `Ideal.IsPrime.inf_le'`, and
   the zero-exponent branch is handled explicitly, so the conclusion has the
   required positive exponent. No new statement was introduced.
4. The proof uses the existing Mathlib integral-extension results recorded by
   the node's proof dependencies; no shorter applicable library theorem was
   found, and all original public imports remain necessary for the interface.
5. The unit route and node statement are unchanged; the node's proof plan and
   proof dependencies remain consistent with the implemented argument.

Changed: added this second-reading record only; no Lean or DAG repair was
needed.
