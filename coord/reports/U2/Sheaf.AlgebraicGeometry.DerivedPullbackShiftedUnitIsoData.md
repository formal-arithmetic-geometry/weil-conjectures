## What changed

Replaced the proof of `AlgebraicGeometry.exists_derivedPullback_shifted_unit_iso`
in `Sheaf.AlgebraicGeometry.DerivedPullbackShiftedUnitIsoData`.
Extract the shift-compatible triangulated structure of the chosen functor from
`Classical.choose_spec (exists_derivedPullback f)`. Install its `CommShift` structure
locally. Evaluate `Functor.commShiftIso` at the source monoidal unit and compose
with the target shift functor applied to `(Functor.Monoidal.εIso _).symm`.
This implements the existing node's monoidal translated-unit proof plan.
The signature, docstring, public imports, and definitions are unchanged.
No new modules, declarations, assumptions, or holes are introduced.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.exists_derivedPullback_shifted_unit_iso`
(node `lem-sc-derived-pullback-shifted-unit-iso-data`).
No `sorry` remains in the item's module; no holes are added or split off.
This is a complete composition of existing comparison isomorphisms, not a
restatement or decomposition. Its shift structure comes from the existing
`AlgebraicGeometry.exists_derivedPullback` theorem; the monoidal comparison comes
from the given strong monoidal instance. Dependencies retain their existing proofs.

## No longer needed

None. Both planned dependency nodes remain needed:
`def-pc-derived-pullback` supplies the functor and its shift structure;
`def-pc-scheme-derived-tensor-structure` supplies the recorded monoidal categories.
No proof-only imports were present or added. The existing public imports provide
statement types and the triangulated interface used to extract the shift data.
No unit statement or step is bypassed; the unit record's realized lists are empty.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction is needed. The comparison already follows from the
shift structure included in `exists_derivedPullback` and Mathlib's monoidal unit
isomorphism. No additional translated-unit or counit-coherence lemma is required
for this statement, which asks only for a nonempty isomorphism type.

## Second reading by U2

1. Compared the delivered module with the repository version. The theorem
   signature, docstring, and definitions are byte-for-byte unchanged; only the
   proof body and one import visibility were changed. Verdict: pass.
2. Compiled the module and checked `#print axioms`; it compiles cleanly and uses
   only `propext`, `Classical.choice`, and `Quot.sound`, with no remaining
   `sorry`, axiom, unsafe declaration, or hollow definition. Verdict: pass.
3. Checked the proof against the existing declarations and searched for an
   upstream duplicate. The proof uses the chosen `CommShift` structure from
   `exists_derivedPullback` and the existing monoidal unit isomorphism; no new
   statement was added and the target is unchanged. Verdict: pass.
4. Checked the proof route and pruning. The two DAG proof dependencies remain
   used, while `Mathlib.CategoryTheory.Triangulated.Functor` is proof-only and
   is now a private import. The unit route is preserved. Verdict: pass.
5. Checked the node metadata against the Lean proof and the unit record; the
   existing node's declaration, proof dependencies, and origin agree, with no
   new nodes or split-off holes. Verdict: pass.

Changed the Triangulated.Functor import from public to private and recorded it
under `## No longer needed`; no mathematical or interface changes were made.
The change record is `coord/changes/derived-pullback-shifted-unit-iso-import.md`.
