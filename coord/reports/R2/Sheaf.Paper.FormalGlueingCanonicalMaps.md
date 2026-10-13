## What changed

Proved all four original theorems in `Sheaf.Paper.FormalGlueingCanonicalMaps` without
changing their signatures or existing docstrings. Added the proof-only import
`Mathlib.RingTheory.Localization.BaseChange`. Added proved private helpers for cancellation,
localizing invertible scalar multiplication, powers of invertible scalars, iterated-localization
extensionality, and the identity equivalence between natural and restricted tensor actions.
Updated the canonical-maps node's proof route and dependencies to match these proofs.

`away_map_functorial` specializes Mathlib's composition and identity theorems and linearity.
`localizedSModule_properties` uses the defining fraction formula and fraction induction.
`swap_properties` uses localized invertibility, denominator cancellation, the existing swap
uniqueness theorem, and two applications of localization extensionality.
`compare_properties` uses localization under tensoring, tensor commutativity, the existing
comparison composition equation, tensor induction, and the induced linear equivalence.
The localized action is the existing definition; no arbitrary witness or data was introduced.
The comparison proof needs additional elaboration heartbeats for the tensor and scalar instances.

## Proved and sorry left

Closed all four holes of node `lem-weil-pbc-formal-glueing-canonical-maps`:

- `LocalizedModule.away_map_functorial`.
- `FormalGlueing.localizedSModule_properties`.
- `FormalGlueing.swap_properties`.
- `FormalGlueing.compare_properties`.

No sorry remains in the item and no new sorry was added. All private helpers are proved.
These are proofs from the existing downstream statements, not claims that the full axiom
closure is already sorry-free: the action uses `FormalGlueing.exists_localized_s_module`,
the swap uses `FormalGlueing.exists_swap`, and the comparison uses
`FormalGlueing.exists_compare` and `FormalGlueing.compare_smul`, all existing holes in
`Sheaf.RingTheory.FormalGlueingData` (node `def-weil-pbc-formal-glueing-data`).

## No longer needed

None. Both original public imports support the statements and remain required. All four
original proof-dependency nodes are used, and the defining module's node is now explicitly
recorded as a proof dependency. No unit statement or realized step is bypassed. No standalone
new iterated-localization theorem or new tensor-comparison theorem is needed.

## Where the brief, the DAG or earlier work was wrong

The module did not yet import the Mathlib module for the planned tensor-localization step;
this delivery adds it as a proof-only import. Natural tensor R-actions and actions restricted
from S agree through an explicit identity linear equivalence, rather than by definitional
identity. The existing uniqueness constructions already supply the defining values and
uniqueness, so they need not be reconstructed here. Edge cases f = 0, g = 0, zero modules,
and unequal module universes need no extra assumptions: the localization unit and cancellation
arguments apply uniformly.

## Second reading by R2

1. **Interfaces: PASS.** Compared the entire delivered module with the repository version
   and checked the declaration table: all four existing signatures, visibility and docstrings
   are byte-for-byte unchanged. The only added import is proof-only. The new declarations are
   private proved helpers; the identity tensor equivalence constructs its maps explicitly.
   No public definition, target statement or change record is changed or needed.
2. **Proofs and axioms: PASS.** The module compiled without errors or warnings (57.5 s).
   A scratch copy with `#print axioms` for all four theorems compiled (56.6 s):
   `LocalizedModule.away_map_functorial` uses only `propext`, `Classical.choice`, `Quot.sound`;
   the other three additionally use `sorryAx` from the existing defining theorems listed above.
   There is no `sorry` in the delivered source and no forbidden declaration or kernel bypass.
   The chosen localized action is determined on every fraction, so the existing existence
   statement determines its data; swap and compare are chosen from unique specifications.
3. **Split statements: PASS, none.** No new public statement or hole was split off. Read the
   five private helpers: fraction cancellation is `smul'_mk` plus `mk_cancel`; invertibility
   survives localization by `map_injective`/`map_surjective`; powers preserve units; iterated
   extensionality applies `IsLocalizedModule.ext` twice; the tensor equivalence is the identity
   with scalar compatibility `algebraMap_smul`. These proofs do not assume f or g is nonzero.
   If f or g is zero the relevant localization is zero and the same arguments hold; f = 1,
   zero modules, and unequal module universes likewise need no added hypothesis.
4. **Route and pruning: PASS.** Searched the local Sheaf library for scalar-bijectivity and
   localization comparison alternatives, and read Mathlib `map_injective`, `map_surjective`,
   `ext`, `linearEquiv`, and `rTensor`. The helpers package these existing facts rather than
   introducing another unfinished result. All imports are used: Basic supplies signature
   constants, FormalGlueingData supplies signature definitions and their specifications, and
   the private BaseChange import supplies `IsLocalizedModule.rTensor`. All four old DAG
   dependencies remain used, so the report's pruning list is complete. Read
   `dag/units/sk-thm-p1.json` realized statement and steps: none is altered or bypassed.
5. **DAG agreement: PASS.** Compared both node records. Only `proof`, `proof_deps`, and
   `proof_origin` changed. The seven steps match respectively functoriality, fraction action,
   invertibility, swap cancellation/uniqueness, inverse composites by extensionality,
   tensor-localization with comparison values/uniqueness/S-linearity, and the final induced
   equivalence. The new dependency on FormalGlueingData records the existing specifications
   actually used. The proof-dependency set is exactly the union of the steps' uses.

Second reading changed only this review report; no proof repair was needed. Four original
holes are closed, zero holes are added, and no modules are pruned. This delivery does not
claim to close the existing dependency holes or to establish a sorry-free target closure.
