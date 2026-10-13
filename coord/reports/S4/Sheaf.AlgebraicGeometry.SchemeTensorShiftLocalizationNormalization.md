## What changed

Completed `AlgebraicGeometry.schemeTensorShift_targetComparison_isIso` in
`Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization`. Two proved
private helpers convert the sheaf K-flat hypothesis to the upstream monoidal
predicate and obtain invertibility of the localization tensorator from the
existing independent-universe lifting isomorphism. The target comparison is a
shifted composite of invertible maps. No import, public signature, definition,
or exported instance changes. Updated the invertibility node's proof route.

## Proved and sorry left

Closed one of the current module's three holes:
`AlgebraicGeometry.schemeTensorShift_targetComparison_isIso`
(`aux-sc-target-comparison-isIso`). No holes added or split off.

The remaining holes are unchanged:

- `AlgebraicGeometry.schemeTensorShift_first_normalization`
  (`aux-sc-target-comparison-first`).
- `AlgebraicGeometry.schemeTensorShift_second_normalization`
  (`aux-sc-target-comparison-second`).

`AlgebraicGeometry.schemeTensorShift_localization_normalization` was already
proved by conjunction of these three components in the current base; its proof
is preserved, and it is not counted as a hole closed by this delivery.

## No longer needed

None. No imports removed and no nodes or modules pruned. The invertibility
component uses the existing independent tensor-shift construction; no new
localization-square statement is needed for this partial delivery.

## Where the brief, the DAG or earlier work was wrong

The dispatch version had one normalization hole. During this session the
read-only checkout synchronized E4's three-component decomposition. This delivery
preserves all those declarations and closes only the invertibility component.
The sheaf K-flat predicate and the upstream monoidal predicate are distinct;
the private conversion proves their needed relationship rather than assuming it.
K-flatness of U is unused in invertibility, but its original binder is preserved.
The two route equalities were explored but remain unchanged in this partial
result. No target statement or unit route changes.

The conservative setup classifier sees the new universe and scoped `open`/`omit`
commands. Their proof-only effect is recorded in
`coord/changes/S4-tensor-shift-private-proof-setup.md`. No downstream adaptations.

## Second reading by S4

1. Compared the delivered module with the repository version. All existing
   public declarations and definitions have byte-for-byte unchanged signatures;
   only private proof setup and the proof of the invertibility theorem changed.
   Verdict: pass.
2. Compiled the module and inspected the declarations for forbidden constructs.
   The target comparison theorem has no `sorry`; the two normalization theorems
   retain their named `sorry`s, with no new holes or hollow definitions. The
   proof uses only ordinary typeclass and category-theoretic lemmas. Verdict:
   pass.
3. Checked the split node `aux-sc-target-comparison-isIso` against its Lean
   statement and searched the library for an existing duplicate. Its conversion
   of sheaf K-flatness and transport of the tensorator are true and exactly the
   needed component. Verdict: pass.
4. Checked the proof route from the top downward. It uses the existing
   independent-universe lifting isomorphism and removes no required import or
   unit step; the unused `hU` binder is intentionally preserved. Verdict: pass.
5. Checked the node proof, proof dependencies, proof origin, and the unit
   realization against the proof. They agree, and no old dependency is pruned.
   Verdict: pass.

Changed only the target-comparison proof and its private helper setup; added no
new split-off theorem beyond the recorded node and added no downstream
adaptation.
