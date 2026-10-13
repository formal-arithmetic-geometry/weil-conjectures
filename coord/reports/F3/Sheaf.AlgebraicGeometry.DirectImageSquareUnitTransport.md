## What changed

Filled the proof of `AlgebraicGeometry.directImageSquare_unit_transport`.
The proof uses equality transport for the direct image and its right-derived unit,
then normalizes the reflexive pushforward composition comparisons. Local
irreducibility and transparency settings keep the derived-category elaboration
within the file limit. No public signatures, definitions, or imports changed.

## Proved and sorry left

Closed `AlgebraicGeometry.directImageSquare_unit_transport`, node
`lem-pc-direct-image-square-unit-transport`. No `sorry` remains and no new
sorry-bearing declarations were added.

## No longer needed

None. The existing import is required for the definitions and derived-category
unit. No DAG modules or proof dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The planned two-step proof is valid. The only implementation issue was
elaboration cost from unfolding chosen derived functors; local irreducibility
attributes and explicit transparency settings resolve it without changing the
mathematical route.

The static preflight flags added scoped commands; their lack of exported effects
is documented in
`coord/changes/directImageSquareUnitTransport-local-transparency.md`.

## Second reading by F3

1. Unchanged interface: compared the sole delivered Lean module against the
   repository with `diff -u` and the declaration parser. All existing declaration
   signatures are byte-for-byte unchanged; `directImageSquareIso`, the previous
   sectionwise theorem, and the imports are unchanged. Added helpers are private.
   The scoped attributes and per-declaration options affect elaboration only;
   their scope is documented in the existing change record. Verdict: pass.
2. Proof and axioms: compiled the delivered file cleanly with `lcompile.py`
   (43.7 seconds). Compiled a scratch copy with `#print axioms` for
   `directImageSquareIso`, `directImageSquareIso_top`, `pushforwardCongr_eq`,
   `directImage_unit_congr`, and `directImageSquare_unit_transport` (42.6 seconds).
   Each uses only `propext`, `Classical.choice`, and `Quot.sound`; none uses
   `sorryAx`. No prohibited declarations or hollow definitions occur. Verdict: pass.
3. Split statements: none. Both new private helpers are fully proved. Their
   equality induction handles the reflexive case; the first reduces by
   extensionality over every open, and the second reduces to identity maps.
   Zero complexes, identity squares, and empty schemes require no extra
   hypothesis. Searched the library by congruence and transport terminology and
   read Mathlib's pushforward composition/congruence definitions and generic
   `eqToHom_naturality`; no missing split-off obligation exists. Verdict: pass.
4. Route and pruning: the proof first unfolds the reflexive Mathlib composition
   comparisons, then uses equality induction for the single unit. This follows
   the original two elementary steps without invoking any open lemma. The sole
   public import supplies the definitions in the signature and cannot be pruned.
   The old `proof_deps` is empty, so `No longer needed: None` is complete.
   `dag/units/sk-thm-picard-duality.json` does not list this auxiliary node in its
   `realized` fields; no unit statement, step, or route is replaced. Verdict: pass.
5. DAG consistency: the node's statement and dependencies agree with the Lean.
   Updated its two proof-step texts to describe the actual unfolding,
   extensionality, and equality-induction proof and updated `proof_origin` to F3.
   Kept `proof_deps` empty and every other node field unchanged. No new nodes
   were needed. Verdict: pass.

Second reading changed only the node's proof description and proof attribution,
plus this report. The Lean proof and the scoped-command change record needed no
repair. One existing hole closed (`AlgebraicGeometry.directImageSquare_unit_transport`),
zero holes added, zero split off; this is a proof, not a decomposition.
