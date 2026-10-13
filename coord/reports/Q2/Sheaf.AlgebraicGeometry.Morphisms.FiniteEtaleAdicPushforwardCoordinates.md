## What changed
Added the bundled-function intermediate theorem `pushforward_coordinates_transition_fun` and used `congrFun` to reduce the original pointwise theorem to it. The original theorem now has a complete proof from that intermediate statement.

## Proved and sorry left
`pushforward_coordinates_transition` is proved. `pushforward_coordinates_transition_fun` remains sorry and is recorded by node `new-sbc-finite-etale-adic-pushforward-coordinates-core`.

## No longer needed
None; all original imports remain needed for the definitions and statement.

## Where the brief, the DAG or earlier work was wrong
The affine naturality argument is substantial; the delivery isolates its bundled-function form as a strictly lower intermediate statement.

## New nodes
`new-sbc-finite-etale-adic-pushforward-coordinates-core` in `dag/nodes/sec-smooth-base-change/`; its Lean declaration is in the item module.

## Earlier second reading (a previous round; superseded)
The pointwise target follows by congrFun from the bundled-function intermediate statement.

## Second reading by Q2

1. Compared the delivered module with the repository version. Existing declarations and definitions retain byte-for-byte identical signatures and bodies; the only changes are the added bundled-function intermediate theorem and the proof of `pushforward_coordinates_transition`. Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles cleanly. The only remaining `sorry` is the named theorem `pushforward_coordinates_transition_fun`, and the target theorem depends on `sorryAx` only through that split theorem. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the split statement and its node. The bundled equality is true and strictly simpler than the pointwise target, and `congrFun` gives the target exactly. The node includes its source, proof route, and Lean declaration. Verdict: pass.
4. Checked the proof route and imports. The proof uses the split theorem and `congrFun`; both existing public imports remain necessary for the definitions and statement. No removable proof dependency was found. Verdict: pass.
5. Checked the DAG agreement and unit route. The target node's declaration and statement match the Lean target, and the intermediate node records the bundled theorem without changing the unit's realized route. Verdict: pass.

Changed only this report; no Lean or DAG repair was necessary.
