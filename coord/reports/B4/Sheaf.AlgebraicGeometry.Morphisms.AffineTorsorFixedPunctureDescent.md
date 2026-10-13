## What changed

Added a core module splitting the proof into finite orbit enumeration and the fixed-orbit geometric descent step. The parent theorem now combines these two statements with a real Lean proof.

## Proved and sorry left

Closed `affine_torsor_fixed_puncture_descent` by applying the two core statements. `affine_torsor_orbit_data` is proved. One sorry remains in `affine_torsor_fixed_orbits`, which records the fixed-orbit geometric descent argument from Tags 03SF and 0EYG.

## No longer needed

None; the parent proof uses the imported core module and all original public imports remain required by the declarations.

## Where the brief, the DAG or earlier work was wrong

The original node packages orbit enumeration and effective affine descent into one proof step, but the latter is not available in Mathlib. The delivery separates that geometric step as a named intermediate theorem.

## New nodes

`lem-sbc-affine-torsor-fixed-puncture-descent-core` — fixed-orbit affine torsor descent step.

`lem-sbc-affine-torsor-fixed-puncture-orbit-data` — finite orbit representative data.

## Earlier second reading (a previous round; superseded)

Pending independent second reading.

## Second reading by B4

1. **Compilation and declarations.** Both delivered modules compile with
`lcompile.py --all`; the parent declaration has the same signature as the
repository version, and the only remaining `sorry` is the named theorem
`affine_torsor_fixed_orbits` in the new core module.

2. **Proof and axioms.** The parent proof is a real application of the two
core declarations. The orbit-data theorem is constructive and introduces no
axioms. The fixed-orbits theorem is explicitly split off with its Stacks
source and remains the sole open geometric step.

3. **Statements and nodes.** The new declarations and node records agree
verbatim. The orbit-data statement is a true finite existence lemma. The
fixed-orbits statement records the intended fixed-ring descent substep; its
proof is still open and therefore does not by itself certify the geometric
claim.

4. **Imports and pruning.** The parent keeps the core module as a proof-only
import. All public imports are required by the declarations; no old proof
dependency can be removed while the geometric substep remains split off.

5. **Route and unit.** The parent still follows the unit route through orbit
enumeration and fixed-orbit descent. The unit's `realized` route is unchanged.

No source or statement changes were made during this second reading. The
remaining geometric theorem should be reviewed before treating the target as
mathematically complete, since its universal `m,K` interface is stronger than
the particular orbit data used by the parent.
