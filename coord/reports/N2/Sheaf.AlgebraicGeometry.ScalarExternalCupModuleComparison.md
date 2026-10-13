## What changed

Restored the three scalar comparison modules. Change record: `coord/changes/scalar-external-cup-module-comparison.md`.

The external comparison theorem now
uses the two named pullback comparison equations, unfolds `externalCup`, and
combines them with `scalarCup_moduleCup_compatibility` via `congrArg₂`. Its public
signature is unchanged. The two prerequisite comparison theorems remain named
`sorry` declarations with their existing statements and documentation. Their DAG
records were updated to match the imports and proof route actually used.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.Scheme.Modules.scalarExternalCup_moduleComparison`
  (`lem-sc-scalar-external-cup-module-comparison`).

Sorries left:

- `AlgebraicGeometry.Scheme.Modules.scalarCup_moduleCup_compatibility`
  (`lem-sc-scalar-cup-module-cup-compatibility`).
- `AlgebraicGeometry.Scheme.Modules.scalar_moduleCohomologyPullback_comparison`
  (`lem-sc-scalar-module-cohomology-pullback-comparison`).

No new theorem or definition was added.

## No longer needed

The external comparison proof does not use `ModuleCohomologyFMap` directly; the
pullback comparison module supplies the required theorem. The pullback comparison
proof does not use `ModuleCohomologyCupProduct` directly. No prescribed unit step
or target statement was changed, and no lower module was adapted.

## Where the brief, the DAG or earlier work was wrong

The returned candidate unnecessarily included adaptations of
`Sheaf.Paper.ModuleCupKInjectiveTarget` and
`Sheaf.Paper.ModuleCupNaiveDerivedCompatibility`. Their original files compile
unchanged against the delivered dependencies, so they are not forced adaptations
and have been removed. With those files removed, the required `deliver3.py --no-push`
dry run passes. The duplicate-instance collision remains an issue only for the
separate combined probe that imports global tensor normalization before the
K-injective module; it is outside this item's delivered import closure.

## Earlier second reading (a previous round; superseded)

The second reader should compile the three delivered modules and inspect the three
DAG records. The external theorem's signature is unchanged from its node and its
proof is a real reduction to the two strictly lower named statements; the lower
statements are unchanged prerequisite interfaces. No unit route or target statement
is altered.

## Second reading by N2

1. Compared the delivered declarations with the repository and DAG records. The
   external comparison signature and the two prerequisite signatures are unchanged;
   no accidental statement or definition change was found. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. The build is
   clean. An axiom probe reports only the permitted logical axioms together with
   `sorryAx` from the two intentionally open prerequisite theorems. There are no
   `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions. Verdict: pass.
3. Checked the two split-off declarations against their DAG nodes, docstrings,
   and source descriptions. They are strictly lower interfaces required by the
   external reduction and are not duplicates found elsewhere in `lean/`. Verdict:
   pass.
4. Read the proof from the target downward. It unfolds `externalCup`, applies
   `scalarCup_moduleCup_compatibility`, and transports both arguments with the two
   named pullback comparison equations. The stated proof-only imports are minimal
   for this route, and the removed adaptations are not needed. Verdict: pass.
5. Checked the DAG proof steps, dependencies, origins, and the unit record against
   the Lean proof. The `sk-prop-av-cube` route remains intact and no target
   statement is changed. Verdict: pass.

Changed only this report; no Lean or DAG repair was necessary.
