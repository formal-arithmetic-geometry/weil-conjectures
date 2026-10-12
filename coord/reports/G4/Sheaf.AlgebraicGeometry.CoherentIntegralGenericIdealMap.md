## What changed

The target theorem is proved by combining two strictly simpler intermediate theorems. Added construction and generic-injectivity modules and imported them privately.

## Proved and sorry left

`coherent_integral_generic_ideal_map` is proved. The new intermediate declarations `coherent_integral_generic_ideal_construction` and `mono_of_coherent_ideal_sum_generic_iso` remain `sorry`, with nodes `lem-weil-pbc-coherent-integral-generic-ideal-map-construction` and `lem-weil-pbc-coherent-integral-generic-ideal-map-mono`.

## No longer needed

None; all original imports remain available to the intermediate construction statement.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was too large to realize directly in one worker interval; it omitted a clean decomposition into construction and injectivity assertions.

## Earlier second reading (a previous round; superseded)

Pending second reading.

## Second reading by G4

1. Compared the delivered target module with the repository version. The target
   declaration and all existing signatures are unchanged; only its proof and
   private imports differ. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; compilation is
   clean and the only remaining `sorry`s are the two named split theorems. Verdict:
   pass.
3. Checked both split statements against Stacks Tag 01YE. They are true,
   strictly simpler than the target, and their docstrings state the source and
   complete mathematical reductions. Verdict: pass.
4. The target uses the construction and generic-injectivity route, retaining the
   unit's route. The mono module's module-stalk-functor import is public because
   it occurs in the exported type. Verdict: pass.
5. The DAG nodes' statements, proof steps, dependencies, source, unit, and
   chapter agree with Lean; no target statement or definition changed. Verdict:
   pass.

Changed the split theorem docstrings, corrected the mono module's public
signature import, and completed both DAG proof records.

## New nodes

Added `lem-weil-pbc-coherent-integral-generic-ideal-map-construction` and `lem-weil-pbc-coherent-integral-generic-ideal-map-mono`.
