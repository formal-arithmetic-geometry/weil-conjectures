## What changed

Proved `exists_derivedPullback_kFlat_counit_data` using the existing derived pullback
witness and a new acyclic intermediate shifted-unit interface. Identified the witness
functor with `Scheme.Modules.tensorPullback f` by `Functor.ext`.

## Proved and sorry left

`AlgebraicGeometry.exists_derivedPullback_kFlat_counit_data` is proved. The new
`AlgebraicGeometry.exists_derivedPullback_shifted_unit_iso` remains a named sorry,
with node `lem-sc-derived-pullback-shifted-unit-iso-data`.

## No longer needed

The downstream `DerivedPullbackTensorUnitShift` import was removed because it creates an
import cycle through cone normalization.

## Where the brief, the DAG or earlier work was wrong

The original route omitted the existing `exists_derivedPullback` counit witness and did not
account for the cycle caused by importing the downstream translated-unit shift theorem.

## New nodes

`lem-sc-derived-pullback-shifted-unit-iso-data` records the strict shifted-unit component
needed by this theorem.

## Second reading by D2

1. Compared the delivered module with the repository version. The target theorem
   signature is unchanged; the only added declaration is the documented split-off
   shifted-unit interface. Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`. There are no errors,
   forbidden declarations, or sorries outside the named shifted-unit theorem.
   The counit theorem uses the existing `exists_derivedPullback` witness and
   identifies its functor by `Functor.ext`. Verdict: pass.
3. Checked the split-off statement against the monoidal and shifted-unit
   construction. It is the exact intermediate isomorphism required by the target,
   with no added hypotheses or weakened conclusion, and its docstring records the
   source and construction. Verdict: pass.
4. The proof follows the existing derived-pullback witness and the new shifted-unit
   interface; the downstream tensor-unit-shift import is not needed and is absent.
   Verdict: pass.
5. Updated the target node's proof and proof dependencies to name the shifted-unit
   node actually used by Lean. The unit remains `sk-thm-picard-duality` and its
   realized route is preserved. Verdict: pass.

Changed the split theorem docstring to include its proof argument and blueprint
identifier, and corrected the target node metadata to match the proof.

The linter-setting change is recorded in `coord/changes/DerivedPullbackKFlatCounitData-linter.md`.
