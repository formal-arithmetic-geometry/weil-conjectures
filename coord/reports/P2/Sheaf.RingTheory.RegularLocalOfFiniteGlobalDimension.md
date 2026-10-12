## What changed

Implemented `IsRegularLocalRing.of_hasFiniteGlobalDimension` by extracting a finite projective resolution of the residue field, applying the residue-field projective-dimension upper and lower bounds, and comparing cotangent-space finrank with Krull dimension. Added the intermediate statement module `ResidueFieldFiniteProjectiveDimensionOfGlobalDimension`.

## Proved and sorry left

The target theorem `IsRegularLocalRing.of_hasFiniteGlobalDimension` is proved. The new theorem `Ring.residueField_hasFiniteProjectiveDimension` remains `sorry` as the strictly lower-level universe transport/extraction step.

## No longer needed

None; all original proof imports remain used.

## Where the brief, the DAG or earlier work was wrong

The direct extraction from `HasFiniteGlobalDimension.{u, max u v}` to a resolution in `ModuleCat.{u}` requires a universe transport step, so it was split into a dedicated intermediate theorem.

## New nodes

`lem-weil-pbc-residue-field-finite-projective-dimension`.

## Second reading by P2

1. Compared both delivered modules against the repository baseline. The existing target statement is byte-for-byte unchanged; the additional module is a separately stated lower-level extraction theorem and its node records the split. Verdict: pass.
2. Compiled all sandbox modules with `lcompile.py --all`. There are no errors, forbidden declarations, or `sorry` in definitions. The only remaining `sorry` is the named split theorem `Ring.residueField_hasFiniteProjectiveDimension`; the target proof itself is complete. Verdict: pass.
3. Checked the split statement against the finite-global-dimension definition and the residue-field use site. It is a strictly lower-level universe-transport/extraction claim needed by the target, with source and proof sketch documented in its docstring and matching DAG node; no duplicate declaration was found in the repository. Verdict: pass.
4. Read the proof from the target downward. It obtains a finite bound for the residue field, derives a finite Krull-dimension witness, applies the existing residue-field resolution bound and cotangent-space inequality, and concludes via the regular-local characterization. Imports remain necessary; no old proof dependency can be removed. Verdict: pass.
5. Checked the DAG node and report metadata against the Lean declarations. The split node has matching statement, proof dependency, origin, module, and declaration. Verdict: pass.

Changed only this report section; no Lean proof or statement changes were needed in second reading.
