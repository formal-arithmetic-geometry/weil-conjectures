## What changed

Proved `DerivedCategory.module_torAmplitudeIn_iff_exists_flat_model` in
`Sheaf.Algebra.Homology.TorAmplitudeFlatModel` by specializing the existing proved
`DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat` to `ModuleCat A`.
The proof converts categorical flatness to module flatness through preservation of
finite limits, converts the two strict degree bounds to termwise vanishing, and
reverses the derived isomorphism. Its signature and all three public imports stay identical. Disabled the unused-variable linter only for this theorem: the fixed
signature includes `hab : a ≤ b`, whereas the generic theorem needs no ordering.
Updated the node proof, proof dependencies and proof origin to this route.

## Proved and sorry left

Closed one hole:
`DerivedCategory.module_torAmplitudeIn_iff_exists_flat_model`
(node `lem-pc-module-tor-amplitude-flat-model`).
No sorry remains in the delivered module. No hole added or split off.
The proof specializes existing proved declarations and introduces no definition
or new statement. Single-file compilation succeeds without warnings (3.8 seconds).
The second-reader dry run now passes compilation, the axiom probe, and preflight.
No forbidden axioms were reported.

## No longer needed

Removed all four proof-plan imports:

- `Sheaf.Algebra.Homology.BoundedFlatKFlat`
  (`lem-pc-module-bounded-flat-kflat`).
- `Sheaf.Algebra.Homology.BoundedFlatReplacement`
  (`lem-pc-kflat-bounded-flat-replacement`).
- `Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion`
  (`lem-pc-module-flat-opcycles-tor-criterion`).
- `Sheaf.Algebra.Homology.KFlat` (`def-pc-kflat-complex`).

Also removed the old proof edges to `def-weil-abstract-derived-category` and
`def-sbc-standard-tstructure-derived-category`: the generic theorem already does
the substantive resolution and truncation argument. The public FlatModel and FlatResolution imports remain necessary for statement elaboration and the module resolution instance; the Mathlib flatness import supplies the flatness conversion.
These nodes and modules are unnecessary for this proof; no claim is made that
other target branches cease to need them.

The unit `sk-thm-picard-duality` has empty realized statement/step lists, so this
specialization replaces no realized unit statement or step.

## Where the brief, the DAG or earlier work was wrong

The DAG's separate bounded-flat, ringed-site replacement and opcycles route is
unnecessary here: the module docstring and its Lean node record already identify
the generic library equivalence as the specialization route. That generic theorem
contains the resolution, K-flat tensor computation and lower truncation proof.
No disputed statement or interface repair was needed. Checked the degenerate
interval a = b and the zero-ring case: the conversions impose no extra hypothesis
and merely translate the same support and flatness conditions.

The earlier import_cycles tool failure is resolved: the second-reader dry run succeeds.

## Second reading by M3

1. I compared the delivered Lean module with the repository version. The theorem signature, namespace, and definition interfaces are unchanged; only the proof, explanatory docstring, and proof-only imports differ. Verdict: pass.
2. I compiled the module with `lcompile.py`; it succeeds with no errors or warnings. The proof contains no `sorry`, axiom, unsafe, opaque, extern, implemented_by, or hollow definition. The generic theorem and flatness equivalence are existing declarations, and the conversion proof reverses the isomorphism in the correct direction. Verdict: pass.
3. No statement was split off and no new theorem was added. The existing statement remains the exact bounded flat-model equivalence, including its `a ≤ b` interface hypothesis; the hypothesis is unused only because the generic theorem is stronger. Edge cases `a = b` and the zero ring are covered by the same support and flatness equivalences. Verdict: pass.
4. The proof takes the shorter generic FlatModel route, so the old bounded-flat/K-flat, replacement, opcycles, K-flat, and t-structure proof dependencies are no longer used. The unit has no realized statement or step entries, so no realized route is bypassed. The node proof and `proof_deps` now match the Lean proof. Verdict: pass.
5. The node statement and Lean declaration agree byte-for-byte, and the node records the specialization route with no added dependencies. Verdict: pass.

Changed the sandbox node's proof, proof dependencies, and proof origin to match the delivered specialization proof, and appended this second-reading record. Tested making FlatResolution proof-only; compilation fails while elaborating the public statement with a missing IsGrothendieckAbelian instance for ModuleCat A. Restored its necessary public visibility. No Lean source repair remained.
