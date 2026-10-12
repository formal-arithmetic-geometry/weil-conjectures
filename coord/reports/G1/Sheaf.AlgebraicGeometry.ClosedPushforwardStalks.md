## What changed
Proved `AlgebraicGeometry.closedImmersion_pushforward_stalks` completely, with the
existing signature and original docstring unchanged. The proof handles off-image
vanishing, the on-image isomorphism and bijectivity, scalar compatibility, and
naturality directly using Mathlib. Removed the first worker's temporary intermediate
statements and all three proposed split nodes, since no gap remains. Replaced the
public TensorPullback and ClosedImmersion imports with Mathlib.Modules.Sheaf, and
removed the plain PresheafModuleStalkFunctor import. Added the proof-only Grp.Zero
import. Import change record:
`coord/changes/closedImmersion_pushforward_stalks-imports.md`.

## Proved and sorry left
`AlgebraicGeometry.closedImmersion_pushforward_stalks` is proved: one of one original
open declarations. No `sorry` remains and none is split off. A scratch copy with
`#print axioms AlgebraicGeometry.closedImmersion_pushforward_stalks` compiled and
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed
Removed imports:
- `Sheaf.AlgebraicGeometry.TensorPullback`;
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`;
- `Sheaf.Topology.PresheafModuleStalkFunctor`.

Removed old proof dependencies:
- `def-pc-module-pullback`: its recorded tensor-pullback declarations are unused;
  the required pushforward is Mathlib's `Scheme.Modules.pushforward`.
- `def-weil-pbc-module-stalk`: its recorded custom stalk functor is unused;
  Mathlib's stalk, representative, and scalar-action API proves the calculation.
- `def-weil-closed-immersion`: the stated hypothesis is a closed embedding and the
  proof does not use `IsClosedImmersion` or its surjectivity hypothesis.

`def-pc-scheme` remains used. The removed modules may still be needed by other
items; this report prunes them only from this item's proof. None of these nodes
realizes a step in `dag/units/sk-thm-p1.json`; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong
The first worker left `sorry` inside a partial proof, supplied split docstrings
without complete proofs or sources, and supplied placeholder node statements,
empty searches, and circular proof dependencies on the original theorem. Its
report did not account for these defects or update the original node's proof.
The three gaps could all be closed with Mathlib germ calculations. The original
statement and its source argument are sound and require no mathematical correction.

## Second reading by G1
1. Compared the final module with the repository version by diff and checked the
   theorem signature byte for byte. The original signature and docstring are
   unchanged. No definition or target statement is altered. Verdict: pass.
2. Compiled the module locally without errors or warnings. It has no `sorry`,
   axiom declaration, unsafe/opaque declaration, extern or implementation override.
   A scratch copy's `#print axioms` reports only the three permitted axioms.
   Verdict: pass.
3. No split-off statement or new declaration remains. Checked the off-image proof
   also for empty source and empty inverse-image opens; the terminal-object argument
   applies without a nonempty-source hypothesis. The isomorphism uses inducing maps,
   while scalar compatibility and naturality need no embedding assumption. Searched
   Mathlib by grep, Loogle, and LeanFinder and read its stalk, scheme-module, and
   scalar-action APIs, as well as the existing closed-pushforward library modules.
   Verdict: pass.
4. Used Mathlib's cofinality isomorphism and germ identities. Removed unused imports
   and all old proof dependencies not used by their recorded declarations; the
   `No longer needed` section is complete. Inspected `sk-thm-p1.realized`: no unit
   statement or step is bypassed. The import change record reviews all eight direct
   importers and their alternate imports; `import_prune_check.py` passed with no
   lost downstream declaration reported. Verdict: pass.
5. Rewrote the original node's proof, proof_deps, and proof_origin to describe the
   actual four-part Lean proof. No new nodes remain and all other node fields are
   unchanged. Verdict: pass.

Changed the first worker's work by proving all three gaps, inlining the complete
argument in the original declaration, removing the provisional split declarations
and nodes, pruning unused imports and dependencies, restoring the original theorem
docstring, and replacing its placeholder report with this checked account.
