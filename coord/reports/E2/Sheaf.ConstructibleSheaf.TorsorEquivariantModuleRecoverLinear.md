## What changed

Kept the existing signature, visibility, public import and documentation of
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_recoverLinear`
byte for byte. Its new proof recovers a unique map from diagonal values on the
single torsor object, propagates that formula to arbitrary etale objects, and
restricts any competing global formula to the diagonal to establish uniqueness.
The two geometric steps are named intermediate theorems in their own modules,
imported with plain, proof-only imports. No data definition changes or additions.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_recoverLinear`
(node `lem-weil-pbc-torsor-equivariant-module-recover-linear`).
Holes added:

- `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_recoverLinear_diagonal`
  (node `lem-weil-pbc-torsor-equivariant-module-recover-linear-diagonal`), in
  `Sheaf.ConstructibleSheaf.TorsorEquivariantModuleRecoverLinearDiagonal`.
- `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_pointwise_of_diagonal`
  (node `lem-weil-pbc-torsor-equivariant-module-pointwise-from-diagonal`), in
  `Sheaf.ConstructibleSheaf.TorsorEquivariantModulePointwiseFromDiagonal`.

No sorry remains in the item's module. Each new module has exactly one named theorem
whose whole proof is sorry. This is a decomposition, not an axiom-free proof of linear
recovery: one upper hole closed and two lower holes added, net minus one before global
import-closure accounting. Neither of the first worker's proposed existence/uniqueness
helpers or nodes remains; they have been replaced by steps of the geometric argument.

## No longer needed

No baseline import is removed and no baseline module is pruned. The old proof dependency
`def-weil-pbc-torsor-associated-module` is now a statement dependency of the item and a
proof dependency of the two lower statements; its public import is still necessary.
The first worker's proposed existence and uniqueness nodes were removed from this
unlanded delivery; those removals are not counted as pruning the baseline library.

## Where the brief, the DAG or earlier work was wrong

The first worker removed the original detailed documentation, omitted proofs in words
for the new holes, searched only invented declaration names, kept new statements in
the item, and did not update the item's proof plan. The uniqueness node's proof text
incorrectly described existence and local extension. These faults are repaired.
The original existence/uniqueness split mostly divided clauses of the conclusion.
The final split follows the original proof's actual steps: recovery on the diagonal
of one object, followed by local naturality and extension to all etale objects.

Project search found `equivariantSections_diagonalEvaluation_surjective`, useful for
the diagonal step's uniqueness argument, but its module has no olean in the last
published green build on this machine or the server. The instruction to wait for
landed declarations to enter the green build precludes importing or copying it as a
compilation workaround. The final proof therefore uses the available associated-module
definitions and isolates diagonal recovery as a complete local obligation; it neither
restates nor adds a duplicate surjectivity theorem. No extra hypothesis is introduced.

The Stacks sources were read online because the cited TeX files are absent here:
[0DV5](https://stacks.math.columbia.edu/tag/0DV5),
[0DV6](https://stacks.math.columbia.edu/tag/0DV6),
[0A3R](https://stacks.math.columbia.edu/tag/0A3R),
[04TR](https://stacks.math.columbia.edu/tag/04TR), and
[04TS](https://stacks.math.columbia.edu/tag/04TS). These give finite locally constant
representation and descent context, rather than the exact arbitrary-module statements.
The elementary diagonal and open-fibre proofs in the new docstrings do not use finite
generation or primality hypotheses from that context.

## New nodes

`lem-weil-pbc-torsor-equivariant-module-recover-linear-diagonal` recovers the linear
map only from eta on the diagonal of the torsor object. It has no conclusion about
other etale objects, so it is a strictly local part of the original argument.
Its proof in words gives explicit extension on each translate, connected constancy,
conjugation of the linear component and diagonal uniqueness at a nonempty point.

`lem-weil-pbc-torsor-equivariant-module-pointwise-from-diagonal` assumes the supplied
linear map already has the uniform diagonal formula, and propagates it to arbitrary
etale objects. It constructs no linear map and asserts no uniqueness. Connectedness
is unnecessary for this step. Its proof identifies the two restrictions on each open
fibre, applies naturality, and evaluates their common graph value at the original point.

Both nodes have the item's chapter and unit, their own modules, exact signatures and
honest mathematical searches. No existing interface changes, hence no change records.

## Second reading by E2

1. Compared the item with the repository by diff. Verdict: only two plain proof imports
   and the proof body change. The existing signature is byte for byte unchanged: same
   coefficient ring, arbitrary representations, connectedness hypothesis and pointwise
   unique-existence conclusion. Visibility, public imports and documentation are restored.
   No other existing module or definition changes.
2. Compiled all three delivered modules in dependency order using lcompile.py, then
   checked all three theorems with explicit print-axioms commands in a scratch copy.
   Verdict: no errors or warnings; only the standard axioms and the two reported
   sorryAx dependencies. No sorry in a definition or partial proof, and no axiom,
   unsafe, opaque, implemented_by or extern declaration.
3. Checked both lower statements against their full proofs in words. For diagonal
   recovery, equivariant extension prescribes rho(g)n on the g-th copy; the action
   identity proves equivariance, connectedness gives constancy, and nonemptiness gives
   uniqueness. For propagation, the open fibre through x is etale over V and maps to
   c.P; restrictions agree on its graph and hence on all translates. Naturality along
   both maps identifies eta-values, and the assumed diagonal formula gives f(s(x)).
   Tested trivial group, zero modules, ell=0, ell=1, empty etale objects, disconnected
   torsors for propagation, and an attempted empty torsor in recovery (excluded by
   ConnectedSpace). Verdict: true, strictly narrower steps, with no concealed finiteness
   or prime assumptions. Lean Finder, Loogle, Mathlib grep and project grep were done
   with mathematical wording; no exact existing statement was found. Loogle's
   LocallyConstant.apply_eq_of_isPreconnected is an elementary component, not a proof
   of either geometric statement. LeanSearch failed with an unavailable-service error;
   this is recorded honestly, not as a successful no-match search.
4. Read dag/units/sk-thm-p1.json and the original proof plan. Verdict: no realized unit
   statement or step is bypassed; the split realizes the existing diagonal and local
   extension argument below the unit level. The public associated-module import remains
   necessary for signatures; each new plain import is used in the proof. No baseline
   module is pruned, and all old direct proof dependencies are accounted for above.
5. Matched the item's changed node and both new nodes with the Lean files. Verdict:
   proof_deps is exactly the union of the steps' uses; the item combines local recovery
   and propagation and restricts competing maps to the diagonal. The new nodes have
   their exact signatures, source context, creation records, searches and complete
   arguments. Existing statement and stmt_deps fields are untouched.

Changes made: restored original documentation; replaced the clause split with geometric
local recovery and propagation statements in separate modules; supplied complete proofs
in words and genuine searches; updated the original node's actual proof dependencies;
removed the obsolete proposed nodes; corrected hole accounting to report a decomposition.
