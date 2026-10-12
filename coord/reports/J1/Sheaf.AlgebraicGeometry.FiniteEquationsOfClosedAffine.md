## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_finite_equations_of_finitely_generated_zeroLocus`
using the finite generating-set witness for `Ideal.FG`, `Scheme.zeroLocus_span`, and
`Scheme.mem_zeroLocus_iff`. Both existing signatures and all definitions are unchanged.
Removed the redundant direct public import `Mathlib.AlgebraicGeometry.AffineScheme`:
`FiberDegree` already publicly imports `Mathlib.AlgebraicGeometry.Limits`, which publicly
imports `AffineScheme`. Corrected the proved node's proof and proof_origin to match Lean.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Hom.exists_finite_equations_of_finitely_generated_zeroLocus`
(node `lem-weil-pbc-finite-equations-of-finitely-generated-zeroLocus`).

Remaining unchanged: `AlgebraicGeometry.Scheme.Hom.exists_finitely_generated_zeroLocus_ideal_degree_sublevel_inter_affine`
(node `lem-weil-pbc-finite-equations-of-isClosed-inter-affine`).

One of two original holes closed; zero holes added; zero statements split off.
The remaining hole requires finite-presentation descent, not the elementary finite-generator
argument, and is not represented as proved by this delivery.

## No longer needed

Removed direct import `Mathlib.AlgebraicGeometry.AffineScheme` (still reached transitively).
No DAG dependencies were pruned: both old proof_deps lists are empty. No module leaves the
import closure through this redundant import removal.

## Where the brief, the DAG or earlier work was wrong

The proved node's old proof incorrectly included representing an arbitrary closed locus and
descending through a directed union of ideals. Its theorem already assumes `I.FG`, so only
unpacking that hypothesis and applying the two Mathlib zero-locus lemmas is necessary.
The first worker had not updated that node. Its Lean proof itself was correct.

## Second reading by J1

1. Compared the entire delivered module against the repository with diff. Both theorem
signatures, their universes, hypotheses, conclusions, docstrings, and visibility are byte
for byte unchanged. There are no definitions changed. The public-import removal has change record
`coord/changes/FiniteEquationsOfClosedAffine-import.md`. The only Lean edits are
closing the second proof, removing the redundant import, and a blank line.
2. Compiled the module locally with lcompile.py before and after import pruning, without
errors or warnings. A scratch copy with #print axioms for both declarations shows the
proved finite-equations theorem uses only propext, Classical.choice, and Quot.sound; the unchanged first
theorem uses sorryAx. There is exactly one sorry, in that named existing theorem, and no
axiom, unsafe, opaque, implemented_by, extern, or holed data construction.
3. No statements were split off and no new nodes were added. Read Mathlib Scheme.lean's
zeroLocus_span and mem_zeroLocus_iff: they give exactly the two rewrites used. The finite
set is obtained from the proved hypothesis I.FG, not from an unproved existence theorem.
The empty generating set (zero ideal), unit ideal, empty W, and empty scheme cause no
exceptions: the same universal zero-locus equivalence applies, and the W implication is
vacuous when needed. The existing first hole retains its source and docstring proof.
4. The shortest direct route is used: obtain the generating set, rewrite the span, and
simplify membership. Read Stacks Tag 07RZ at https://stacks.math.columbia.edu/tag/07RZ,
especially its finite-generators conclusion, and dag/units/sk-thm-p1.json including realized.
This local algebraic step bypasses none of the realized unit steps. FiberDegree is needed
for finrankΓ and IsFiniteLocallyFreeOfDegree; QuasiFiniteMorphism is needed for IsQuasiFinite.
AffineScheme is supplied by FiberDegree through Limits and its redundant direct import
was removed. No old proof dependency is omitted from No longer needed.
5. Read both sandbox node files and compared the unchanged first node with the repository.
Its proof remains a plan for the existing hole. Corrected the second node's proof to the
actual elementary Ideal.FG/Mathlib argument; proof_deps remains empty and proof_origin
now records the direct argument. Statements, sources, unit, and all other node fields stay
unchanged. There are no new-node field obligations.

Second reading changed: corrected the proved node's stale proof and proof_origin, removed
the redundant AffineScheme import, and removed one extra blank line. No proof repair was
needed and no additional hole was introduced.

The dry run required a change record for public-import pruning. Added
`coord/changes/FiniteEquationsOfClosedAffine-import.md`, with all 183 transitive users
from tools/downstream.py and the retained public-import path proving no interface effect.
