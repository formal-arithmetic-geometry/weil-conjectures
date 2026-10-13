## What changed

Proved `AlgebraicGeometry.koszulCechCocone_stage_lifting` in
`Sheaf.AlgebraicGeometry.KoszulCechStageLifting` with its signature unchanged.
Added two fully proved private helpers: `finite_affine_denominators` clears a finite
family of affine localization denominators at one positive exponent;
`koszul_basis_values` constructs a homogeneous Hom cochain with prescribed ordered
exterior-basis values. The main proof applies the existing cocone formula and cancels
the invertible denominator and sign. Added the proof-only import
`Mathlib.LinearAlgebra.ExteriorPower.Basis`. The second reading removed the
redundant added import `Mathlib.Algebra.Module.LocalizedModule.Away`. Updated the existing DAG node's proof
and proof_origin to describe the Lean argument; its proof_deps are unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.koszulCechCocone_stage_lifting`
(node `lem-sc-koszul-cech-stage-lifting`), the only original hole.
No sorry remains in the item's module. No holes added or split off.
Both private helpers are proved. This proof uses the existing specified-object and
cocone verification theorems in `KoszulCechComparisonConstruction`, which remain
separate work items; it does not claim to close their holes.

Validation: the module compiles through lcompile.py. The construction handles r=0
via the empty finite index type and zero basis assignments, and zero/nilpotent
products through localization and the regular scalar action on the principal open.
The complex can be unbounded; no cycle hypothesis is used.

## No longer needed

Removed the redundant proof-only import
`Mathlib.Algebra.Module.LocalizedModule.Away`, added by the first worker; its
localization declarations are already available through the original import.
No original dependency import, node, or module is pruned. All three planned
dependency nodes remain needed:
`def-sc-koszul-cech-comparison-construction`, `def-sc-koszul-open-system`, and
`def-sc-principal-open-alternating-total`. No node or module is bypassed, and no unit
statement or realized proof step is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had two compiling private helpers but no proof of the
item. Its finite-denominator helper unnecessarily put the finite index type in the
ring's universe. Changed that private helper to use a small index type independently of the ring
universe, so it applies to finite subsets of Fin r. Completed the main proof from those helpers.
No mathematical error in the statement or DAG plan was found. No existing public
signature, definition, or visibility changed; no forced adaptations are needed.


## Second reading by J4

1. **Public interface: PASS.** Read the complete diff against the repository's module.
   The existing theorem signature and docstring are byte-for-byte unchanged. The
   only additions are two private, fully proved helpers and the main proof, together
   with a proof-only exterior-basis import. No definition or public visibility changes,
   no change records, and no forced adaptations.
2. **Proof and axioms: PASS.** Compiled the delivered file with lcompile.py without
   errors or warnings. A scratch copy with explicit `#print axioms` for both private
   helpers and `AlgebraicGeometry.koszulCechCocone_stage_lifting` confirms that the
   helpers use only `propext`, `Classical.choice`, and `Quot.sound`; the main theorem
   additionally uses `sorryAx` from the existing open construction dependencies.
   No sorry, axiom, unsafe, opaque, extern, or implemented_by occurs in this module.
   The proof chooses numerator witnesses only from a proved localization theorem;
   it adds no data definition or arbitrary object chosen from an unproved existence.
3. **Split statements and edge cases: PASS.** No statements are split off and no
   holes are added. Read both private helpers: the first takes the finite supremum
   of individual denominator powers, then multiplies numerators to reach e+1; the
   second uses `Basis.constr` on every exterior power and transports precisely the
   degree equality, with zero in positive source degrees. For r=0 the subset index
   is empty and the finite supremum is zero. For r=1 there is only the source degree
   zero assignment. Nilpotent products give empty principal opens, where regular
   scalar cancellation is valid on the zero section module. Arbitrary integer n
   and unbounded coefficient complexes require no extra assumptions. Searched
   the project with `stage_lifting`, `constr_basis`, and `IsLocalizedModule.Away.surj`,
   read the nearby HigherDirectImageSectionDenominators proof, and ran msearch grep
   for "IsLocalizedModule finite denominators" (zero hits). The existing higher
   direct-image statement requires a different cohomology setup and is not a
   shorter substitute for this affine degreewise argument.
4. **Route and imports: PASS after cleanup.** Read Stacks Tags
   [08D0](https://stacks.math.columbia.edu/tag/08D0) (localization and ordered wedges)
   and [08D1](https://stacks.math.columbia.edu/tag/08D1) (total Hom comparison).
   The proof follows finite affine denominators and exterior-basis assignments,
   then uses the *specified* cocone formula, rather than claiming differential
   compatibility anew. Removing both added imports in a scratch copy loses
   `Module.Basis.exteriorPower` and `exteriorPower.basis_apply`; restoring just
   ExteriorPower.Basis compiles cleanly with the axiom checks. Thus Away was
   redundant and has been removed. No old proof dependency is dropped: the proof
   uses the total coordinates, Koszul tail and basis, object transports and cocone
   formula. Read `dag/units/sk-thm-picard-duality.json`: this item is below the unit
   realization, and its `realized` record and route remain untouched.
5. **DAG agreement: PASS.** Compared the existing node JSON with the repository.
   Only `proof` and `proof_origin` change. Its three proof steps match denominator
   clearing, basis construction, and cancellation in Lean; the union of their uses
   is exactly the unchanged three-element `proof_deps`. The node's statement and
   verbatim Lean signature match the theorem. No new nodes require review.

Changed on second reading: removed the redundant proof-only Away import and updated
this report to distinguish that cleanup from pruning original dependency modules.
The mathematical proof was retained unchanged. One original hole is closed, zero
holes are added, and no dependency module is pruned; the inherited construction
holes remain open, so this is not a claim of an axiom-free import closure.
