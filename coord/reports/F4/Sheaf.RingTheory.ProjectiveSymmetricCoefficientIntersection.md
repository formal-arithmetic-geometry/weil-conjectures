## What changed

Completed `Algebra.projective_symmetric_coefficient_intersection` in the assigned
module, preserving its signature and its four public imports. Repaired the earlier
attempt's basis calculation by explicitly rewriting `LinearMap.comp_apply` and
`Pi.basisFun_apply`. The complete direct proof splits q, constructs a section of α,
lifts its variable images through the proved surjective coefficient reduction,
and uses the resulting substitution endomorphism β to prove both ideal inclusions.
Updated the theorem's proof description and its existing DAG node to this route.
Only Mathlib is used. The item is below the unit's realized statements and steps;
none of the unit's route is bypassed.

## Proved and sorry left

Closed one original hole:
`Algebra.projective_symmetric_coefficient_intersection`
(node `lem-weil-pbc-projective-symmetric-coefficient-intersection`).
No sorry remains in the delivered module. No holes or new declarations were added.
This is a complete proof, not a decomposition into unproved statements.
The unused earlier `projective_symmetric_kernel_local_regular` draft was moved to
scratchpad and is excluded from delivery. All witness choices in the delivered
proof use already-proved Mathlib theorems. The same proof includes I = P and m = 0.

## No longer needed

Removed proof imports:
- `Mathlib.RingTheory.Polynomial.Basic`
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`
- `Mathlib.Algebra.Module.LocalizedModule.Exact`
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`
- `Sheaf.RingTheory.SymmetricAlgebraBaseChange`
- `Sheaf.RingTheory.ConormalIntersectionRegularQuotient`

The direct proof uses declarations already available through the four public
statement imports. No additional proof imports remain. The second reader also
removed the redundant attempted imports `Mathlib.LinearAlgebra.Pi` and
`Mathlib.RingTheory.Ideal.Maps`.
All seven original proof dependency nodes are unnecessary for this item:
- `lem-weil-pbc-finite-projective-standard-free-cover`
- `lem-weil-pbc-symmetric-algebra-base-change`
- `lem-weil-pbc-symmetric-algebra-free-module-polynomial`
- `def-weil-pbc-regular-sequence`
- `lem-weil-pbc-conormal-intersection-regular-quotient`
- `lem-weil-pbc-localization-module-exact`
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`

Their corresponding modules (where recorded) need not be reached through this
item: `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`,
`Sheaf.RingTheory.SymmetricAlgebraBaseChange`,
`Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`,
`Mathlib.RingTheory.Regular.RegularSequence`,
`Sheaf.RingTheory.ConormalIntersectionRegularQuotient`,
`Mathlib.Algebra.Module.LocalizedModule.Exact`, and
`Mathlib.RingTheory.Spectrum.Prime.Topology`.
This does not assert they are unused by other targets or modules.
The abandoned new module `Sheaf.RingTheory.ProjectiveSymmetricKernelLocalRegular`
is also unnecessary and is not delivered.

## Where the brief, the DAG or earlier work was wrong

The local regular sequence route is unnecessary: splitting and substitution prove
the intersection directly. The earlier direct attempt did not compile because
`simp only` left the linear-map composition on the right hand side of the basis
calculation; explicit rewriting closes it. No statement or definition was changed.
The proposed local regular helper is not required. No new nodes or forced
adaptations are delivered.


## Second reading by F4

1. Compared the sole delivered module and existing node against the repository.
   Verdict: the existing theorem signature is byte for byte unchanged, including
   all hypotheses, its conclusion, visibility, and universes. No definitions or
   declarations were added or removed. The four public statement imports remain.
   Changes are confined to the proof, its explanatory docstring, proof imports,
   and the node's proof, proof_deps, and proof_origin. No change record is needed.
2. Compiled the module with lcompile.py without errors or warnings. A scratch copy
   with `#print axioms Algebra.projective_symmetric_coefficient_intersection`
   reports exactly propext, Classical.choice, and Quot.sound. Inspected the proof
   from the projective splitting through both ideal inclusions: every inference
   proves the unchanged statement. There is no sorry, forbidden declaration, or
   hollow definition. The section and polynomial lifts use proved Mathlib
   theorems; no witness is selected from an unproved existence statement.
3. No split-off statements or new nodes are delivered, so there are no remaining
   statements to test or duplicate-check. Checked the original theorem's edge
   cases: if I = P, H = J = Q; if m = 0, the section and generator extensionality
   arguments still apply. Neither case needs a nonzero-ring assumption.
4. Reviewed the proof from the target downward, read the old dependency modules,
   and searched the upstream library and Mathlib for intersection, kernel, and
   ideal-product results. The available regular-quotient and pure-ideal lemmas
   require extra facts and give no shorter route here. The direct substitution
   proof avoids all seven old proof dependencies, each listed above. Checked
   dag/units/sk-thm-p1.json: neither this item nor the pruned dependency nodes
   realizes a unit statement or step; the realized route is retained. Found two
   redundant proof imports: removing both together still compiles and gives the
   same permitted axiom list. The public imports provide the statement's notions.
5. Compared the node with the Lean proof. Verdict: all four steps describe the
   actual splitting, substitution, coefficient expansion, and ideal inclusions;
   proof_deps is correctly empty and proof_origin records the direct agent proof.
   The node's statement, statement dependencies, and Lean signature are unchanged.

Second-reading changes: removed the redundant proof imports
`Mathlib.LinearAlgebra.Pi` and `Mathlib.RingTheory.Ideal.Maps`; corrected the report's
import description and added this review. The proof itself needed no repair.
