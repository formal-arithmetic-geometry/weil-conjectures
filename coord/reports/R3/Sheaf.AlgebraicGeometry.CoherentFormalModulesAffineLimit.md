## What changed

Replaced the hole in `AlgebraicGeometry.coherentFormalModules_affine_limit` by a compiling
proof. It constructs the functor on morphisms from the ordinary limit functor, proves
completion-linearity by coordinate residues, checks functor laws, lifts to finite modules,
and transports the limiting cones. Its statement and visibility are unchanged.

Second reading removed the finite-limit module's public import of the completed-scalar
module: only the Mathlib limits, restriction-of-scalars and completion types are needed
in its signature. Redundant direct limits imports were removed from both algebraic
modules, since ChangeOfRings publicly imports Limits. The scalar theorem's proof
docstring now describes its actual endomorphism/limit construction.

Added three modules and nodes separating the finite-level affine-sections bridge, the
completed scalar action, and the algebraic finite-generation/projection-kernel argument.
`ModuleCat.adicTower_completedScalarLimit` is proved without any sorry dependency: scalar
endomorphisms factor through the quotients and are lifted through the limit universal
property. The completed module is a real construction on the existing limit, not data
chosen from an unproved mere-existence theorem.

The source read was Stacks Project Tag 087W (online), including its generator-lifting,
Nakayama, kernel-correction and Mittag-Leffler argument. The local referenced coherent.tex
was absent. All four delivered modules compile with lcompile.py --all.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.coherentFormalModules_affine_limit`
(node `lem-weil-pbc-coherent-formal-modules-affine-limit`). This is a decomposition into
two remaining holes, not a completed sorry-free proof of the original mathematics.

Also proved `ModuleCat.adicTower_completedScalarLimit`
(node `lem-weil-pbc-adic-tower-completed-scalar-limit`) with no new holes.

Two holes added, each in its own module, exactly `:= by sorry`:
- `AlgebraicGeometry.coherentFormalModule_affine_sections_adic`
  (`lem-weil-pbc-coherent-formal-module-affine-sections-adic`): finite-level sheaf bridge.
- `ModuleCat.adicTower_finiteLimit`
  (`lem-weil-pbc-adic-tower-finite-limit`): one given algebraic tower and one given limit
  comparison; finite generation and projection kernels, no functor or morphism construction.

No sorry remains in the assigned module. No existing definition or signature changed.

## No longer needed

Removed direct proof imports from the assigned module:
- `Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Sheaf.RingTheory.NakayamaNilpotent`
- `Mathlib.RingTheory.AdicCompletion.Completeness`

These are relocated to the two remaining proof tasks, not globally pruned: all original
mathematical ingredients remain needed transitively. No entire module or node is claimed
pruned. The unit's realized statement and steps are unchanged.

Every former direct proof dependency of the assigned node is now routed through the
three new nodes, rather than directly invoked in its Lean proof:
- `pqf-def-locnoeth`
- `def-weil-affine-spectrum`
- `def-weil-pbc-coherent-formal-module`
- `pqf-lem-coherent-ft-locnoeth`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
- `def-weil-pbc-adic-completion`
- `lem-weil-pbc-tower-limit-exact-surjective-kernels`
- `lem-weil-pbc-nakayama-nilpotent`
- `def-weil-finitely-generated-module`
- `lem-weil-pbc-module-completion-complete`
- `def-weil-pbc-noetherian-ring`

Definitions still occur in signatures; the mathematical proof ingredients remain in
the two open tasks' plans. No global pruning or positive net hole reduction is claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The planned imports supply lower-level ingredients,
not the affine-sections transport or algebraic tower presentation argument as ready-to-apply
statements. Those two gaps are now precisely stated and independently provable.

Checked edge cases of the new statements: I=0 gives a constant-isomorphism tower and its
ordinary finite module; I=top forces every term and its limit to zero. The scalar theorem
requires neither Noetherianity, finiteness nor surjective transitions, because its action
is defined coordinatewise. The finite theorem retains Noetherianity for finite generation
of I and the completion quotient formula; all indices mean exponent n+1.

The whole-blueprint searches for adic tower, coherent formal and completed scalar found
no duplicate of the three new statements. The existing adic-tower reconstruction theorem
concerns completeness and quotients of an already specified A-module, and does not provide
the completed scalar construction or finite-generation assertion needed here.

## New nodes

`lem-weil-pbc-coherent-formal-module-affine-sections-adic`: the original first step only,
with finite-level sections and successor transitions, and no inverse limit.

`lem-weil-pbc-adic-tower-completed-scalar-limit`: the completed scalar construction on
an arbitrary annihilated tower. Fully proved; no finite-generation assertion.

`lem-weil-pbc-adic-tower-finite-limit`: the original generator/Nakayama/Mittag-Leffler
and kernel-calculation steps, for one algebraic tower. This is strictly separate from
the affine sheaf bridge and the functor construction. No change records are needed.


## Second reading by R3

1. Compared every delivered module with the repository. Only the assigned module
   previously exists. Its complete theorem signature is byte-for-byte identical;
   its public imports and visibility are unchanged. The three added modules introduce
   new declarations, not replacements of existing definitions. No change record is needed.
2. Compiled all four modules in import order using lcompile.py. Printed axioms on
   scratch copies for all four public declarations: completedScalarLimit uses only
   propext, Classical.choice and Quot.sound; the other three additionally use sorryAx.
   Exactly the two reported named theorems contain sorry. There are no hollow definitions,
   forbidden declarations or unproved arbitrary data choices. The scalar theorem really
   constructs the module on the existing limit, and its residue equation determines
   the action relative to the comparison. The upper proof transports ordinary limit
   maps, proves completion-linearity by joint injectivity, and checks both functor laws.
3. Checked the two open statements against the formal-system definition, their cited
   lower declarations and Stacks 087W. The sheaf statement is solely a finite-level
   sections bridge. The algebra statement assumes a given module and limit comparison
   and proves finite generation and kernels; it neither constructs the action nor
   the functor. Both are true, needed, and strict parts of the original argument.
   For I=0 transitions are isomorphisms and the conclusion is a finite constant limit;
   for I=top annihilation forces zero terms and a zero limit. Also tested the zero
   system and the standard A/I^(n+1) system: both have the expected projection kernels.
   Repeated LeanFinder, Loogle and grep with different queries and read the nearest
   library matches, including AdicTowerReconstruction and AdicLimitFiniteModules.
   Neither supplies arbitrary completed-module finiteness. Existing affine and
   completion tools are ingredients, not duplicate statements. Neither open theorem
   can be closed by a short application of an existing declaration.
4. Read the top-down reduction and the scalar proof in full. The decomposition keeps
   the generator/Nakayama/surjective-kernel route of Stacks 087W. Checked sk-thm-p1's
   realized statement and all steps: none is bypassed or edited. The report now names
   every former direct proof dependency, distinguishing relocation from pruning.
   Removed the unnecessary public dependency on the new scalar theorem from the
   finite-limit module, and redundant direct Limits imports from the algebraic modules.
5. Checked all node signatures against Lean and each proof_deps against the union of
   proof-step uses. The assigned node changes only proof, proof_deps and proof_origin.
   All new nodes have source, natural-language proof, provenance, searches, created,
   blueprint, chapter/unit and verbatim Lean signature records. The scalar node's
   endomorphism construction matches the actual proof. Independent searches are added
   to the two open nodes. Verdict: deliverable decomposition, with two holes left and
   no claim of a completed proof or positive net hole reduction.

Second reading changed imports, the scalar proof docstring, independent-search records,
and report completeness; no theorem statement, definition or proof body was changed.
