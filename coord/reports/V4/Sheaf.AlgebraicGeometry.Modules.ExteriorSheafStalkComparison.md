## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_stalk_comparison` with its
original signature and visibility. Added the proved auxiliary module
`Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafStalkWedge`, which establishes
independence of representatives and the alternating wedge map on stalks.
The original module constructs the reverse comparison by an abelian stalk colimit,
checks both inverse identities on wedge generators, and transports the resulting
linear equivalence through sheafification. Added proof-only imports of that helper,
`Mathlib.Topology.Sheaves.Sheafify`, and `Sheaf.Topology.PresheafModuleStalkFunctor`.
Existing public imports are unchanged. Updated the comparison node's proof route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_stalk_comparison`
(node `lem-sc-exterior-sheaf-stalk-comparison`).
Also proved `AlgebraicGeometry.Scheme.Modules.exteriorPresheaf_stalk_wedge`
(node `lem-sc-exterior-presheaf-stalk-wedge`). No holes added or left in either
module. All private helpers are proved. This is a proof, not a decomposition.
The constructions include degree zero, with the empty tuple represented over the
top open, and require no nontrivial-ring, local-freeness, or exactness hypothesis.

## No longer needed

No imports removed and no planned dependency nodes or modules pruned. The proof
keeps both original steps: the presheaf exterior comparison and sheafification.
The exterior-power universal property and pure-wedge spanning suffice; it does
not directly manipulate the generators and relations of `exteriorPower.presentation`.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement found. The cited blueprint and Stacks source files are not
present in this machine’s read-only literature checkout; the proof follows the
complete argument supplied in the original node and docstring, with the Mathlib
APIs checked against their local sources. The original plan did not provide a separate Lean
interface for the descent of wedge germs. That step is now a proved auxiliary
module. The unit's `realized` fields impose no additional nodes here, and its
Riemann--Roch route is unchanged. No definition, existing statement, or public
interface was changed; there are no forced adaptations.

## New nodes

`lem-sc-exterior-presheaf-stalk-wedge` records the alternating map from module
stalks to the sectionwise exterior presheaf stalk, with the wedge-germ formula.
Its proof uses common neighborhoods and independence of representatives, followed
by coordinate additivity, the scalar germ identity, and alternation. The theorem
is fully proved. No change records are needed.

## Second reading by V4

1. **Interfaces: pass.** Diffed the existing module against the repository and
   independently compared its target signature byte for byte. The existing
   statement, docstring, visibility, and public imports are unchanged. The new
   auxiliary module is reported and has its own node; no change record is needed.

2. **Proof: pass.** Read both
   modules in full. There is no `sorry`, forbidden declaration, or hollow
   definition in either. The representative choice in the auxiliary is based on
   a fully proved existence theorem, and its independence is proved by `uniq`.
   Both inverse identities use wedge spanning and the correct germ scalar law.
   The sheafification unit is the actual module-sheafification unit, and its
   underlying stalk map is Mathlib's sheafification comparison. Compilation and
   axiom results are recorded below.

3. **New statement: pass.** The proved `exteriorPresheaf_stalk_wedge` isolates
   descent and alternation, strictly below the comparison equivalence. Its
   docstring supplies the complete argument and its node has the required fields.
   Reviewed empty tuples, degree one, repeated entries, and zero stalk rings:
   common neighborhoods and restriction preserve the stated formula in each case.
   Independent leanfinder search for alternating maps descending to germs, grep
   search for alternating/stalk combinations, and rg over both library roots
   found no existing equivalent theorem. There are no new unproved split statements.

4. **Route and pruning: pass.** The universal property and pure-wedge span give
   the presheaf comparison; Mathlib then supplies sheafification on stalks.
   The imports supply the exterior definitions, module-stalk scalar instance and
   germ API, wedge descent, sheafification isomorphism, and stalk-map API.
   No old proof dependency is absent from the new proof. The unit's empty
   `realized` records impose no additional node, and its Riemann--Roch route stays.

5. **DAG agreement: pass.** The existing node changes only `proof` and
   `proof_deps`. All previous dependencies remain and the proved wedge node is
   added. Both proof routes and their agent/source origins agree with the code;
   the auxiliary Lean signature is byte-identical to its node's `lean.statement`.

No mathematical or interface repair was necessary. Added this independent
second-reading record. Final validation: `lcompile.py --all` compiled both delivered modules without
errors or warnings. Scratch copies with `#print axioms` compiled and reported
exactly `propext`, `Classical.choice`, and `Quot.sound` for both
`exteriorPresheaf_stalk_wedge` and `exteriorSheaf_stalk_comparison`; no `sorryAx`.
Initial timeouts occurred during severe shared-machine load; the launcher then
introduced compile slots, and the unchanged proofs passed. No definition or proof
was split to evade the per-file limit.
