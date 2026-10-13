## What changed

Replaced the target's sorry with a reduction to finite freeness of stalks and reflection
of isomorphisms between finite free modules along a local ring homomorphism. Added the
proof-only imports `Sheaf.AlgebraicGeometry.StalkFiniteFree` and
`Sheaf.AlgebraicGeometry.LocalFreeBaseChangeReflectsIso`. Existing signatures and public
imports are unchanged. No definitions or data constructions were added.

## Proved and sorry left

Closed the body hole of
`AlgebraicGeometry.Scheme.Modules.isIso_moduleStalkMap_of_isIso_extendScalars` by reduction.
Added two named holes:
- `AlgebraicGeometry.Scheme.Modules.stalk_isFiniteFree_of_isFiniteLocallyFree`, node
  `lem-sc-stalk-finite-free-of-finite-locally-free`;
- `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_extendScalars_of_finite_free`, node
  `lem-sc-local-free-base-change-reflects-iso`.

This is a decomposition, not a sorry-free proof: one hole closed, two added, net -1.
The target and both helpers still depend on sorryAx, as well as the permitted standard
axioms. No other holes were added or closed.

## No longer needed

No modules pruned. The old proof dependencies `def-sc-finite-locally-free-sheaf` and
`def-pc-module-stalk-functor` are no longer direct target proof dependencies: they are
statement dependencies and remain needed by the stalk helper. Their imports remain
necessary for the unchanged target signature. All four original public imports stay.

## Where the brief, the DAG or earlier work was wrong

The first worker's target node erroneously recorded the local-ring helper's signature
instead of the target signature. The new nodes inherited unrelated review stamps and
had placeholder statements and generic proof text; their source and search records
needed correction. The helper docstrings tagged the parent rather than their own nodes.
The reduction had four avoidable letI style warnings; ordinary have bindings suffice.

## New nodes

`lem-sc-stalk-finite-free-of-finite-locally-free` isolates the sheaf/germ calculation
from Stacks 01C6. `lem-sc-local-free-base-change-reflects-iso` isolates the finite matrix
argument of Stacks 00O0 adapted to local maps. Both are strictly simpler ingredients,
and neither just renames the target. No change records are needed.

## Second reading by P1

1. Compared the target file to the repository: the existing signature is byte-for-byte
   identical. No definition or public interface changed. Verdict: pass.
2. Compiled all three files with lcompile.py after fixing the letI warnings. All holes
   are exactly the two reported public named theorems. No axiom, unsafe, opaque, extern,
   implemented_by, or hollow definition occurs. Explicit axiom checks list only the
   permitted axioms and sorryAx from those reported holes. Verdict: pass as decomposition.
3. Checked the two helper statements against Stacks 01C6 and 00O0 and their definitions.
   Zero ranks and empty schemes are covered; unequal ranks contradict the extended
   isomorphism over the residue field. Locality reflects determinant units, so flatness
   is unnecessary. Each new docstring gives a complete proof in words. Independent
   leanfinder, loogle, grep and local library searches found no exact public equivalent;
   leansearch returned Internal Server Error and is recorded as unavailable. The private
   coordinate equivalence in FiniteLocallyFreeStalkFinrank confirms the stalk argument
   but is not accessible here; closing this calculation requires more than a quick patch.
   PicardBaseChangeStalkFiniteBases is a specialized sorry, not this statement. Verdict: pass.
4. Read from the target downward. The matrix and stalk split is a real two-part reduction;
   faithfully-flat reflection does not apply because flatness is absent. Tested removal
   of FiniteDimensional.Defs: Module.Finite became unknown, so restored it. All helper
   imports serve their signatures; new target imports are proof-only. No original module
   can be pruned. The unit sk-prop-av-cube has empty realized lists and this lower-level
   reduction leaves its route untouched. Verdict: pass.
5. Restored all existing node metadata except the allowed proof fields; the target's
   recorded signature again matches Lean. New nodes have self-contained statements,
   exact Lean signatures, their own blueprint tags, corrected sources, genuine search
   results, no inherited review stamps, and proof_deps equal to the proof-step uses.
   Verdict: pass.

Second reading changed instance bindings, helper documentation and tags, node statements,
source/search/proof metadata, and report accounting. No additional hole was closed.
