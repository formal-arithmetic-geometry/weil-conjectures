## What changed

Proved `AlgebraicGeometry.Scheme.Modules.tensorPullback_isFiniteType` with its signature
unchanged in `Sheaf.AlgebraicGeometry.ModulePullbackFiniteType`. The proof first constructs
the same-rank epimorphism on each inverse-image open using over-site equivalences,
Mathlib pullback and free-sheaf isomorphisms, and uniqueness of the tensor-pullback
adjoint. It then constructs finite local generators data on the inverse-image cover.
The DAG proof now records these actual operations. All new imports are proof-only:
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`, `Mathlib.Data.Fintype.EquivFin`,
and `WeilConjectures.Mathlib.Topology.Category.TopCat.Opens` (the finality instance).

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.Modules.tensorPullback_isFiniteType`
(node `lem-weil-pbc-module-pullback-finite-type`). No sorries remain in the delivered
module and no holes or declarations were added. This is a proof, not a decomposition.
The earlier attempt's two auxiliary holes were eliminated by writing their proofs inline.
External dependencies retain their existing proof status.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`: categorical epimorphisms
  suffice throughout; the explicit local-lifting criterion is unnecessary. Its node
  `lem-weil-pbc-ringed-space-module-exactness-local-lifting` is removed from proof_deps.
- `Sheaf.AlgebraicGeometry.Coherent`: the finite-type predicate and its local generators
  are already public in Mathlib Generators. The definition node `pqf-def-coherent` remains
  as a mathematical reference and statement dependency; no coherent-module theorem is used.
- `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`: Mathlib's structure-sheaf
  pullback isomorphism suffices after comparing left adjoints. The mathematical node
  `lem-weil-pbc-module-pullback-structure-sheaf` remains, via its recorded Mathlib match.

Removed the earlier sandbox's auxiliary modules `ModulePullbackFiniteTypeLocal` and
`ModulePullbackFiniteTypeEpi` and their proposed `-local` and `-epi` nodes. No other
original proof-plan nodes are bypassed. No unit statement or realized step is changed.
These removals describe this proof's requirements; other targets may still need the modules.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox compiled a decomposition but its new nodes copied the parent statement,
missed recorded Lean signatures and detailed proof steps, and included a placeholder second
reading. Those files and that placeholder were removed. The new proof needs no auxiliary
public statements or new nodes. The original plan's conversion between categorical epi
and explicit local lifting is unnecessary because Mathlib's finite-type definition directly
uses generating epimorphisms. Empty inverse-image opens, empty schemes and rank zero are
covered by the same equivalences, coproducts and covering-sieve proof.

## Second reading by K1

1. **Interface: pass.** Compared the sole delivered module with the repository using
   `diff -u`, then compared the complete theorem signature as raw text: byte-identical.
   The universes, arbitrary schemes X and Y, morphism f, module G and finite-type
   assumption are unchanged. Both conclusions remain: finite type and, on every V,
   preservation of an epi from the free module with exactly the same rank n on f⁻¹V.
   No definition, declaration visibility, public import, or target was changed.
2. **Proof: pass.** Independently compiled the delivered file with `lcompile.py`:
   no errors or warnings (43.5 s). Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.Modules.tensorPullback_isFiniteType`: exactly `propext`,
   `Classical.choice`, `Quot.sound`, without `sorryAx` (38.5 s). Scanned the delivered
   source: no sorry, axiom, unsafe, opaque, implemented_by or extern; no new definition.
   The adjunction chosen from Nonempty is used only to prove a proposition and compare
   already constructed functors, not to define arbitrary data from unproved existence.
3. **Split statements: pass, none.** No new declaration, module or node is delivered,
   and no lower holes replace the closed hole. Read Mathlib Generators.lean (finite
   local generators and finite index instances) and PullbackFree.lean (unit pullback
   and free sheaves), and the upstream finality instance in TopCat/Opens.lean. The
   empty scheme, empty inverse-image open, and n = 0 need no nonemptiness hypothesis:
   free sheaves allow empty index types; coversTop quantifies only over actual points.
4. **Route and pruning: pass.** Read the proof of Stacks 01B6 and its restriction
   argument 01B3 at https://stacks.math.columbia.edu/tag/01B6 and
   https://stacks.math.columbia.edu/tag/01B3 (local literature copy absent).
   The isomorphism k uses restriction-pullback, composition, and the commuting square;
   e transports it to the tensor formula by uniqueness of left adjoints. F preserves
   colimits and epis, and its unit comparison gives mapFreeIso. The finite index
   equivalence supplies the same rank; intersection with an arbitrary W proves the
   covering sieve condition. Re-searched Mathlib and lean/ by finite-type/pullback
   concepts and ran Loogle `SheafOfModules.IsFiniteType`: its four results contain
   no finite-type pullback theorem. GeneratingSections.map only handles global
   generators, so it does not remove the restriction/cover argument. Both public
   imports are required by the signature; the three new imports supply free-unit
   pullback, equivFin, and finality respectively. The No longer needed list includes
   all three removed imports and the only removed old proof dependency, local lifting.
   Read dag/units/sk-thm-p1.json: this technical node is not a realized unit step;
   none of its realized statements or steps is bypassed.
5. **DAG: pass.** Compared both node files: only proof, proof_deps and proof_origin
   changed. The four recorded steps match hlocal's over-site comparison and free epi,
   finite reindexing, and inverse-image cover assembly. Their uses have exactly the
   recorded union. Read every retained dependency statement and its Lean/Mathlib
   match: restriction, composition/adjunction, preservation of epis and sums, unit
   pullback, and finite local generation provide the claimed facts. The structure
   sheaf lemma is used through its Mathlib match, not the pruned tensor-specific
   module. No new-node metadata or change record is required.

Changed the existing theorem's proof docstring, which still cited the removed
local-lifting criterion twice and described the obsolete plan. It now describes the
actual four proof steps and use of categorical epis. No proof term was rewritten;
all lines still satisfy the 100-character limit.
