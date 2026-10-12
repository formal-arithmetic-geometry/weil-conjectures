## What changed

Proved `AlgebraicGeometry.Etale.isIso_constantSheaf_to_generic_lowerStar` in
`lean/Sheaf/AlgebraicGeometry/NormalGenericConstant.lean`, preserving its entire signature.
Used the existing `Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed` in
`WeilConjectures.ConstructibleSheaf.FinitePushforward`, with `ULift ℤ` coefficients.
Added the proof import `Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison`
for its already-proved canonical inverse-image comparison. The coefficient module structure
is already available through the retained imports. All original public imports are preserved.

Three fully proved private helpers provide the formal glue: coefficient forgetting respects
invertibility of the constant-sheaf unit; the residue map of the generic stalk is an
isomorphism; and an invertible unit stays invertible after precomposition with a scheme
isomorphism. The coefficient helper uses the actual adjunction-unit equation, then
`constantCommuteCompose` and unit naturality, rather than an arbitrary object isomorphism.
The composition helper uses `upperStarComp_hom_app_unit_app` to transport the actual unit.
Its scheme-isomorphism case uses only identity/composition coherence, not the theorem on
general universal homeomorphisms. The final canonical constant-sheaf identification is
invertible, and pushforward preserves its invertibility.

Updated the existing node `lem-fin-normal-generic-constant` in `proof`, `proof_deps`, and
`proof_origin` to match this shorter route. No definitions or public statements changed.
The unit `sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps`; the change is
below the unit level and does not remove a required unit realization.

## Proved and sorry left

Proved the module's sole original sorry:
`AlgebraicGeometry.Etale.isIso_constantSheaf_to_generic_lowerStar`
(node `lem-fin-normal-generic-constant`). No sorry remains in the delivered module;
no new sorry was introduced and no intermediate statement was split off.
All three private helpers are completely proved.

The existing source theorem
`AlgebraicGeometry.Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed`
(node `lem-weil-pbc-normal-constant-generic`) is still sorry in its own module.
This delivery reduces to that existing geometric theorem; it does not claim that the
transitive proof is sorry-free. The canonical coefficient-comparison theorem imported
from `Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison` is proved.

Local compilation of the final module succeeds without warnings in approximately six
seconds. `deliver3.py --no-push` printed OK: local and server compilation and the
axiom/preflight checks passed, except for the second-reading section reserved for the
next worker. Nothing was pushed.

## No longer needed

Removed original proof imports:

- `Sheaf.AlgebraicGeometry.EtaleNormalComponents`.
- `WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (its definitions remain available
  through the unchanged public import `WeilConjectures.ConstructibleSheaf.Defs`).

The second reader also removed the redundant newly added proof import
`Mathlib.Algebra.Module.ULift`; compilation confirms its instances are already available.

The delivered proof does not directly need the original componentwise-route nodes
`lem-fin-etale-normal-components`, `lem-weil-pbc-flat-lfp-open`,
`lem-weil-pbc-generic-fibre-localization-domain-irreducible`, or
`lem-weil-pbc-constant-sheaf-sections-connected`. The direct image definition remains needed.
The connected-section and generic-fibre facts remain dependencies of the reused source
normal-scheme theorem, so they are not claimed to be globally unreachable. Other users may
also still need the pruned nodes and modules.

The two new proof-level dependencies are `lem-weil-pbc-normal-constant-generic` and
`lem-weil-pbc-module-abelian-inverse-image-comparison`; the composition comparison is
`lem-weil-pbc-inverse-image-composition`. The definition nodes for the function field,
residue field, constant sheaf and direct image describe the remaining constructions.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG already records the reused 09Z5 theorem in `same_as`,
but the earlier Lean review noted its coefficient category and its generic-stalk domain
as differences and the proof plan did not exploit it. Those differences can be bridged:
use `ULift ℤ` to put the ring in universe `u + 1`, the proved canonical coefficient
comparison, and the generic-stalk residue isomorphism. This is an existing-declaration
specialization with complete Lean glue, not a new restatement of the item.
The theorem does not need the Noetherian or finiteness assumptions along this route,
but its signature is left unchanged. The original theorem docstring preserves the valid
componentwise proof plan; the updated node records the proof actually written.

No new nodes and no change records are needed. All writes by the worker are in its sandbox;
the dry-run delivery tool is the only operation that prepares a review commit.

## Second reading by W2

1. Interface: PASS. Compared the sole delivered module and node with the repository using
   `diff`. The existing theorem signature and its docstring are byte for byte unchanged;
   no existing definition or other declaration was changed. Original public imports remain
   identical. The three added helpers are private and occur only in proofs. No change record
   is required.
2. Proof: PASS. Independently compiled the module without errors or warnings. In a scratch
   copy, `#print axioms` for each private helper reports only `propext`, `Classical.choice`
   and `Quot.sound`. The main theorem reports those axioms and `sorryAx`, as expected from
   the existing normal-scheme theorem; no direct sorry remains. Checked the module for
   forbidden declarations and attributes and for hollow definitions: none. In particular,
   the coefficient comparison is the mate of the actual unit, its adjunction equation and
   unit naturality identify the required map, and composition coherence transports that
   unit along the generic residue isomorphism. The isomorphism case uses the proved
   equivalence construction from identity and composition, not an open topological
   invariance theorem.
3. Split statements: PASS, none were added. The private helpers are all proved. Their
   edge cases are sound: arbitrary (including zero) coefficient groups have their integer
   module structure; an integral scheme is nonempty and its generic stalk is a nontrivial
   field; the composition helper includes identity scheme isomorphisms and arbitrary
   sheaves. Read the reused normal-scheme theorem and the canonical comparison in full.
   Independent LeanFinder search for the generic stalk/residue-field identification,
   Loogle search for bijectivity of the residue map, and `rg` searches for residue
   isomorphisms and constant generic units found no shorter applicable theorem.
4. Route and pruning: PASS after removing one redundant import. The existing normal-scheme
   theorem is already recorded as `same_as`; this proof specializes it and supplies the
   genuine coefficient and generic-stalk glue. Both remaining proof imports are used by
   name. Tested deletion of `Mathlib.Algebra.Module.ULift` in a scratch copy: compilation
   still succeeds, so removed it from the delivery. `No longer needed` lists all four old
   proof dependencies absent from the new proof, and all three original removed imports.
   Checked `dag/units/sk-prop-sf-cbc.json`: its realized statement and steps are empty, and
   this below-unit reduction does not bypass a required realization.
5. DAG: PASS. The node differs only in `proof`, `proof_deps` and `proof_origin`; its
   mathematical statement, source, unit and Lean record are unchanged. Checked each
   dependency's recorded declarations against the proof. The dependency list is exactly
   the union of the proof steps' `uses`, and the proof steps describe the Lean argument.
   The function-field node explicitly records reuse of Mathlib's integral-scheme
   function field, which is what the generic-residue helper uses. No new nodes exist.

Second-reading changes: removed the redundant proof import `Mathlib.Algebra.Module.ULift`,
updated the import explanation and pruning list above, and added this review. No proof or
statement needed repair. Scratch axiom and import checks remain outside `lean/` and are
not part of the delivery.
