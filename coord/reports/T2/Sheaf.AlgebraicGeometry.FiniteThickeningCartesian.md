## What changed

Proved `AlgebraicGeometry.isFinite_iff_of_finiteOrderThickening` in
`Sheaf.AlgebraicGeometry.FiniteThickeningCartesian`, with its signature unchanged.
The proof follows Stacks 09ZW (8): finite is integral plus locally of finite type;
the existing lifting equivalences supply those two properties. Nilpotence gives
surjectivity by Mathlib's ideal-support lemmas. The pullback is a thickening by
Mathlib's closed-immersion and surjectivity base-change instances. Pullback symmetry
reconciles the opposite projection convention of the local finite type lemma.
Removed the proof import of the universal-homeomorphism module and the unused
public import of `Sheaf.AlgebraicGeometry.BaseChangeConventions`, and updated the
item's DAG proof, dependencies, and proof origin to match these choices.

Validation: the module compiles with lcompile.py with no errors or warnings.
Both proof imports passed tools/import_direction.py. LeanFinder, Loogle and grep
searches found the existing Mathlib base-change and finite/integral/LFT lemmas,
but no direct finite-thickening descent theorem. The unit's realized steps are
unchanged; this node is below that unit's realized statements and steps.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.isFinite_iff_of_finiteOrderThickening`
(node `lem-weil-pbc-thickening-finite-cartesian`).
No sorry remains in the delivered module. No new holes or intermediate statements
were added. This is a proof from existing stated dependencies, not a new
split: `AlgebraicGeometry.isIntegralHom_iff_of_thickenings`
(node `lem-weil-pbc-thickening-integral`) and
`AlgebraicGeometry.locallyOfFiniteType_iff_of_finiteOrderThickening`
(node `lem-weil-pbc-thickening-lft-cartesian`) retain their pre-existing holes
in their undelivered library modules. Thus the theorem still depends on those holes;
it is not claimed to be transitively sorry-free.

## No longer needed

Removed imports:
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism` and
`Sheaf.AlgebraicGeometry.BaseChangeConventions`. The latter contributes no declaration
to the statement or proof: Mathlib already supplies the chosen pullback and projections.
The node `def-pc-base-change` remains as the mathematical convention in the DAG;
its separate comparison theorems and module are not used by this proof.
The proof does not need node
`lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`:
its sole purpose in the planned proof was to establish that the pullback projection
is a surjective closed immersion, which Mathlib proves directly. The updated DAG
instead uses `lem-weil-pbc-closed-immersion-base-change` and
`lem-weil-pbc-surjective-base-change`, both already Mathlib leaves. This reports
pruning from this proof only; other import paths may still need that module/node.
No further planned proof dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The target uses `pullback.snd f' i`,
while the local finite type dependency uses `pullback.fst i f'`; these are equivalent
through pullback symmetry, so neither statement needs changing. The DAG's step 2
unnecessarily passed through universal homeomorphisms. The second reading updated the declaration docstring to describe the support
and direct base-change argument; the DAG records the same shorter step.

## Second reading by T2

1. Compared the entire delivered Lean file against the repository version and parsed
   the node changes: the sole theorem signature is byte-for-byte unchanged; no
   definitions or other declarations were added or changed. Only the proof, imports,
   and explanatory docstring changed. Verdict: pass.
2. Compiled the delivered proof with `lcompile.py` without errors or warnings.
   A scratch copy with `#print axioms
   AlgebraicGeometry.isFinite_iff_of_finiteOrderThickening` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the last comes from
   the two existing dependency holes reported above. No forbidden declaration,
   new sorry, hollow definition, or witness chosen from unproved existence was
   introduced. The nilpotence/support argument also handles order zero and empty
   schemes, and pullback symmetry has the correct projection orientation.
   Verdict: pass.
3. No new statements or split holes exist. Read both imported lifting equivalences
   and checked their arguments against the constructed commutative square. Searched
   the Mathlib finite-morphism file and the upstream finite-morphism additions for
   a direct thickening/nilpotence shortcut; neither provides one. Verdict: pass.
4. Compared old and new `proof_deps`: the sole removed dependency is the
   universal-homeomorphism lemma, explicitly listed above. The replacement leaves
   are Mathlib's closed-immersion and surjectivity base-change instances.
   Inspected `dag/units/sk-thm-p1.json`: neither this node nor the removed lemma
   realizes its statement or a proof step. The unit route stays intact. Removed
   the unused public BaseChangeConventions import and verified the same proof still
   compiles; its mathematical convention remains in the DAG. Verdict: pass.
5. Compared the DAG steps with the Lean proof, including the ideal-support
   surjectivity calculation, the two thickening pairs, `pullback.condition`, and
   the symmetry/composition argument for local finite type. `proof_deps` is exactly
   the union of the steps' `uses`; only allowed proof fields were changed.
   Verdict: pass.

Second reading changed the unused BaseChangeConventions import, synchronized the
proof docstring with the actual argument, and expanded this report. No proof term,
statement, or definition needed repair. Scratch axiom probes are not delivered. The public import removal is documented
in `coord/changes/FiniteThickeningCartesian-imports.md`; the sole direct importer
`Sheaf.AlgebraicGeometry.FiniteEtaleThickeningLift` uses no declaration from that
module, and no target statement changes.
