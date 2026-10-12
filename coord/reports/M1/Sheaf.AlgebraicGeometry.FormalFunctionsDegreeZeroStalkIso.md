## What changed

Proved `AlgebraicGeometry.formalFunctions_degreeZero_stalkIso` using Mathlib's
isomorphism instance for the degree-zero right-derived augmentation of an additive
functor preserving finite limits. Module direct image is definitionally scheme
module pushforward, which preserves finite limits. Map the augmentation through
the module stalk functor and turn its bijective underlying linear map into a
`LinearEquiv`. The existing signature and docstring are unchanged.

Removed three unused proof imports: `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`,
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`, and
`Sheaf.Paper.HigherDirectImagePresheaf`. The last removal was made during second reading.
Scoped `linter.unusedVariables false` to the existing theorem to suppress the unused
existential name `a` without altering its signature. Updated the node's proof,
`proof_deps`, and `proof_origin` to match the direct Mathlib argument.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.formalFunctions_degreeZero_stalkIso`
(node `lem-weil-pbc-formal-functions-degree-zero-stalk-iso`). Proved 1 of 1;
no holes remain and no holes or declarations were added. This is a proof, not a
decomposition. Local compilation is clean. A scratch-copy `#print axioms` shows
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`;
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`;
- `Sheaf.Paper.HigherDirectImagePresheaf`.

The old proof dependency `lem-weil-pbc-left-exact-injective-resolution-degree-zero`
is no longer used as a separate project node: Mathlib supplies its needed
augmentation-isomorphism instance directly. The first worker's added dependency
`lem-weil-pbc-higher-direct-image-presheaf` is likewise unnecessary and removed.
The two other removed imports were not old `proof_deps` and no declaration from
them is used. These removals describe this module's proof dependencies; whether
any whole module leaves the targets' import closure is determined by the ledger.

## Where the brief, the DAG or earlier work was wrong

The first worker's argument was valid, but extracted one conjunct of the much
larger `higherDirectImagePresheaf` theorem. The direct Mathlib augmentation instance
is shorter and needs no chosen injective resolution. The original DAG's unnamed
left-exact-resolution dependency need not be separately realized for this proof.
No mathematical error in the existing statement was found.

## Second reading by M1

1. Compared every delivered Lean file with the repository version. There is only
   the item's module. Its existing signature is byte-for-byte unchanged; no
   statement, definition, visibility, or public import changed. No change record
   is needed. Verdict: pass.
2. Read the complete proof, the formal-functions stalk abbreviation, the direct
   image definition, and Mathlib's augmentation instance. Compiled the repaired
   file with `lcompile.py`: no errors or warnings. No `sorry`, prohibited axiom,
   unsafe declaration, opaque declaration, external implementation, or data
   definition was added. The scratch axiom check lists exactly the three permitted
   axioms. Verdict: pass.
3. No new or split-off statements exist, so there are no new small-case claims,
   duplicate statements, docstring proofs, or nodes to validate. The argument
   applies to all scheme morphisms, including identity maps and zero stalk modules,
   since finite-limit preservation and functorial preservation of isomorphisms
   have no extra hypotheses. Verdict: pass.
4. Searched the library for degree-zero augmentation and stalk comparisons and
   read Mathlib's `RightDerived.lean` instances. Found and used the shorter direct
   route, removing the larger presheaf theorem import. The remaining sole public
   import supplies the theorem's types and definitions. Checked
   `dag/units/sk-thm-p1.json` `realized`: neither the removed nodes nor this local
   comparison realizes a fixed unit step, and all recorded unit steps are retained.
   The removed old proof dependency is explicitly reported above. Verdict: pass.
5. Compared the old and delivered node records: only stage-3-owned proof fields
   change. The final proof and dependency list record module direct image and
   module stalk, with Mathlib providing the augmentation and linear equivalence
   conversion. No new node or unit change is required. Verdict: pass.

Second reading changed the proof to use Mathlib's augmentation instance directly,
removed `Sheaf.Paper.HigherDirectImagePresheaf`, suppressed the pre-existing unused
binder warning locally, and corrected/completed the node and pruning report.
