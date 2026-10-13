## What changed

Completed the inherited sandbox reduction of
`Sheaf.AlgebraicGeometry.ProjectionComparisonExact`. The public definition
`AlgebraicGeometry.projectionComparisonNatTrans` and the signature of
`AlgebraicGeometry.projectionComparison_exact` are unchanged. Added proof-only imports
of `Sheaf.AlgebraicGeometry.DerivedPullbackTensorShift`,
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift`, and
`Mathlib.CategoryTheory.Triangulated.Adjunction`.

The proof chooses compatible tensor/pullback shifts, induces the direct-image shift
through the given adjunction, proves direct-image exactness by Mathlib's right-adjoint
exactness theorem, and obtains composite exactness by instances. It identifies the
explicit projection mate with the upstream right-adjoint projection map by extensionality
and the inverse-tensorator component formula. The upstream projection-map shift theorem
then gives compatibility. Neither invertibility of the mate nor a projection formula
is assumed in this argument.

Added one new module and node for the geometric tensor/pullback shift construction.
Updated the parent node's proof, proof dependencies and proof origin to match the Lean.
No existing definition, statement, universe, binder or public visibility was changed.
No forced adaptations and no change records are needed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.projectionComparison_exact`
(node `lem-sc-projection-comparison-exact`). There are no remaining sorries in the
item's module.

Added one hole:
`AlgebraicGeometry.derivedPullback_tensorShift`
(node `lem-sc-derived-pullback-tensor-shift`), in the new module
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorShift`.
Its proof is exactly `:= by sorry`; its statement, source and natural-language proof
are in the docstring and node. This is a decomposition, with one upper hole closed
and one lower hole added (net zero), not a claim of an axiom-free geometric proof.
The lower statement supplies only tensor/pullback exact shift data. It has no direct
image, adjunction, counit, fixed E, or projection mate. The direct-image exactness,
shift transport through the adjunction, identification of the mate, and combination
of the shift squares are genuine Lean proofs in the parent module.

Both modules compile in sandbox import order. The inherited version compiled first;
the corrected existential pullback-shift version also compiled. Compilation and the
axiom probe are repeated by the required delivery dry run. Existing dependency
sorries are not modified and no additional holes are introduced by the proof.

## No longer needed

None. No original imports, modules or node dependencies were removed. All six original
public imports are preserved for the original public statements and definition, and
all three added proof-only imports are used. The geometric K-injective proof of
direct-image exactness described in the original plan needs no additional lemma:
Mathlib proves exactness of the right adjoint from that of the left adjoint. This
eliminates an argument to formalize, but no previously listed separate DAG node.

The unit `sk-thm-picard-duality` and its route are unchanged; its realized fields do
not assign the current node to a separate mandatory unit step.

## Where the brief, the DAG or earlier work was wrong

The previous attempt had compiling Lean but no new-node record, parent-node update,
or report. These have been supplied. Its intermediate statement required compatibility
with an independently supplied exact shift structure on pullback. That is stronger
than the parent's source argument, which chooses compatible shifts together. The new
intermediate theorem instead existentially chooses the pullback shift along with the
tensor shifts; the parent no longer selects the separate shift witness from
`exists_derivedPullback`. This correction affects only the previously undelivered helper.

The upstream tensor shift module already proves canonical tensor exactness, and the
upstream projection-map shift module already proves the formal mate argument. Neither
alone supplies compatible shift structures for the geometric pullback with its supplied
strong monoidal structure. This is the precise remaining geometric step, retained in
the new theorem rather than hidden in the parent's proof.

Checked zero tensor factors, empty schemes, translation by zero and identity pullback
as edge cases of the new statement. Zero factors give zero functors; the zero shift is
controlled by unit coherence. Identity pullback with its canonical monoidal structure
reduces to the standard tensor shift comparisons. For a supplied monoidal structure,
the statement chooses compatible shifts rather than asserting equality with separately
fixed canonical comparisons. No boundedness, invertibility or quasi-coherence assumption
was silently added to the tensor inputs. The new assertion follows the parent's
monoidal transport route and remains the next proof item.

Consulted Stacks [Tag 08EU](https://stacks.math.columbia.edu/tag/08EU) and
[equation the project server](https://stacks.math.columbia.edu/tag/0B53): the former uses exactness
for the triangle argument, and the latter specifies the mate orientation. The expanded
shift-coherence argument is recorded as agent-written, as in the original parent node.
Searches of the whole blueprint for tensor shifts and Tag 08EU found no existing exact
match. The new node records the semantic, type-pattern and local source searches;
LeanSearch was unavailable and that failure is recorded, not treated as a result.

## New nodes

`lem-sc-derived-pullback-tensor-shift`, at
`dag/nodes/sec-picard-framework/lem-sc-derived-pullback-tensor-shift.json`, states
simultaneous exact shifts for derived pullback and tensorRight, natural in the fixed
factor and compatible with the flipped inverse tensorator. It is the geometric portion
of the parent's second and third steps, inherits its chapter and unit, and has its own
public module and named hole. Its statement is strictly a part of the parent's argument;
it does not restate any projection comparison theorem. No change record is required.

## Second reading by F4

1. **Unchanged interface: PASS.** Compared the complete item module and its node
   against the repository by `diff -u`. The existing definition, its naturality
   proof, the theorem signature, all universes and binders, and public visibility
   are byte-for-byte unchanged. Only proof imports, the theorem proof and its
   proof explanation changed. There are no change records or forced adaptations.
2. **Proof and holes: PASS as a decomposition.** Compiled both modules in import
   order with `lcompile.py --all`: 4.2 s and 8.9 s, without warnings or errors.
   Read the adjunction-induced shift construction, right-adjoint triangulatedness,
   tensorator flip, componentwise mate identification and final upstream application.
   The single new sorry is the whole proof of the named public theorem
   `AlgebraicGeometry.derivedPullback_tensorShift`. There are no hollow definitions
   or forbidden declarations. The delivery dry run's per-declaration axiom probes
   passed; dependency sorryAx remains expected. This closes one original hole and
   adds one lower hole, net zero; it does not complete the geometric proof.
3. **New statement: PASS.** Read every clause against its use in the parent.
   It concerns only tensor/pullback shifts, and strictly omits the direct-image,
   adjunction and mate conclusions proved by the parent. Checked the zero tensor
   factor, zero translation, empty schemes and identity pullback: no additional
   nonvanishing or boundedness condition is needed. Simultaneous existential
   choice avoids requiring a previously fixed pullback shift. Its source and
   full proposed K-flat/localization and monoidal-transport proof are recorded
   in the docstring and node; this argument is agent-written, rather than an
   assertion that Stacks supplies arbitrary-monoidal-structure coherence verbatim.
   Independent LeanFinder, qualified Loogle and grep searches found no exact
   replacement. Read upstream `DerivedCategory.Monoidal.Shift` and
   `DerivedCategory.Monoidal.ShiftComparison`: the latter's factorization and
   compatibility hypotheses are not available for the supplied tensorator.
   The remaining geometric construction is not a few-minute closure.
4. **Route and pruning: PASS.** The parent already uses Mathlib for right-adjoint
   exactness and upstream `ProjectionMapShift` for the mate calculation. Each
   added import is proof-only and used. No old proof dependency has become
   unused, so the No longer needed list is complete. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists
   are empty, and this reduction does not bypass a recorded mandatory unit node.
   The unit record and route remain unchanged.
5. **DAG agreement: PASS.** The parent proof steps and dependency union match
   the construction and the geometric helper application. Its original statement
   is unchanged. The new node has its source, statement dependencies, three
   successful search kinds (including this reader's qualified Loogle search),
   proof steps, origin, creation/blueprint/chapter/unit records and exact Lean
   signature. All proof uses are in its proof dependency union.

Second reading changed only the new node's search evidence and this report.
The compiling Lean proofs and statements needed no repair. Final delivery checks
are run again after adding this section.
