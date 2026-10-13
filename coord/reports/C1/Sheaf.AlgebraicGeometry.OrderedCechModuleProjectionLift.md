## What changed

Replaced `orderedCech_module_projection_exists` in
`Sheaf.AlgebraicGeometry.OrderedCechModuleProjectionLift` by a complete Lean proof
from a proved degreewise construction and one differential-compatibility theorem.
The proof assembles `D ⟶ D` with `CochainComplex.ofHom`, applies pushforward and
`HomologicalComplex.extendMap`, and verifies the required formula by evaluating
`extendMap_f` and cancelling the extension isomorphism.

Added `Sheaf.AlgebraicGeometry.OrderedCechDegreewiseProjection`. It defines the
source-scheme coordinate and its explicit finite signed value, then **proves**
`orderedCech_degreewise_projection_exists`. The construction uses a product lift of
finite sums of natural coefficient restrictions and the inverse of `e`. Local
linearity follows by coordinate injectivity, `hlinear`, semilinearity of restrictions,
and uniqueness of arrows of opens. `PresheafOfModules.homMk` lifts the resulting
natural transformation to a module-sheaf map. No data is taken from an unproved
existence statement.

Added `Sheaf.AlgebraicGeometry.OrderedCechDegreewiseProjectionDifferential` for the
remaining adjacent-differential identity. This requires already supplied degreewise
maps and `hd`; it has neither an existence conclusion, pushforward, extension by
zero, nor an `hlinear` hypothesis. Thus it is strictly a part of the original task.

All three modules compile cleanly with `lcompile.py --all`. A separate scratch
check proves that the signed value is zero whenever `r ≤ p`, using the cardinality
bound for a strict embedding `Fin (p+1) → Fin r`. This checks the empty-family case
and all degrees beyond the cover size. The scratch file is outside the delivery's
Lean sources. The construction and its coordinate proof use no nonemptiness
assumption and work for zero coefficient modules and empty opens.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.orderedCech_module_projection_exists`
(node `lem-pc-ordered-cech-module-projection-lift`). Its signature and all existing
definitions are unchanged.

Also proved the new theorem
`AlgebraicGeometry.Scheme.Modules.orderedCech_degreewise_projection_exists`
(node `lem-pc-ordered-cech-degreewise-projection`).

Exactly one new hole remains:
`AlgebraicGeometry.Scheme.Modules.orderedCech_degreewise_projection_comm`
(node `lem-pc-ordered-cech-degreewise-projection-differential`). Its proof is exactly
`:= by sorry`, with a complete source-based proof plan in its docstring and node.
There are no sorries in the original module or the degreewise construction module.

This is a decomposition: one old hole closed and one strictly smaller hole added;
net hole reduction is zero. The module-sheaf assembly and pushforward/extension
parts are proved, while transport of the additive differential identity remains.

## No longer needed

Removed the original module's direct proof import
`Sheaf.AlgebraicGeometry.SignedCechExtension`, replacing it with
`Sheaf.AlgebraicGeometry.OrderedCechDegreewiseProjectionDifferential`.
The old parent proof dependency `lem-pc-signed-cech-extension-differential` is
no longer directly used by the parent proof. SignedCechExtension is still a planned dependency of the remaining differential
statement, so no existing dependency module or DAG node is globally pruned.
The original public imports remain because its statements and definitions use them.
No homotopy, sorting-homotopy, or kernel-vanishing lemmas are used or added.

## Where the brief, the DAG or earlier work was wrong

The existing dependency `signedCechExtension_differential` is formulated for additive
cochains on a chosen SiteCechComplex. It is not directly a compatibility theorem for
the categorical Čech presheaves and module-sheaf presentation of this item. The new
differential node isolates precisely this transport and the ordered-face argument.
The degreewise naturality and local scalar assembly, which had no separate stated
interface, are now proved rather than postponed.

The unit route is unchanged (`sk-thm-picard-coherence`); this is a subdivision of the
parent's existing signed-projection argument. No statements or interfaces were
changed and no adaptations of other modules are needed.

Sources read: [Stacks 01FK](https://stacks.math.columbia.edu/tag/01FK) and
[Stacks 01FM](https://stacks.math.columbia.edu/tag/01FM). The source omits the proof
of 01FK, so the explicit assembly and transport details are marked as agent-written
in proof_origin. Searches ran through msearch.py: LeanSearch was unavailable with
HTTP 500; LeanFinder returned generic cochain constructions; Loogle returned
`HomologicalComplex.extendMap_f`; grep returned no projection match. Direct local
searches found the existing additive signed-extension and evaluation-comparison
interfaces. Blueprint searches for signed extension, ordered Cech and 01FK found
no duplicate imported node.

## New nodes

`lem-pc-ordered-cech-degreewise-projection`, in
`dag/nodes/sec-picard-framework/lem-pc-ordered-cech-degreewise-projection.json`,
records the source-scheme coordinate formula and the proved degreewise module-sheaf
construction. Its Lean module is OrderedCechDegreewiseProjection.

`lem-pc-ordered-cech-degreewise-projection-differential`, in
`dag/nodes/sec-picard-framework/lem-pc-ordered-cech-degreewise-projection-differential.json`,
records the adjacent-differential identity for any family satisfying that formula.
Its Lean module is OrderedCechDegreewiseProjectionDifferential; this is the sole
remaining sorry. The parent node now records the actual assembly proof and these
dependencies. No change record is needed because existing signatures, definitions
and public imports are unchanged.


## Second reading by C1

1. Compared the original module with the repository using diff. Only the proof
import, theorem docstring and theorem body change. All four existing declarations'
signatures and all three existing definition bodies are byte-for-byte unchanged;
the original public imports are identical. The only changed parent-node fields
are proof, proof_deps and proof_origin. There are no forced adaptations or interface
changes and no applicable open change record. Verdict: unchanged statement.

2. Independently compiled all three modules in import order using lcompile.py.
They compile without errors or warnings. Inspected every delivered definition and
proof: the restriction natural transformation R, product lift c, inverse transport
and PresheafOfModules.homMk are actual constructions. The choose of Q uses the
proved construction theorem, not an unproved existence theorem. Exactly one literal
sorry remains, in orderedCech_degreewise_projection_comm. Scratch #print axioms
checks of every declaration show only propext, Classical.choice and Quot.sound
for the degreewise construction and all definitions; the differential theorem and
parent existence theorem additionally use sorryAx. Verdict: valid partial proof,
not a sorry-free proof of the original theorem.

3. Read the differential theorem against its node and Stacks 01FK and 01FM
(https://stacks.math.columbia.edu/tag/01FK and
https://stacks.math.columbia.edu/tag/01FM). The hd hypothesis transports the
adjacent differential; hQ fixes the degreewise formula, and no local scalar
hypothesis is needed for equality of already supplied morphisms. Read
signedCechExtension_differential and signedCechExtension_increasing: the first
asserts that the differential of a signed extension is the signed extension of
its ordered coordinates; the second identifies those coordinates, whose faces
remain increasing. This supplies precisely the additive argument needed. The
new theorem asserts only commutation, with no existence, pushforward or extension
claim, so it is strictly smaller than the parent. The module assembly and local
linearity are already proved separately. The filtered sum has one sorting term
on distinct tuples and no term on repeated tuples. Recompiled the scratch
cardinality proof that r ≤ p makes every value zero, covering r=0 and all high
degrees. Also checked p=0: Q is the identity and the pair differential is the
two-term difference, including the zero repeated pair; for r=1 every higher Q
is zero and the pair differential on the sole repeated label vanishes. Zero
modules and empty opens require no additional assumption. Added an explicit
sectionwise family, coefficient presheaf and face-coordinate formula to the
remaining docstring and node proof to make the transport instructions concrete.
Verdict: true, necessary decomposition with a complete natural-language proof.

4. Searched independently with msearch LeanFinder for alternating extension and
face differential, Loogle for Tuple.eq_sort_iff, and grep for alternating
 differential / cechComplex map. Also searched lean/Sheaf and lean/WeilConjectures
for sorting and comparison interfaces, and read CechEvaluationComparison.
The generic alternating-coface map theorem does not supply a cosimplicial sorting
map; CechEvaluationComparison supplies an isomorphism without a public coordinate
formula. Neither closes this compatibility theorem by a short application.
SignedCechExtension is the existing useful additive result, retained for the open
proof. The concrete product-extensionality import is used in coordinate
injectivity; the public imports supply signature and definition data. The sole
old proof dependency removed from the parent's direct proof_deps is now explicitly
listed under No longer needed; it remains below the differential node, so no
module is globally pruned. Read sk-thm-picard-coherence.json and its realized
fields: no unit realization is removed or bypassed. Verdict: route preserved.

5. Read all three node files with their modules. Their recorded Lean signatures
occur verbatim, and proof_deps is exactly the union of step uses. The parent
records degreewise construction, commutation, ofHom, pushforward, extension and
coordinate cancellation. The new construction node records the actual product
and local-linearity proof; the differential node records the sole remaining hole.
Both new nodes have source, searches, creation, blueprint ancestry, chapter/unit
and full Lean records, and neither introduces a cycle through the parent.
Verdict: nodes agree with the delivered Lean.

Second-reading changes: added missing blueprint identifiers to the two new
module docstrings, made the remaining differential transport proof more explicit
in its docstring and node, and named the removed parent proof dependency in the
pruning report. No Lean signature, definition or proof body was changed. The
hole accounting remains one original hole closed, one new hole added: a
decomposition with net reduction zero.
