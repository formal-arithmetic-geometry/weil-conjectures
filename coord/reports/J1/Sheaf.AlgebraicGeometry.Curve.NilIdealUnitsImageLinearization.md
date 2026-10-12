## What changed

Replaced the `sorry` in `AlgebraicGeometry.Scheme.nonempty_nilIdealUnitsImageIso`
with a complete Lean proof composing two isomorphisms through a concrete additive
image sheaf. Its signature, universes, hypotheses and conclusion are unchanged.
Added two private proof imports; all three existing public imports remain necessary
for the original statement.

Added `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf`: the coefficient
functor forgets ring multiplication and lifts the additive group; the sheaf has
exactly these section groups and pullback restrictions. Its sheaf condition is
proved using preservation and reflection of limits. The restriction map is the
actual whiskering of `etaleStructurePresheafToPullback`. There is no chosen witness,
new existence-based data, or hole in these constructions.

Added two comparison modules, each with one named theorem left `:= by sorry`:
`NilIdealUnitsAdditiveImageComparison` handles only the square-zero multiplicative
calculation; `AdditiveIdealImageTensorComparison` handles only the additive
ideal/module/tensor comparison. They import the common definitions independently,
so neither proof needs the other theorem.

The original node now records exactly these two comparisons and their composition.
The unit and chapter route are unchanged. All four modules compile together in
import order with `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.nonempty_nilIdealUnitsImageIso`
(node `lem-sc-nil-ideal-units-image-linearization`) by decomposition, not by an
axiom-free proof of its two mathematical comparisons. There are no remaining
`sorry`s in the item's module.

Added two holes:

- `AlgebraicGeometry.Scheme.nonempty_nilIdealUnitsAdditiveImageIso`, node
  `lem-sc-nil-ideal-units-additive-image-comparison`.
- `AlgebraicGeometry.Scheme.nonempty_additiveIdealImageTensorIso`, node
  `lem-sc-additive-ideal-image-tensor-comparison`.

The former has no module cokernel, tensor sections, or quasi-coherence hypothesis
on that cokernel. The latter has no unit groups, nilradical hypothesis, or
square-zero hypothesis. Neither is the target renamed or its hypotheses repackaged:
they identify distinct pairs of mathematical objects and require distinct parts
of the original affine argument. The original proof genuinely composes their
isomorphisms through an intermediate object that is defined without holes.
Closed one old hole and added two lower holes; holes closed minus holes added is -1
(one more remaining hole). This is a decomposition delivery.

Checked the new statements on I=J, I=0, and empty objects: both images and the
quotient are zero. Finite-ring enumeration also checked R=Z/8, I=(2), J=(4),
where I itself is not square zero, and the I=J and zero-ideal cases. The zero ring
was included. The additive comparison was also checked for R=Z/6, I=(2), J=0,
which needs neither nilpotence nor square-zero. These are sanity checks of the
local formulas, not formal proofs of the sheaf comparisons.

## No longer needed

The old direct proof dependencies `def-pc-scheme`, `def-sbc-ideal-sheaf-powers`,
`def-weil-pbc-scheme-reduction`, `def-sc-gm-torsor`, and
`def-sc-etale-qcoherent-module` are replaced in the parent node by the two comparison
nodes. None is globally pruned: they remain statement dependencies or dependencies
of the comparisons (the scheme definition is used by their statements).

No existing imports, nodes or modules were pruned: the original public imports
occur in the unchanged statement, and the original definition dependencies are
still needed transitively by the two comparisons. Removed the stale previous
attempt's report claims and second-reading text from this first-worker report.
No equivalent invertible-morphism existence split is retained.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's `exists f, IsIso f` split was equivalent to the entire target.
This delivery instead separates the ring-theoretic unit comparison from the
additive tensor-section comparison and constructs their common intermediate sheaf.

The node's proof dependencies are definitions, not theorems asserting its affine
comparisons. Reading them did not supply those comparisons. The new named theorems
state the missing steps of that existing plan with full proof descriptions.

LeanSearch was unavailable (Internal Server Error). LeanFinder, Loogle and source
searches found general unit, cotangent-module, and structure-sheaf infrastructure,
but no existing comparison of these specified sheaf images. Blueprint-wide searches
found no duplicate of the new statements or small-etale additive restriction.
The existing `structureSheafAb` is on the Zariski site, not this small etale site.

WANTED: the blueprint source file
`literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/lem-sc-brauer-zero-all-curves.md`,
Proof, Step 1 and its Claim. Its file is absent on this machine. The detailed affine
argument is available in the original item's docstring and node; the new proofs in
words expand that existing argument and are marked as written by an agent.

## New nodes

`def-sc-etale-additive-structure-restriction` records the concrete additive structure
sheaf and pullback restriction, including its coefficient functor. Its constructions
are fully defined and their required proofs compile without holes.

`lem-sc-nil-ideal-units-additive-image-comparison` records the unit-image to
additive-image comparison: on affine refinements send the image of 1+a to a mod J.
The node and docstring explain nilpotence, well-definedness, bijectivity, the
square-zero group law and compatibility with restrictions.

`lem-sc-additive-ideal-image-tensor-comparison` records the additive image to
tensor-section comparison: identify the additive image locally with I_B/J_B and
use flat base change for the specified module cokernel. It is independent of the
unit calculation and has no nilpotence hypotheses.

No statement or definition of an existing module was changed, and no change record
or forced adaptation is needed.

## Second reading by J1

1. **Existing interface: PASS.** Compared the item with the repository by `diff`
   and checked the complete theorem signature byte for byte. Only two private
   proof imports and the proof body changed. Its original docstring, universes,
   hypotheses, conclusion and public imports are unchanged. The other three
   modules are new. No existing definition changed; no change record is needed.
2. **Proof and data: PASS as a decomposition.** Compiled all four files in import
   order with `lcompile.py --all`, without errors or warnings. Independently
   compiled scratch copies with `#print axioms` for every delivered declaration.
   All four additive construction declarations use only `propext`,
   `Classical.choice`, and `Quot.sound`. The parent and both open comparisons
   additionally use `sorryAx`, exactly as reported. The only two textual holes
   are the complete proofs of the two named public comparison theorems. No
   forbidden declarations, hollow definitions, or arbitrary existence witnesses
   occur. Extracted the sheaf-condition proof into the proved named theorem
   `AlgebraicGeometry.Scheme.isSheaf_etaleAdditivePresheaf`, and the definition
   now refers to it, as AGENTS.md section 5 requires.
3. **Split statements: PASS.** Read both signatures and their full affine proofs
   in words against the actual Gm restriction, additive restriction, ideal module
   inclusion and tensor-sections definitions. The unit comparison has no tensor
   object; the additive comparison has no units or nilpotence hypothesis. They
   are distinct proper parts of the affine argument, and their common object is
   constructed without holes. Checked I=J, I=0, empty affine objects and the zero
   ring; independently enumerated all ideal pairs J contained in I in Z/n for
   1 <= n <= 16, checking additive quotient cardinalities and, under the stated
   nil/square-zero hypotheses, the bijection and group law. This is a local sanity
   check, not a sheaf proof. Repeated LeanFinder searches using principal units,
   square-zero extensions, and flat pullback of quotient ideals; Loogle searched
   `IsNilpotent, IsUnit`; grep searched kernels of structure maps and ideal images,
   and both library roots were searched. Mathlib supplies `isUnit_one_add` and
   affine subscheme quotient descriptions, but no matching sheaf comparison.
   Neither remaining comparison is closable by a short application of these
   results: both still require the natural local-to-sheaf comparison.
4. **Route and pruning: PASS.** The parent composes the two isomorphisms, with a
   definitionally identical intermediate object. All public imports contribute
   to signatures or exposed definitions; both new parent proof imports are
   private. No unused import or globally prunable old dependency was found.
   Clarified `No longer needed` by listing all five old direct proof dependencies
   replaced by comparison nodes; they remain needed transitively or in statements.
   Read `dag/units/sk-prop-h2.json`: its realized fields are empty already; this
   delivery changes neither those fields nor its statement, steps or chapter
   route. The split refines the original affine argument below the unit level.
5. **DAG: PASS.** Compared the existing node JSON: only `proof`, `proof_deps` and
   `proof_origin` changed. The steps name exactly the two applied comparison
   theorems followed by composition, and their dependency union matches. Checked
   each new node's source, statement dependencies, proof description, searches,
   creation metadata, blueprint provenance, unit/chapter and Lean record. Each
   recorded signature occurs verbatim in its module. Added the extracted
   sheaf-condition theorem to the construction node's declaration inventory.

Second reading changed only the placement of the additive sheaf-condition proof,
its node declaration inventory, and this report's direct-dependency accounting.
No additional hole was closed or added: one original hole closed by composition,
two strictly lower comparison holes added, net -1. No module was pruned.
