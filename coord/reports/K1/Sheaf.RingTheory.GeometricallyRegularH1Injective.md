## What changed

Changed `lean/Sheaf/RingTheory/GeometricallyRegularH1Injective.lean` to prove
`Algebra.isRegularLocalRing_and_injective_h1Cotangent_of_isGeometricallyRegular`
with its original signature and docstring. Regular locality is proved directly using the
universe-lifted trivial purely inseparable extension, tensor equivalences and Mathlib regularity
transport. The proof selects a basis from the spanning universal differentials, extends it to K,
checks every finite subfamily using the new lemma, and proves injectivity of the comparison c.
Connecting-map naturality, prime-field H1 vanishing and Mathlib Jacobi-Zariski exactness then prove
injectivity of the H1 map. Composing with the original conormal equivalence finishes the theorem.

Added `lean/Sheaf/RingTheory/GeometricallyRegularDifferentialFamily.lean` for the finite-family
argument, with its own node and complete source proof in words. Added proof-only imports for this
module, Mathlib basis selection, tensor bases and ULift fields. Preserved every existing public
import and declaration signature. No definitions, interfaces or other existing modules changed.

Both modules compile without warnings through lcompile.py --all. The original theorem has no
sorry in its body. The remaining finite-family argument requires the p-root quotient identification,
base-changed exact conormal rows and snake dimension calculation; the existing dependency
signatures were read, but that assembly is left as the strictly smaller finite-family item.

Source checked: Stacks Tag 07E5, proposition-characterization-geometrically-regular, especially
(2) => (4) and (3) <=> (4), at https://stacks.math.columbia.edu/tag/07E5.
The local checkout does not contain the untracked literature source, so the primary online source
was read. The unit sk-thm-p1 and its realized nodes are preserved.

## Proved and sorry left

Closed the sole original hole:
`Algebra.isRegularLocalRing_and_injective_h1Cotangent_of_isGeometricallyRegular`
(node `lem-weil-pbc-geometrically-regular-h1-injective`).

Added one hole, with the entire proof exactly `by sorry`:
`Algebra.linearIndependent_residueField_differentials_of_isGeometricallyRegular`
(node `lem-weil-pbc-geometrically-regular-differential-family`).

This is a decomposition, not an unconditional proof or a net reduction in hole count: one hole
closed and one added. The existing naturality theorem is also still unproved and is used as
intended by stage 3; no hole was added to that existing dependency. Regular locality, the spanning
basis reduction, and the final diagram chase are now actual Lean proofs.

The new statement handles any finite index type, including the empty type. For an empty family
independence is automatic. If k is perfect its absolute differentials vanish, so no nonempty
independent family satisfies the premise. For A = k the asserted family is just the scalar extension
of the original independent family. For a polynomial local algebra the assertion is compatible
with its free differential summand. In contrast, adjoining a p-th root to an imperfect field kills
a nonzero differential, but that field algebra is not geometrically regular over k. No finiteness
of the full absolute differential space is assumed. The statement is the finite-family portion
of the source's argument; it contains neither the regular-local conclusion nor an H1 injection.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.FieldTheory.PthRootsExtensionDegree`
- `Sheaf.Paper.CartierEquality`
- `Sheaf.RingTheory.PthRootPresentationDifferentials`
- `Sheaf.RingTheory.PurelyInseparableBaseChangeLocalRing`
- `Sheaf.RingTheory.JacobiZariskiHomologySequence`

The last import is redundant: naturality publicly imports that module, and the actual exactness
application uses Mathlib `H1Cotangent.exact_map_δ`. The first four modules concern the finite-family
argument now deferred into the new node. They are not used by the original Lean proof, but their
mathematical work is still needed by the new node, so this delivery does not claim to eliminate it.

Removed from the original node's direct proof_deps (now in the finite-family node's proof plan):
`lem-weil-pbc-regular-local-cotangent-dimension`,
`lem-weil-pbc-pth-roots-extension-degree`, `def-weil-pbc-mv-polynomial-ring`,
`lem-weil-pbc-finite-dimensional-domain-is-field`,
`lem-weil-pbc-purely-inseparable-base-change-local-ring`, `lem-weil-pbc-flat-height-formula`,
`def-weil-pbc-flat-ring-map`, `lem-weil-pbc-pth-root-presentation-differentials`,
`lem-weil-pbc-cartier-equality`, and `lem-weil-pbc-snake-lemma-modules`.
The direct dependency `lem-weil-pbc-nl-presentation-h1-functoriality` is also unnecessary for the
original proof: the bundled maps and equivalence already supply the required functoriality;
it remains in the new finite-family node's conormal-row argument. No unit node was bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement or the source. The regularity clause can be
proved directly from the geometric regularity definition, without first using conormal dimension.
The stronger project homology-sequence theorem is unnecessary for the final chase because the
needed exactness is already in Mathlib. Distinct residue-field and quotient instance paths required
explicit quotient use in the proof and a field structure extending the existing quotient CommRing.
Uniqueness of the prime-field algebra structure aligns the field-vanishing theorem. These are local
proof adjustments, not interface changes or forced adaptations.

Searches: LeanFinder returned related extension and standard-smooth results, none matching the
finite-family assertion. Loogle returned a generator-kernel independence lemma, not this assertion.
Mathlib grep found no geometric-regularity or differential-family match. LeanSearch returned an
Internal Server Error and is recorded as unavailable. Blueprint searches for "independent
differentials" and "07E5" returned no matching blueprint node. Existing DAG Tag 07E5 nodes were
read; none states the finite-family subargument. No shorter noncircular proof was found in the
source library. No new axiom or data definition was introduced.

## New nodes

`lem-weil-pbc-geometrically-regular-differential-family`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-geometrically-regular-differential-family.json`,
states preservation of finite independent prime-field differential families. Its eight proof
steps retain the original node's p-root extension, regularity/dimension, beta calculation,
conormal rows, Cartier equality and snake calculation, followed by descent of independence.
Its module is `Sheaf.RingTheory.GeometricallyRegularDifferentialFamily`. This isolates original
steps 4-10; the regularity clause and original steps 2-3 are now proved in Lean. The ancestor is
thm-weil-pbc-finite-etale-lifting, with the original item prepended to the ancestry path.
No change records are needed because no existing definition or statement changed.

## Second reading by K1

1. **Visible declarations:** Compared the entire original module with the repository using
   diff and compared the raw theorem signature byte for byte. The sole existing declaration,
   its docstring, and all three existing public imports are unchanged. The declaration-local
   transparency option affects elaboration of the proof; it adds no assumption. Only the
   existing node's proof, proof_deps and proof_origin differ. No definition, target, or
   change-record-requiring interface was altered. Verdict: pass.
2. **Proof and axioms:** Compiled both delivered modules in dependency order with lcompile.py,
   with no errors or warnings. Scratch copies with explicit #print axioms for both declarations
   show exactly propext, Classical.choice, Quot.sound and sorryAx. The latter is expected from
   the one new finite-family hole and the existing naturality dependency. The item itself has
   no sorry; the helper's only sorry is the complete proof of its public named theorem.
   There are no forbidden declarations or hollow definitions. The comparison c obtained
   from naturality is uniquely determined: pure tensors with universal differentials span
   its source, and hc prescribes its value on each. No arbitrary object is defined from an
   unproved existence statement. Verdict: pass as a decomposition, with net hole change zero.
3. **Split statement:** Read Stacks Tag 07E5, specifically (2) => (4) and (3) <=> (4),
   and the helper's complete docstring and eight node steps. The field, prime characteristic,
   local Noetherian algebra, geometric regularity, canonical residue field, prime-field
   structures and finite independent input family all match the source subargument.
   Empty families are independent; over a perfect base only the empty independent
   differential family occurs; A = k gives scalar-extension independence; a p-root field
   extension killing a nonzero differential fails geometric regularity. The finite-family
   lemma isolates original steps 4-10 and states neither regular locality nor an H1 map.
   The item contains the actual basis reduction and diagram chase, rather than one
   application of a renamed target. Independent searches used LeanFinder for absolute
   differential injectivity at a residue field, Loogle for mapBaseChange, msearch grep for
   p-independence/geometric regularity/07E5, and rg in both source roots and Mathlib.
   The returned formal-smoothness criteria require additional hypotheses; the general
   differential exactness lemmas do not prove the geometric-regularity step. No matching
   upstream result or DAG duplicate was found. The p-root presentation, base-change local
   ring, degree and Cartier dependency declarations were read, including the corrected
   Cartier field-generation hypothesis in its change record. Verdict: true, useful and
   strictly a subargument; not something closable by a short existing lemma.
4. **Route and pruning:** Read sk-thm-p1.realized: neither this item nor the new finite-family
   node replaces any realized unit statement or step. The original proof uses the direct
   regularity transport, a basis selected from spanning differentials, the naturality
   generator formula, and Mathlib H1Cotangent.exact_map_δ to finish the H1 argument.
   Checked that No longer needed lists all eleven removed original proof dependencies and
   all five removed direct imports. The deferred mathematical work remains in the new
   node's plan, so these are direct-import removals, not a claim that those mathematical
   dependencies were eliminated. Removed two redundant public imports from the new module:
   Mathlib.RingTheory.LocalRing.ResidueField.Basic (already public through GRing) and
   Mathlib.LinearAlgebra.LinearIndependent.Defs (already through the remaining imports).
   Both modules still compile. Existing public imports were preserved. Verdict: pass.
5. **DAG agreement:** Checked the unchanged original statement/Lean record and the four
   replacement proof steps against the actual proof. For both nodes, proof_deps is exactly
   the union of the steps' uses. The new node has its source, complete finite-family proof,
   search records, split status, worker/item/group/date, ancestry, chapter/unit, and verbatim
   normalized Lean statement record. Both Lean files satisfy the module conventions and
   100-character line limit. Verdict: pass.

Second-reading changes: removed the two redundant imports in the new module and appended
this review. No proof, statement, definition, or node needed repair. One original hole is
closed and one strictly smaller hole added; this delivery is a decomposition, not an
axiom-free completion of the item or a net decrease in sorry count.
