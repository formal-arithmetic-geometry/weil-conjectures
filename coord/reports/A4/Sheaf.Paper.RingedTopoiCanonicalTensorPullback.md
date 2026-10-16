## What changed

Partially reduce `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`: prove the uniqueness
half of the normalized ordinary tensor comparison and combine it with a separate
existence construction. The theorem's signature is unchanged. Move the existing,
unchanged `SheafOfModules.CanonicalRingedTensorComparison` structure to
`Sheaf.Paper.RingedTopoiTensorComparisonData`, publicly reexported by the original
module, so the independent construction module can be imported without a cycle.
All structure fields, universes, visibility and meaning stay unchanged.

Make `ringedTensorPreadditive` a theorem with exactly its former proposition,
instead of a proof-valued abbreviation. The profiler showed expensive expansion through
`tensorClosed`; this opaque proof API makes the full file compile within 60 seconds.
`MonoidalPreadditive` is a proposition, so proof irrelevance identifies the two values.
The second reading assembles its four laws directly from the proved additive tensor
functors, avoiding expansion of the larger tensorClosed conjunction. No computational
data changes. Also keep the final canonical comparison definition explicit and keep the monoidal structure locally irreducible within the sectionwise and
uniqueness proof sections and while elaborating the derived signatures, with `totalIso`
also locally irreducible; these edits preserve all declaration values and signatures.

The uniqueness proof is concrete Lean: `q_one` identifies the two insertion maps.
Finite-product preservation lifts any pair of inverse-image sections to a generalized
pair, on which the two `pure` equations identify the inverse tensorators. The proof
then cancels tensor sheafification and uses the extension-of-scalars adjunction twice
to extend equality from inserted pure tensors to the whole sheaf tensor. Isomorphism
extensionality and proof irrelevance finish. The helpers are private and fully proved.

Replace two unused public theorem imports by the foundational public imports needed
for the existing statements. Add the construction import and Mathlib's binary-product
and fully-faithful-adjunction APIs for the proof. Update the parent node's route and
add nodes for the extracted data and existence construction. No target statement,
existing mathematical statement, or definition value is changed.

## Proved and sorry left

Closed the original hole
`SheafOfModules.canonicalRingedTensorComparison_existsUnique`
(node `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`). Its uniqueness conjunct is
proved from the definitions and existing tensor/sheafification APIs; its existence
conjunct uses the new construction theorem below.

This is a decomposition, not a net reduction in holes: one original hole closed and
one strictly smaller hole added. The new theorem is only the existence conjunct;
the complete, substantial uniqueness argument remains in the original module.

Original holes left unchanged, both at
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`:

- `SheafOfModules.canonicalRingedTensorComparison_unit`.
- `SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback`.

One new hole:

- `SheafOfModules.canonicalRingedTensorComparison_nonempty`, in
  `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`, node
  `lem-weil-pbc-canonical-ringed-tensor-comparison-construction`. It still needs
  the inverse-image universal property for balanced bilinear maps with the given
  algebraic lift, followed by the explicit scalar-extension tensor isomorphism and
  its generalized pure-tensor equation. The complete construction argument is in
  the docstring and node. Its input may be a zero ring or a zero module; the formulas
  use no nonzero element, division, faithfulness or pointwise inverse-image assumption.

The extracted data module has no proof hole and no hollow definition. No other
module is adapted. The unit and derived assembly were explored in scratch files;
their uncompleted proofs are not delivered or counted as progress.

## No longer needed

Removed direct public imports:

- `Sheaf.Paper.RingedTopoiDerivedTensorPullback`, with its noncanonical theorem
  `SheafOfModules.ringedTopoiDerivedTensorPullback`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`, including the route through
  `lem-weil-pbc-ringed-topoi-module-pullback-tensor` and its set-level auxiliary
  `Sheaf.CategoryTheory.ModulePullbackTensorIsoE`.

The new ordinary comparison construction uses the specified algebraic lift directly;
it does not use the old arbitrary module-lift tensor theorem. The parent node replaces
that proof dependency by the construction node. These imports are not needed by any
proof or signature in this item. A repository-wide declaration-use search found no
use of either removed top-level theorem outside its defining module. Their global
reachability and any additional pruning are for the maintainer's ledger to determine.
The blueprint unit's derived-tensor route and its steps remain in the parent node.
Removed unused proof imports of `FlatOnSite`, `KFlatTelescopeClosure`,
`SiteDerivedTensorDescent`, `ModulePullbackPushforwardAdjunction`,
`RingedTopoiDerivedPullback`, `KFlatResolutionIndependentCoefficients`, and
`KFlatRingedToposPullback`. Their intended derived argument remains recorded in the
parent node because its derived hole is unchanged; they are not claimed as globally
pruned. Remove the duplicate proof import of KFlat, which is now publicly imported
because it appears in the existing statement. No other node or module is claimed
as globally pruned. The second reading also removes the redundant
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses` import from the item
and extracted data module: these declarations use the specialized tensor API already
publicly imported through `TensorClosed`, not the independent-universe API.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the auxiliary theorem
`SheafOfModules.module_pullback_tensor_iso_tail` in
`Sheaf.CategoryTheory.ModulePullbackTensorIsoE` cannot follow merely from an
underlying-set natural isomorphism for an arbitrary module lift. It does not require
compatibility with transported ring and module operations. Counterexample: use the
one-point site, inverse image the identity on sets, source ring R = k × k, and
RI = S = k. Let the module functor be restriction along the diagonal k → k × k and
c the identity of k. Its underlying sets agree, and scalar extension along c supplies
the required presentation. For M = N = R, the image of M tensor_R N has dimension
2 over k, whereas the tensor over k of the two images has dimension 4. Thus no tensor
isomorphism exists. That module is held by E2 and is not edited here. The new
construction instead retains the actual `AlgebraicInverseImage` operation-compatibility
axioms, which exclude this counterexample.

The item docstrings use node `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
but its current lean attachment names `Sheaf.Paper.ProEtaleCanonicalTensorPullback`,
a source file absent from this checkout. No node currently has this item's module as
its primary lean.module. The delivery leaves that existing lean attachment unchanged
and updates only the ordinary-construction part of the documented proof plan. The
new nodes have exact attachments to their delivered source files. This mismatch is
reported for the maintainer; it does not justify changing a target or the item signature.

An existing theorem producing some module lift would also not identify that lift
with the specified I.modules and L needed here. The ordinary normalization must be
constructed for the given data, or transported using a proved compatible identification.
The extraction of the data declaration only separates this dependency; it does not
change any mathematical object.

## New nodes

`def-weil-pbc-canonical-ringed-tensor-comparison` attaches the unchanged existing
structure to `Sheaf.Paper.RingedTopoiTensorComparisonData`. Its fields and declaration
are copied verbatim, and it is publicly reexported from the original module. Change
records: `coord/changes/A4-canonical-tensor-comparison-data.md` and
`coord/changes/A4-ringed-tensor-preadditive-proof-api.md`.

`lem-weil-pbc-canonical-ringed-tensor-comparison-construction` attaches the existence
conjunct to `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`. Its proof plan uses
inverse-image bilinear universality, the explicit scalar-extension formulas, and
transport/naturality. It is strictly a part of the original conjunction; the other
part is now proved. The node and docstring record the source and full proof in words.

## Second reading by A4

1. **Interfaces: pass after restoring exact whitespace.** Diffed the item against the
   shared version and compared all 15 original declaration headers with the project's
   declaration parser. Restored the extra space before `:=` in existsUnique. All existing
   theorem signatures are now byte for byte identical. The only declaration-kind change
   is the recorded proof-valued `ringedTensorPreadditive` abbreviation-to-theorem change;
   its proposition is identical and proof irrelevance identifies its value. The extracted
   structure, including all five fields, is byte for byte identical and publicly reexported.
   Both interface changes have change records. No target or other group's source is edited.

2. **Proof: pass with the three reported holes.** Read the complete delivered modules,
   particularly scalar_tensor_ext and the product/generalized-section uniqueness argument.
   The proof cancels an isomorphism obtained by sheafifying the tensor of the two
   sheafification units; it does not assume global surjectivity of those units. Sectionwise
   extension-of-scalars extensionality in each variable then suffices. The product comparison
   lifts arbitrary pairs after inverse image without assuming preservation of sections.
   Scratch `#print axioms` checks show only propext, Classical.choice and Quot.sound for
   every new helper checked, ringedTensorPreadditive, total and total_isIso. The assembled
   existsUnique and derived comparison additionally use sorryAx from the reported open
   statements. There is no hollow definition, arbitrary unproved witness selection,
   forbidden declaration or kernel bypass. The derived comparison chooses from an existing
   unique-existence statement; no new data choice is introduced.

3. **Split statement: pass as a decomposition.** The construction theorem is exactly
   the existence conjunct of the original conjunction; the substantial uniqueness proof
   remains in the item. It is therefore strictly a part of the argument, not a renamed
   copy of the whole statement. Its graph-compatible AlgebraicInverseImage hypotheses
   exclude the reported diagonal-restriction counterexample to the older arbitrary-lift
   tail. Checked the identity one-point case, zero rings and zero modules, and nonflat
   scalar extension: neither direction of the balanced formulas requires flatness or
   nonzero elements. Read the complete construction docstring and matching node, and
   checked the bilinear-adjunction route against
   [Stacks 03EL](https://stacks.math.columbia.edu/tag/03EL).
   Repeated leanfinder, loogle and grep searches with different terms; the hits give
   sectionwise scalar extension or continuous-site/free-module pullbacks, not this
   specified algebraic lift with its generalized pure-tensor normalization. The remaining
   construction is substantial and cannot be closed by one of these hits in a few minutes.
   One original hole is closed, one existence hole is added, and the original unit and
   derived holes remain: net zero, reported as a decomposition.

4. **Route and imports: pass after pruning and a local performance repair.** The ordinary
   construction and uniqueness follow the stated tensor/sheafification route. The derived
   hole and its planned K-flat representative route are unchanged, consistent with
   [Stacks 07A4](https://stacks.math.columbia.edu/tag/07A4). Read the unit's realized arrays:
   the proper-base-change statement and all three geometric steps are retained; this is
   a lower-level tool reduction. The only old parent proof dependency removed is
   lem-weil-pbc-ringed-topoi-module-pullback-tensor, already listed above. The proof-only
   construction, products, fully-faithful-adjunction and MonoidalFree imports are plain
   imports. The second reading proves ringedTensorPreadditive directly from the four
   additive tensor functor laws to avoid expanding the larger tensorClosed conjunction.
   A scratch removal test confirmed KFlatCoefficientUniverse is required for the
   WEqualsLocallyBijective instances appearing in the extracted structure signatures.
   Removed the redundant TensorProductOfUniverses import from both the item and the new
   data module; they use the specialized API already imported by TensorClosed. A local
   compile hit the 60-second limit. Profiling confirmed expensive elaboration through the
   monoidal structure; additionally keeping monoidalCategory locally irreducible beside
   totalIso compiled the unchanged signatures and bodies in 51.3 seconds, and the axiom
   audit copy in 47.1 seconds. The final version additionally scopes this reducibility
   boundary inside the sectionwise and uniqueness proof sections, leaving the unit
   statement's required unfolding unchanged; it passes without warnings in 56.3 seconds.
   The final definition explicitly supplies its existing site and ring parameters.
   These changes affect only elaboration, without splitting a proof or changing a
   definition's value. The unchanged ProjectionFormulaArrows consumer compiled against
   the overlay without errors or warnings (60.5 seconds including queue time).

5. **DAG: pass after two corrections.** Read all three delivered nodes and checked each
   proof_deps list against the union of its proof-step uses. Removed the construction
   node's misleading dependence on the existential module-adjunction theorem: its given
   sheaf adjunction and graph equations handle the specified lift directly. Corrected
   the parent total-comparison step's stale reference to the discarded arbitrary-lift
   tensor node. New nodes have sources, proof plans, searches, creation and blueprint
   fields, chapter/unit and exact Lean attachments. The pre-existing parent attachment
   mismatch remains explicitly reported above; its statement and attachment are unchanged.

Changed exact signature whitespace, the preadditivity proof, scoped local reducibility
attributes, explicit arguments, two redundant imports, the two proof-plan references, search records and this report. No additional
hole or mathematical statement was introduced by the second reading.
