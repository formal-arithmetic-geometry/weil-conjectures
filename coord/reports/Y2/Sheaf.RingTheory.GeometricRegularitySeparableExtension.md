## What changed

Proved both remaining directions in
`lean/Sheaf/RingTheory/GeometricRegularitySeparableExtension.lean`, preserving every
existing signature and docstring. The existing iff proof is unchanged. Added the
fully proved private helper `finite_separable_ascent` for the finite case.

Ascent follows Stacks 07QH: regularity after finitely generated field extensions
proves geometric regularity of the finite base change; Mathlib etale base change
and cancellation prove its multiplication map smooth; smooth ascent proves the
finite case; finite intermediate fields form a directed cover for the general case.
Descent uses the existing separable/purely inseparable tensor-field theorem,
the finitely generated extension theorem, tensor cancellation and ring-equivalence
invariance of regularity. The latter extension theorem permits independently sized
universes for the test field and the base field without changing any statement.

Added proof-only imports `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra` and
`WeilConjectures.Mathlib.RingTheory.Etale.Field`. The import-direction tool confirms
that the latter introduces no cycle. Updated the proof plans and dependency lists
of all three existing nodes to describe the Lean argument. No new statements,
modules, definitions, public imports or axioms were added.

The local source copy of Stacks algebra.tex is absent on this machine. Read the
specified source at https://stacks.math.columbia.edu/tag/07QH. Searches actually run:
LeanFinder for geometric regularity under separable algebraic extension (only
geometrically reduced / separability APIs); Loogle for IsRegularRing (including
IsRegularRing.of_ringEquiv); ripgrep on Mathlib and both library roots for
geometric regularity and tensor cancellation. Local single-file compilation is
clean after import removal.

## Proved and sorry left

Proved `Algebra.isGeometricallyRegular_of_isSeparable` and
`Algebra.isGeometricallyRegular_of_isSeparable_rev`: 2 of the original 2 sorries.
The existing `Algebra.isGeometricallyRegular_iff_of_isSeparable` remains proved
and now uses these completed proofs. The private helper is fully proved.
No sorry remains in this delivery, and none was split off.

The proofs still rely on the existing named statements:
- `separableTensor_purelyInseparable_isField`
  (`lem-weil-pbc-separable-tensor-purely-inseparable-field`);
- `Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular`
  (`lem-weil-pbc-geometrically-regular-finitely-generated-extensions`);
- `Algebra.isGeometricallyRegular_of_smooth`
  (`lem-weil-pbc-geometrically-regular-smooth-ascent`);
- `geometricallyRegular_of_directed_subfields`
  (`lem-weil-pbc-geometrically-regular-over-subfields`).
Their sorries are existing downstream work, outside this delivery.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.FiniteSeparableMultiplicationEtale`:
`lem-weil-pbc-finite-separable-multiplication-etale` is not needed by either
proof. Its smooth multiplication conclusion is obtained directly from the
sorry-free `Algebra.Etale.of_finite_of_isSeparable`, Mathlib base change,
`Algebra.TensorProduct.commRight`, and `Algebra.Etale.of_restrictScalars`.

Removed proof dependency `lem-weil-pbc-finite-algebra-noetherian`: Noetherianity
of the finite tensor product comes from its regularity, already provided by
the finitely generated field-extension theorem.

Removed proof dependency `lem-weil-pbc-smooth-ring-map-base-change-composition`:
we use the Mathlib etale base-change instance and cancellation, then the
etale-to-smooth instance. The corresponding etale leaf nodes are recorded.

The backward node additionally no longer needs the unrelated forward-route
nodes `def-weil-pbc-separable-algebraic-extension`,
`lem-weil-pbc-geometrically-regular-over-subfields`,
`lem-weil-pbc-geometrically-regular-smooth-ascent`, or
`lem-weil-pbc-finite-separable-multiplication-etale`.
The forward node no longer needs
`lem-weil-pbc-separable-tensor-purely-inseparable-field`.
The subfields, smooth-ascent, finitely generated extension, and separable/purely
inseparable tensor-field modules remain imported because the combined proof uses them. No other original import is removed.
No module or node is deleted: these are dependencies pruned from this item's route.

## Where the brief, the DAG or earlier work was wrong

The two direction nodes each listed the union of both directions' dependencies,
rather than dependencies of their own direction. Their proof plans are now precise.
The earlier finite multiplication etale theorem is unnecessary for this proof:
Mathlib cancellation at the R-algebra level closes the required smoothness step.
The source's directed finite-field reduction and smooth-ascent route are retained;
no unit statement or realized unit step is bypassed.

The directional nodes have the parent iff node in stmt_deps to describe their
hypotheses. Thus the parent node retains an expanded argument, rather than adding
reverse proof edges to those nodes and creating a statement/proof dependency cycle.
The Lean iff assembly itself remains the original two direct applications.


## Second reading by Y2

1. **Unchanged public statements: PASS.** Read the entire delivered module and its
   repository diff. The signatures and docstrings of the two directional theorems
   and the iff are byte-for-byte unchanged. Both fields retain independent universes;
   R is still an arbitrary commutative Noetherian algebra, with both algebra
   structures and their scalar tower explicitly required. No definition, public
   import, target, change record, or other module is changed. The only additional
   declaration is the fully proved private finite-case helper.
2. **Proof and axioms: PASS, conditional on existing open dependencies.** Local
   lcompile.py compilation was clean (2.4 seconds). A scratch copy printing axioms
   for the helper and all three public theorems compiled cleanly (2.2 seconds).
   Each prints exactly propext, Classical.choice, Quot.sound, and sorryAx. The
   sorryAx comes from the four existing imported open theorems listed above;
   there is no sorry in this module and no axiom, unsafe, opaque, implemented_by,
   extern, hollow definition, or kernel-check bypass. These are two closed local
   sorries, not an assertion that the transitive theorem closure is sorry-free.
3. **Split statements: PASS (none).** No statement was split off or left sorry.
   Read the helper's finite-field proof: finiteness of L over k follows by the
   finite tower; geometric regularity of B includes its Noetherianity; the
   multiplication map is a k'-algebra map with composite R -> B -> R equal to
   identity, so etale cancellation applies. Checked identity extensions,
   characteristic zero (purely inseparable tests are trivial), positive
   characteristic, and the zero algebra: none requires an omitted nontriviality
   or perfectness assumption. The intermediate-field index is nonempty via
   bottom, directed via finite suprema, and covers all elements by separability
   implying integrality. Descent uses the tensor field and finite-generation
   theorem with independent universes, avoiding a universe restriction on the
   definition's test fields.
4. **Route and pruning: PASS.** Read Stacks 07QH at
   https://stacks.math.columbia.edu/tag/07QH and each imported Sheaf statement.
   The directed finite-field reduction and smooth ascent match that argument;
   Mathlib etale base change/cancellation replaces only the lower-level
   multiplication-etale lemma. Independently searched the library and Mathlib
   using regularity names, and queried Loogle for
   Algebra.Etale.of_restrictScalars (one exact hit, Mathlib.RingTheory.Etale.Basic).
   Read that lemma, baseChange, commRight, and cancelBaseChange in Mathlib.
   No existing complete geometric-regularity replacement was found. Each retained
   import supplies a statement, definition, theorem, or intermediate-field
   instance used here; all new imports are proof-only. Compared every old
   proof_deps list: the report names every removed edge (including direction-only
   edges). Read sk-thm-p1.json and its realized statement/steps: none of these
   pruned auxiliary nodes realizes a unit step, and the unit route is preserved.
5. **DAG agreement: PASS after a metadata correction.** Compared all three node
   JSONs with the repository: only proof, proof_deps, proof_origin differ.
   Each proof_deps equals the union of its steps' uses, and the etale and tensor
   leaf nodes describe the declarations actually applied. The iff expands both
   directional arguments in its plan to avoid a dependency cycle through the
   direction nodes' existing stmt_deps. There are no new nodes. The backward
   proof_origin had copied ascent/iff commentary; corrected it to describe
   descent alone.

Changed only the backward node's proof_origin note and an ambiguous retained-import
sentence in the report, then added this review. No Lean proof repair was needed.
