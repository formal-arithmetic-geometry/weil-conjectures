## What changed

Replaced the original hole in
`CategoryTheory.DecreasingFiltration.stableSubquotient_at_bounds` with a complete Lean
reduction through two cycle presentations. The proof calculates normalized cycles and
boundaries using the two outer bounds, transfers the supplied boundary inclusion along
these equalities, transports the quotient using a proved private helper
`quotient_iso_of_eq`, and composes the two presentation isomorphisms.
The existing theorem's signature and docstring are unchanged.

Added proof imports of `Sheaf.CategoryTheory.FilteredNormalizedQuotientPresentation`,
`Sheaf.CategoryTheory.FilteredCohomologyImagePresentation`, and
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`. The last supplies the image
of the top subobject. Each new module contains one public theorem representing a
strict part of the existing DAG argument. Updated the parent node's proof and
proof dependencies to match the Lean reduction.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.DecreasingFiltration.stableSubquotient_at_bounds` (one of one original
holes). Its proof contains no `sorry`. This is a decomposition, not an unconditional
proof: the delivery-local hole balance is 1 closed minus 2 added = -1, before
any ledger baseline or closure calculation. Two lower holes were added, and remain exactly as whole public theorem proofs:

- `CategoryTheory.DecreasingFiltration.normalizedStationaryQuotient_presentation`,
  node `lem-sp-filtered-normalized-quotient-presentation`. This is the quotient-of-quotients
  part of the argument, with no cohomology filtration or stationarity assumptions.
- `CategoryTheory.DecreasingFiltration.cohomologyImage_graded_presentation`,
  node `lem-sp-filtered-cohomology-image-presentation`. This identifies the graded
  cohomology image with the common cycle quotient, with no page index or outer bounds.

The private helper `quotient_iso_of_eq` is fully proved by substitution and proof
irrelevance. No other holes, axioms, definitions, or interface changes were added.
The earlier attempt's unused private boundary-inclusion helper was removed.

Validation: all three delivery modules compile locally in dependency order, with
no warnings. Edge-case inspection checks equal consecutive filtration steps (both
quotients zero), a zero next step (cycles modulo ambient boundaries), a zero filtration
step, and zero incoming and outgoing differentials (ordinary graded filtration).
Separate scratch Lean checks verify that the common denominator lies in the cycle
numerator, the equal-step and zero-next-step lattice simplifications, and the ambient
boundary inclusion from `d` squared equal to zero. No boundedness is needed for either
new statement. No arbitrary witness was used to define an object.

## No longer needed

Removed redundant direct proof imports of
`Sheaf.Algebra.Homology.FilteredComplexSubquotients` and
`Sheaf.CategoryTheory.Filtration`; both remain available through the unchanged public
import `Sheaf.CategoryTheory.FilteredCohomologyImage`, so this does not remove these
modules from the target import closure. No whole module is claimed as pruned.

The proof does not use `cohomologyImage_isFinite`, the finiteness conclusion in node
`lem-sp-filtered-cohomology-image-finite`, or a uniform/global filtration bound.
That node's module remains required for its actual `cohomologyImage` definition.
The old direct proof dependencies removed from the parent node are
`def-sp-abelian`, `def-sp-filtration`, and
`lem-sp-filtered-cohomology-image-finite`; their interfaces remain statement
dependencies or dependencies of the two presentation lemmas. Their modules are
not pruned from the import closure. `def-sp-filtered-complex-subquotients` remains
a direct proof dependency of the parent. In particular, removing the finite-image
node from the parent's direct proof plan does not remove its `cohomologyImage`
definition from the theorem's statement.

## Where the brief, the DAG or earlier work was wrong

The previous attempt left the original main theorem's hole inside a partial proof,
which is why it was rejected. This delivery closes that hole and states its two
unfinished categorical comparisons independently, with complete proof plans and nodes.
The existing DAG's steps 2 and 3 describe real comparisons but do not name any Lean
lemmas proving them. Neither the library search nor Mathlib search found those full
presentations, so they are the two new statements. LeanSearch returned an internal
server error; LeanFinder and local source searches were used instead.

No mathematical statement was corrected and no unit route was bypassed. The supplied
unit record has no realized nodes naming this comparison. The reduction follows the
same normalized quotient and cohomology image presentations as the parent's plan.

## New nodes

`lem-sp-filtered-normalized-quotient-presentation`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-normalized-quotient-presentation.json`,
states the parent's step 2 in
`lean/Sheaf/CategoryTheory/FilteredNormalizedQuotientPresentation.lean`.
Its proof plan uses the degreewise quotient projection, the modular identity, and the
abelian first isomorphism theorem. It neither assumes nor concludes the main theorem.

`lem-sp-filtered-cohomology-image-presentation`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-cohomology-image-presentation.json`,
states the parent's step 3 in
`lean/Sheaf/CategoryTheory/FilteredCohomologyImagePresentation.lean`.
Its proof plan identifies filtered cycles, their images in ambient cohomology, and
the kernel of the subsequent graded projection. Both nodes cite Stacks Tags 012Q
and 012P, inherit the parent's chapter and unit, and record all three search kinds.
There are no change records because existing public signatures and definitions stay
identical and the new modules are imported only for the main proof.


## Second reading by P2

1. **Interfaces: pass.** Compared the main module against the repository with
   `diff -u`. The signature and docstring of `stableSubquotient_at_bounds` are
   byte-for-byte unchanged. The sole existing public import is unchanged; all
   added imports are private proof imports. The other two modules are new.
   No definition, instance, target statement, or existing visibility changed;
   no change record is needed.
2. **Proof and axioms: pass as a decomposition.** Recompiled all three modules
   with `lcompile.py --all` in import order, without errors or warnings. A scratch
   copy with `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`
   and `sorryAx` for the main theorem and both open presentations. The fully
   proved private equality-transport helper uses only the three allowed axioms.
   The main proof rewrites the actual cycle/boundary formulas, transfers the
   inclusion, and composes the two independent presentations; it contains no
   hole. Exactly the two reported public presentation theorems remain `by sorry`.
   There are no definitions with holes, forbidden declarations, or arbitrary
   object constructions from unproved existence statements.
3. **Split statements: pass.** Read both statements and docstring arguments
   against the final quotient calculation of Stacks Tag 012Q and the image
   filtration definition of Tag 012P. The normalized presentation is a
   quotient-of-quotients statement, with no cohomology image; the image
   presentation is an ambient-homology comparison, with no page or bounds.
   Neither restates the original theorem. The denominator is contained in the
   cycle numerator because d squared is zero and the next step lies in the
   current step. Recompiled `scratchpad/EdgeCases.lean`, including that
   containment, equal-step and zero-next-step simplifications and B <= Z.
   Also checked zero current step and zero incoming/outgoing differentials.
   Equal steps give zero on both sides; a zero next step gives cycles in A
   modulo ambient boundaries in A. No extra boundedness assumption is needed.
   Fresh LeanFinder, Loogle and grep searches used inverse-image and nested-image
   terminology. LeanFinder found coimage/image isomorphisms; Loogle returned
   an unknown-identifier diagnostic for the query, hence no usable evidence.
   Local searches found `noetherIso`, `cokernelOfLEIsoExistsObj`, and
   `homologyIsoImageICyclesCompPOpcycles`, but none supplies either whole
   comparison. Those APIs still require the evaluation-kernel and image-map
   comparisons described in the docstrings; neither hole closes by a short
   application. Both open statements have matching nodes and full proof plans.
4. **Route and pruning: pass after report repair.** The reduction follows steps
   1--3 of the original plan and uses both newly named strict parts. The unit
   `sk-prop-av-pqf-finite` has empty `realized.statement` and `realized.steps`
   entries, so no realized unit node was bypassed. The main public import is
   needed by the signature; each new proof import supplies a used declaration.
   The new modules publicly import only modules needed by their statements.
   Completed the old-proof-dependency accounting above: removed direct edges
   are distinguished from definitions still needed indirectly. No whole module
   is pruned, and this delivery is not claimed as net hole progress.
5. **DAG: pass after metadata repair.** Read all three node files and compared
   the parent's proof steps, dependency union and origin with the Lean body.
   The two new nodes carry source, statement dependencies, proof plans,
   provenance, searches, creation data, blueprint ancestry, chapter/unit and
   Lean records as required. Their `lean.statement` fields were flattened
   rather than verbatim; replaced those two fields with the exact multiline
   signatures from their modules. No mathematical node statement changed.

Second-reading changes: corrected the two new node signature records and the
report's old direct dependency accounting; explicitly recorded the decomposition's
hole balance. No Lean proof repair was necessary. The scratch axiom probe was
removed before delivery.
