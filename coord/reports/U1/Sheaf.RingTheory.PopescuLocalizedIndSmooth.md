## What changed

Closed `localized_target_is_ind_smooth` without changing its signature, visibility, or existing
docstring. The proof decomposes the localized arrow into residue-field fibres, proves each
fibre map regular, applies the assumed field case, and glues the resulting presentations.
The private proved helper `regular_of_geometricallyRegular` establishes the field regularity
step directly from the definition, using the canonical residue-field isomorphism and tensor
base-change cancellation. No regular-base-change theorem or Popescu theorem is imported.

Added two fully proved modules:

- `Sheaf.RingTheory.TotalFractionFiberDecomposition`: the compatible base and target ring
  isomorphisms, constructed from `reduced_noetherian_total_ring_fractions`, tensor-product
  distribution over finite products, and the localization/base-change isomorphism.
- `Sheaf.RingTheory.IndSmoothFiniteProductTransport`: finite-product induction from the
  already proved `Algebra.ind_smooth_prod`, plus explicit restriction of scalars along a
  base ring isomorphism and transport of colimit presentations.

Both enter the item's file as proof-only imports. Its original public imports are unchanged.
The two original proof-only imports are replaced by imports of the two proved helpers;
their declarations are still used inside those helpers. Updated the item's proof plan and
added nodes for both new public theorems. No existing interface, definition, or other module
is adapted, so no change record is required.

Validation: all three delivered modules compile together with `lcompile.py --all`, with no
warnings. The finite-product proof includes the zero-factor case. The decomposition allows
the zero ring and an arbitrary target algebra, including a zero target. The compatible ring
maps, rather than just separate abstract isomorphisms, are used in the final proof. No data
is defined from an arbitrary unproved existence theorem: the decomposition is an existential
theorem proved using the existing uniquely determined localization maps.

## Proved and sorry left

Holes closed: `localized_target_is_ind_smooth` (node
`lem-weil-pbc-popescu-standard-nonzerodivisor-aux-localized-ind`), one of one original holes.
No holes remain in the item's module. No holes are added or split off.

New public theorems proved without their own `sorry`:

- `total_fraction_fiber_decomposition`, node
  `lem-weil-pbc-total-fraction-fiber-decomposition`.
- `Algebra.ind_smooth_of_finite_product`, node
  `lem-weil-pbc-ind-smooth-finite-product-transport`.

The proof still depends on the existing named theorem
`reduced_noetherian_total_ring_fractions` in
`Sheaf.RingTheory.ReducedNoetherianTotalRingFractions`, whose proof is still `sorry` on this
base. The finite-product helper also depends through the proved `Algebra.ind_smooth_prod` on
the existing open theorem `Algebra.smooth_over_product_ring` in
`Sheaf.RingTheory.SmoothOverProductRing`. Neither existing hole is changed or re-proved
here. Axiom probes of the three public theorems show `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`; the field-regularity and scalar-transport helpers use only
the three permitted axioms. This is a complete proof
from the project's stated lower declarations, not an axiom-free proof of the entire closure.

## No longer needed

Removed direct imports `Sheaf.RingTheory.ReducedNoetherianTotalRingFractions` and
`Sheaf.RingTheory.FilteredColimitSmoothProduct` from the item's module. They remain needed
through the new decomposition and transport modules respectively, so neither module nor
its node is pruned from the transitive proof closure.

The separate direct reference to
`lem-weil-pbc-noetherian-finitely-many-minimal-primes` is unnecessary in this module:
the existing total-fraction theorem already supplies the finite enumeration. Its result
is still needed inside that theorem. The other original proof dependencies either remain
directly used as definitions or occur in the new helper nodes. The old direct dependencies
`lem-weil-pbc-reduced-noetherian-total-ring-fractions` and
`lem-weil-pbc-popescu-product` move into the two new helper nodes. Together with the
minimal-prime finiteness node just named, these are all old `proof_deps` absent from the
new direct list. No transitive module or mathematical dependency is claimed as pruned;
pruned: none.

Second reading removed redundant imports
`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian` (public) and
`Mathlib.RingTheory.Localization.BaseChange` (proof-only) from the new decomposition
module. Its remaining public imports already provide the statement vocabulary;
`Localization.Algebra` publicly imports `Localization.BaseChange`.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The existing plan was valid but did not yet have a directly
usable finite-product/transport interface or compatible fibre-decomposition interface.
Both are now proved from the available declarations. The field regularity step is proved
from the definition, rather than using the finite-type-only regular-base-change theorem,
which would not directly apply to the residue-field localization used here.

The existing docstring says nontriviality ensures a nonempty product. The delivered finite
product lemma handles the empty product as well, so the implementation does not need to
establish nonemptiness. The original theorem's `Nontrivial R` binder is preserved verbatim.

The cited Stacks source was read in the available copy at
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/smoothing.tex`, since the read-only
project clone does not carry that generated literature file. Node citations keep the
project-relative source path.

## New nodes

`lem-weil-pbc-total-fraction-fiber-decomposition`, module
`Sheaf.RingTheory.TotalFractionFiberDecomposition`: the compatible ring-theoretic
localization decomposition, independent of regularity and the field-case hypothesis.
It is fully proved and supports the first step of the item's argument.

`lem-weil-pbc-ind-smooth-finite-product-transport`, module
`Sheaf.RingTheory.IndSmoothFiniteProductTransport`: gluing over arbitrary finite product
ring decompositions, independent of fields, reducedness, Noetherianity, and regularity.
It is fully proved and supports the last step of the item's argument.

Both inherit chapter `sec-proper-base-change` and unit `sk-thm-p1`; the unit route is
unchanged. Searches of the DAG/blueprint found no existing declaration of either complete
interface. LeanSearch was unavailable; LeanFinder, Loogle, and source searches supplied
the ingredients recorded in the nodes. There are no change records.

## Second reading by U1

1. Compared the existing module with the repository using `diff`: the only changes
   are proof-only imports, the private proved field-regularity helper, and the original
   theorem proof. Its signature, visibility, public imports, and docstring are byte for
   byte unchanged. No existing definition changes; no change record or forced adaptation
   is needed. The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   Verdict: pass.
2. Compiled all three modules locally in import order, with no errors or warnings.
   Inspected every declaration, including the private functor and equivalence: no new
   `sorry`, prohibited declaration, hollow definition, or arbitrary choice of data from
   unproved existence. The chosen localization maps are uniquely determined; the choices
   occur within a theorem proof. Scratch-copy axiom probes show only the permitted three
   axioms, plus `sorryAx` from existing lower holes for the three public results and the
   finite-product induction. In particular scalar transport and field regularity are
   axiom-clean. Verdict: pass, conditional on the existing lower statements.
3. There are no split-off holes. Read both new proved statements and their docstring
   arguments; neither restates the item. Checked zero factors, zero base and target rings,
   one factor, arbitrary target algebras, and scalar compatibility. The finite-product
   theorem requires no fields or regularity; the decomposition requires no target
   Noetherianity. Independent LeanFinder and Loogle searches, plus source searches for
   scalar restriction, dependent products, and fraction decompositions, found ingredients
   already used here and no duplicate complete interface. Verdict: pass.
4. Read the proof downward from the original theorem, the imported total-fraction and
   binary-product declarations, the Mathlib tensor/localization interfaces, and the
   third paragraph of Stacks Tag 07F5 in the available local literature copy. The proof
   follows that reduction without using a general Popescu or regular-base-change theorem.
   Removed two redundant imports from the new decomposition module. The pruning report
   now explicitly lists all three old direct dependencies moved or subsumed. Checked
   `dag/units/sk-thm-p1.json`: its realized statement and steps remain unchanged; these
   helpers lie below that unit route. Verdict: pass.
5. Checked every Lean signature against its node's verbatim `lean.statement`; all match.
   Each `proof_deps` equals the union of the proof steps' `uses`. The proof plans describe
   the actual compatible tensor construction, scalar-equivalence transport, finite
   induction, and field-regularity argument. New nodes have the required source, searches,
   status, creation, blueprint, unit, chapter, and Lean records. Corrected the decomposition
   node's source place to mention Algebra Tag 02LX rather than the unrelated product
   lemma. Verdict: pass.

Changes in this reading: removed two redundant imports, corrected the decomposition
source-place metadata, completed the direct-dependency pruning list, and clarified the
existing smooth-product hole and axiom results. No proof or existing signature changed.
