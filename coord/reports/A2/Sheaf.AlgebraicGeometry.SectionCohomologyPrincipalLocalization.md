## What changed

Replaced the sole proof hole of
`AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_isLocalized_away`
with a complete combining proof. Multiplication by the restricted scalar is a unit
in the endomorphism ring, proved directly using
`RingedSpace.isUnit_res_basicOpen` and `Module.End.isUnit_iff`.
`IsLocalizedModule.Away.mk_of_addCommGroup` combines this with the two separate
raw-cohomology assertions below. The denominator equation is explicitly converted
from the native scalar action on the principal open to restriction of scalars,
using `map_pow`; the kernel assertion supplies the third hypothesis.

Added the item’s proof-only imports
`Sheaf.AlgebraicGeometry.SectionCohomologyClearDenominators` and
`Sheaf.AlgebraicGeometry.SectionCohomologyKernelPowerTorsion`.
Each new module contains one public theorem, its complete proof in words and a
matching DAG node. Updated the item's proof route and dependencies.
All existing signatures, public imports and visibility are preserved.
Single-file compilation through `lcompile.py --all` succeeds for all three modules.

## Proved and sorry left

Closed the hole in
`AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_isLocalized_away`
(node `lem-pc-section-cohomology-principal-localization`). No direct hole remains
in the item. This is a decomposition, not a complete proof of cohomology
localization: one hole closed and two holes added (net minus one).
The scalar-action invertibility step is proved without a new hole.

The delivery adds exactly these two remaining holes:

- `AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_clearDenominators`
  (node `lem-pc-section-cohomology-clear-denominators`): only fraction surjectivity.
- `AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_kernel_pow_annihilates`
  (node `lem-pc-section-cohomology-kernel-power-torsion`): only the zero-kernel criterion.

Each hole is the entire proof of its public named theorem in its own new module.
Neither alone asserts the localization property. Edge cases checked mathematically:
for a=0 the principal open is empty and the kernel is killed by exponent one;
for a a unit restriction is an isomorphism; empty W, zero F and q=0 are included.
The natural-language proofs explain the canonical resolution comparisons and the
separate surjectivity/injectivity uses of `invertS_cohomology`.

## No longer needed

Removed the item's direct proof import `Sheaf.AlgebraicGeometry.InvertSCOhomology`.
Its node `lem-sc-invert-s-cohomology` is still needed in the proofs of both new
intermediates; it is not claimed as a globally pruned module or mathematical lemma.
The item's old direct proof dependency edges to `def-pc-morphism-conventions`,
`def-weil-pbc-flat-base-change-open-choices` and `lem-sc-invert-s-cohomology` are
replaced by the two new intermediate nodes. The definitions remain statement
dependencies and the invert-s argument remains below the intermediate nodes.
No other existing module or unit step is claimed as unnecessary.

## Where the brief, the DAG or earlier work was wrong

The plan suppresses the tensor-unit identifications and their compatibility with
canonical resolution-section restriction. The available `invertS_cohomology`
interface is an additive equivalence on twisted cohomology, not directly a linear
localization assertion for this raw presheaf. The two new clauses make the remaining
work explicit without changing a statement or using sheafification circularly.

The library also states the same full assertion as
`higherImageCohomologyPresheaf_isLocalized` in
`Sheaf.AlgebraicGeometry.HigherImageCohomologyPresheafLocalization`.
At first its compiled object was absent. Once the green snapshot supplied it,
direct reuse compiled. However, the refreshed source dependency graph showed that
another delivery had made that duplicate import this item. The final dry run
therefore rejected direct reuse as a two-module cycle. The delivered decomposition
uses neither the duplicate nor any sheaf-level assertion depending on this item.
No existing dependency was recopied or adapted.

Searches: LeanFinder found ring-section torsion and tilde fraction results;
Loogle found the localized-module API; LeanSearch returned an internal-server-error
and was recorded as unavailable; direct source/DAG/blueprint searches found no
separate raw-presheaf lifting or kernel statements. The sheaf-section assertions
already in the library depend on raw localization and cannot be used circularly.
Sources read: https://stacks.math.columbia.edu/tag/09MR and
https://stacks.math.columbia.edu/tag/01E4. The unit record has no realized node for
this item; the tensor-unit localization route is preserved below the new nodes.

## New nodes

`lem-pc-section-cohomology-clear-denominators` in
`dag/nodes/sec-picard-framework/lem-pc-section-cohomology-clear-denominators.json`
states only that a power times a class lifts. Its proof specializes surjectivity of
the canonical fraction comparison, combines a finite sum into a single fraction,
and uses the canonical numerator equation. Lean module:
`Sheaf.AlgebraicGeometry.SectionCohomologyClearDenominators`.

`lem-pc-section-cohomology-kernel-power-torsion` in
`dag/nodes/sec-picard-framework/lem-pc-section-cohomology-kernel-power-torsion.json`
states only that a class in the restriction kernel is killed by a power. Its proof
specializes injectivity of the canonical fraction comparison and then uses the
existing `cohomologyFraction_eventually_zero` theorem. Lean module:
`Sheaf.AlgebraicGeometry.SectionCohomologyKernelPowerTorsion`.

No interface change record or forced adaptation is required.

## Second reading by A2

1. Interface preservation: PASS. Compared every delivered module with the repository.
   The only existing module changes its proof and plain imports; its existing theorem
   signature is byte-for-byte identical, as are its public imports and visibility.
   The other two modules are new. No definition or target statement changes, and no
   change record is needed.
2. Proof and trust: PASS as a decomposition. All three files compile locally in import
   order, with no errors or warnings. Scratch copies with `#print axioms` show exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for each declaration.
   The latter is expected from the two explicitly reported open theorems. Scanned
   the three files: no forbidden declaration or attribute and no data definition.
   The sole direct holes are the whole proofs of the two new public named theorems.
3. Split statements: PASS. Read both statements, docstring arguments and nodes.
   Each is a strictly smaller clause of localization: one gives fraction surjectivity,
   the other the zero-kernel criterion; neither asserts the full localization property.
   Checked zero and nilpotent scalars (empty principal open), unit scalars, empty W,
   zero coefficients and degree zero. The tensor-unit specialization of
   [09MR](https://stacks.math.columbia.edu/tag/09MR) gives each clause, and the
   resolution evaluation in [01E4](https://stacks.math.columbia.edu/tag/01E4)
   identifies precisely the restriction map. Read `invertS_cohomology` and
   `cohomologyFraction_eventually_zero`, including their canonical-map equations.
   Independent LeanFinder search used distinguished-open extension phrasing; its
   results concern structure-sheaf sections, not arbitrary raw cohomology. Loogle
   search found general Away/local-algebra APIs; msearch grep and direct rg of
   lean/ found no independent raw lifting or kernel theorem. The full duplicate
   `higherImageCohomologyPresheaf_isLocalized` imports this item and cannot be used.
   Neither remaining hole has a closure in a few minutes from the available APIs.
4. Route and pruning: PASS after repair. The combining proof uses the direct unit
   argument and Mathlib’s `IsLocalizedModule.Away.mk_of_addCommGroup`, followed by
   the two clauses with the necessary scalar-restriction `map_pow` conversion.
   All old direct proof-dependency edges are accounted for in No longer needed.
   No module is claimed globally pruned. The unit’s realized statement and step
   arrays are empty; no realized unit node is bypassed. The two new modules had
   omitted the plain imports for their recorded unfinished proof plans. Added
   `Sheaf.Topology.RestrictInjectiveResolution` and
   `Sheaf.AlgebraicGeometry.InvertSCOhomology` to each, plus
   `Sheaf.AlgebraicGeometry.CohomologyFractionEventuallyZero` to the kernel module.
   Fraction-presentation definitions arrive through InvertSCOhomology’s public import.
   These imports keep the documented lower route in the actual import closure;
   the statements’ public imports are unchanged and no proof import is public.
5. DAG agreement: PASS. The existing node changes only proof, proof_deps and
   proof_origin. Its two dependency edges match the Lean proof. For all three
   nodes, proof_deps is exactly the union of step uses. Checked the new node fields,
   matching declarations and signatures, sources, searches, creation metadata,
   chapter and unit. Their plans and the added proof imports now agree.

Second reading changed only the missing plain proof-dependency imports, spacing
before `:=` in the unit-action proof, and this report. No mathematical statement,
proof route or hole count changed: one original hole closed, two strictly smaller
holes added, net minus one. This remains a decomposition, not a completed proof
of cohomology localization. Recompiled the edited delivery and checked axioms.
