## What changed

Proved `AlgebraicGeometry.Scheme.Modules.IsAmple.exists_finite_common_power_cover` with
its signature unchanged. The proof selects a finite affine subcover, adds a degree-one
zero section, multiplies the positive degrees, raises the sections to the quotient
powers, transports them to the common degree and enumerates the nonempty finite type.
The extra zero section handles empty schemes without a separate geometric argument.

Added the proved module `Sheaf.AlgebraicGeometry.SectionNonvanishingZeroLocus` and
`nonvanishingLocus_eq_compl_support_zeroLocus`. Its private helper proves that a local
free generator gives a bijection on stalks using representatives and equality of germs.
The public theorem then compares maximal-ideal membership with the unit coefficient
and uses the source library's `basicOpen_coeff_eq`.

Both modules compile cleanly together through lcompile.py. No statement or definition
was changed. Read Stacks tags 01PS, 01VS, 01PW and 01CY online because the named local
literature files are absent. The unit sk-thm-p1's realized statements and steps are
untouched; this item is below that level. The finite common-degree route is retained.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_finite_common_power_cover`
(node `lem-weil-pbc-ample-finite-common-power-cover`).

Also fully proved
`AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_eq_compl_support_zeroLocus`
(node `lem-weil-pbc-section-nonvanishing-zero-locus`) and its private helper
`bijective_smul_germ`. No holes remain in either delivered module; no holes were added
or split off. This is a proof, not a decomposition.

## No longer needed

Removed the proof import `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
(module of `def-pur-sheaf-tensor-product`): the proof uses the source library's existing
monoidal tensor powers, tensorPowSection and tensorPowMulIso. It needs no separate
positiveTensorPower comparison or generic Sheaf tensor-product statements.

Removed the explicit proof import `WeilConjectures.AlgebraicGeometry.Modules.Invertible`;
its definitions remain visible through the unchanged public imports. This module and
the node `def-sc-invertible-module` remain mathematically needed and are not pruned.

No original proof-dependency node is wholly bypassed: ampleness, quasi-compactness,
invertibility and tensor powers are all used. The replacement proof import is
`WeilConjectures.AlgebraicGeometry.Modules.AffineComplement` for its proved
`compl_support_zeroLocus_tensorPowSection`; no proof of that result is needed here.

## Where the brief, the DAG or earlier work was wrong

The earlier plan called the stalk/zero-locus convention change elementary, but no
existing Lean declaration states it. We proved it in a separate module instead of
leaving a new hole. Existing `nonvanishing_section_trivializes` does not state the
required zero-locus identification and is not imported.

The source already proves the positive tensor-power support calculation, so no new
statement for preservation of nonvanishing under powers is needed. The empty-scheme
case can be handled uniformly by adding a zero section to Option t. All edge cases
(empty X, zero section, degree one, empty finite subcover) are included in the proofs.

Elaboration initially unfolded the chosen finite enumeration repeatedly when implicit
arguments to hc and iSup_comp were left as placeholders. Explicit index arguments and
an explicit family resolve the issue: no heartbeat increase or definition change is
needed. All final files compile within the single-file limit.

## New nodes

`lem-weil-pbc-section-nonvanishing-zero-locus` states and proves the precise comparison
needed in step 3 of the original plan, for any invertible module on any scheme.
It is strictly smaller than the cover theorem and contains no sorry. Blueprint
searches for nonvanishing/zero scheme and direct searches in the DAG found no existing
node with this precise identification. LeanSearch was unavailable; LeanFinder, Loogle
and grep were run and recorded. No change record is needed: only proof imports were
changed in the existing module, and its public interface is unchanged.

## Second reading by P1

1. PASS: Compared every delivered module with the read-only repository. The only
   existing declaration, `IsAmple.exists_finite_common_power_cover`, has a byte-for-byte
   unchanged signature; the two existing public imports are unchanged. There are no
   changed definitions, target statements, or undeclared interface changes.
2. PASS: Independently compiled both modules in import order with lcompile.py, cleanly
   in under six seconds each. Scanned both sources: no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or kernel-check bypass. Scratch #print axioms checks of
   the original theorem, the new public comparison theorem, and bijective_smul_germ
   each show exactly propext, Classical.choice, Quot.sound, with no sorryAx.
3. PASS: There are no split-off holes. The added comparison theorem is strictly
   smaller than the cover theorem, with a complete local proof and matching node.
   Read its germ-representative injection/surjection argument and maximal-ideal
   comparison. Checked empty schemes, zero sections, degree one, and empty finite
   subcovers; none needs an extra hypothesis. Independent LeanFinder search for
   stalk generators and zero-ideal support returned only basicOpen/germ criteria;
   Loogle IsFreeGenerator returned no matches. Direct rg searches, including
   FreeGenerator, GeneratingLocus and InvertibleSections, found no existing theorem
   identifying this stalk predicate with zero-locus support. GeneratesAt uses a
   neighbourhood-generator predicate and does not replace this identification.
4. PASS: The proof uses compactness, a finite subcover, positive common tensor powers,
   and the already proved source support lemma. It adds no alternative upper route.
   All four original proof-dependency nodes remain needed; no such node is pruned.
   Read sk-thm-p1's realized record: this auxiliary cover is below the unit steps,
   which remain intact. Removed a redundant public PullbackFreeGenerator import
   from the new module: its signature needs homOfGlobalSection, but the proof and
   signature already receive it through the necessary ClearDenominators import.
   The original TensorProduct import remains the only removed dependency-module
   import claimed as unnecessary; global target-closure pruning is not inferred.
5. PASS AFTER REPAIR: Checked node statements against the Lean, proof_deps against
   the union of step uses, new-node fields and the source-library lemmas. Replaced
   the broad lem-pc-zero-scheme-properties citation with the precise existing
   lem-pc-zero-scheme-zero-iff in the cover node and lem-pc-zero-scheme-ideal-local
   in the comparison node. The broad node's primary Lean declaration is unrelated
   to these local calculations. The proof texts still explicitly identify the
   already proved source support and coefficient lemmas; no new holes are needed.

Second reading changed only a redundant public import in the new module, the
original theorem's docstring to describe its actual uniform Option-family treatment
of empty schemes, and the two DAG dependency citations above. Proof bodies and all
statements remain unchanged. Closed one original hole; added zero holes; split off
zero holes. The two new helper declarations are proved, not additional holes closed
against the baseline. No change record is required.
