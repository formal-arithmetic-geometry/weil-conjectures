## What changed

Replaced the proof of `Algebra.artinian_lifting_conormal_split_mod_maximal` without
changing its signature, public imports, or existing definitions. The main theorem now
uses Mathlib's Artin--Rees equality at `N = c + 2`, proves the required containment
`m^N ∩ J ≤ mJ`, obtains a truncated section, and applies a residue-kernel comparison.
The proved private helper `Algebra.residue_retraction_of_kernel` constructs the induced
quotient map, proves its injectivity, extends scalars to the residue field, and uses
`IsSemisimpleModule.extension_property` to extend the identity along this injection.
Restricting scalars gives the retraction and the exact equation originally requested.
This final step needs no finite generation or freeness assumption.

Added two modules, each stating one strictly intermediate theorem:
`Sheaf.AlgebraicGeometry.ArtinianLiftingTruncatedSection` covers the Artinian quotient,
finite-length filtration, localization and section construction (original steps 1--3
and universe transport). `Sheaf.AlgebraicGeometry.TruncatedSectionConormalResidueKernel`
covers the square-zero retraction and differential comparisons (original steps 4--5),
assuming an explicit intersection bound rather than any lifting hypothesis. Both have
complete proof descriptions, sources, DAG nodes and recorded Mathlib searches.
The unit's realized route is unchanged; neither new step bypasses a realized unit node.

Validation: all three modules compile together through `lcompile.py --all`, with no
compiler errors or warnings. The Artin--Rees and linear-algebra combination is fully
proved in Lean; no partial proof or definition contains a hole. Small-case checks:
`J = 0` gives identity quotient maps and a zero conormal source; `N = 1` in the
section theorem gives `C/m -> C/m`; `N = 2` in the comparison is valid and uses
exponent 1 in the differential-power lemma. The comparison retains the essential
intersection hypothesis: with `J = (t^2)` in `k[t]_(t)` at `N = 2` it fails, so
that example is excluded by the bound, not silently by a strengthened ring hypothesis.
The universe `v` remains arbitrary and the section node explicitly explains ULift tests.

## Proved and sorry left

Original hole closed: `Algebra.artinian_lifting_conormal_split_mod_maximal`
(`lem-weil-pbc-artinian-lifting-conormal-mod-maximal`), 1 of 1 original sorries.
There is no `sorry` left in the item's module. Its new private helper
`Algebra.residue_retraction_of_kernel` is fully proved.

Two holes added, each in its own new module:

- `Algebra.artinian_lifting_truncated_section`
  (`lem-weil-pbc-artinian-lifting-truncated-section`).
- `Algebra.truncated_section_conormal_residue_kernel`
  (`lem-weil-pbc-truncated-section-conormal-residue-kernel`).

This is a decomposition, not an axiom-free proof of the original theorem:
1 upper hole closed, 2 strict intermediate holes added, net -1 in hole accounting
before considering separately held dependencies. The first conclusion is an algebra
section of explicit Artinian quotients. The second has no lifting tests or localization
hypothesis and concludes a kernel-membership implication, rather than the requested
retraction. The main theorem genuinely combines them with a proved Artin--Rees bound
and proved residue-field linear algebra. Existing dependency holes are unchanged.

## No longer needed

Removed direct proof imports from the item's module:
`Mathlib.RingTheory.Smooth.Kaehler`, `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`,
`Sheaf.Paper.ArtinianIdealLengthOneFiltration`, and
`Sheaf.RingTheory.KaehlerDifferentialsModPowerIdeal`.
They are needed by the corresponding intermediate proof plans and are imported there;
this is redistribution of dependencies, not pruning them from the targets' closure.
`Mathlib.RingTheory.Filtration` remains and is actually used in the main proof.
Removed redundant newly added direct imports `Mathlib.Algebra.Module.Torsion.Basic`
and `Mathlib.RingTheory.SimpleModule.Basic` during second reading; their needed
declarations and instances are already available through the retained imports.

Original direct proof dependencies transferred to the new intermediates:
`lem-weil-pbc-noetherian-local-quotient-artinian-local`,
`def-weil-pbc-localization-at-prime`,
`lem-weil-pbc-artinian-ideal-length-one-filtration`,
`lem-weil-pbc-local-ring-unit-criterion`,
`lem-weil-pbc-square-zero-section-conormal-retraction`,
`def-weil-pbc-kahler-differentials`, and
`lem-weil-pbc-kahler-differentials-mod-power-ideal`.
Only `lem-weil-pbc-artin-rees` remains a direct old proof dependency.
These seven dependencies are still used transitively, so none is globally pruned.
No original dependency node or module is claimed globally pruned: the original planned
Artinian quotient, filtration, unit criterion, square-zero retraction, Artin--Rees and
differential comparison nodes remain necessary through the two new nodes.
No public import was removed, and no change to another holder's module is needed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt said that the needed interfaces could not be stated and compiled.
They can: the section uses `Ideal.Quotient.factorₐ`, and the comparison is stated as
kernel membership with a precise Artin--Rees containment. They are both strict parts
of the original argument. The absence of already proved interfaces does not prevent
the requested stage-3 decomposition.

The local clone lacks `literature/stacks-project/algebra.tex`; the cited Tag 02HT
was read directly at `https://stacks.math.columbia.edu/tag/02HT`. Its finite filtration,
localization-to-section and final conormal comparison paragraphs justify the split.
Mathlib's `Ideal.exists_pow_inf_eq_pow_smul` supplies the bound without a new hole.
The choice `c + 2` handles the possible Artin--Rees index zero and ensures both
differential comparisons have positive exponents. The generic retraction helper uses
`Ideal.Quotient.field` explicitly because it is not a typeclass instance on a raw
ideal quotient. No definition or existing statement was changed or disputed.

LeanSearch returned Internal Server Error for both new-node queries, recorded as
unavailable with no absence verdict. LeanFinder returned related formal-smoothness
lemmas requiring stronger hypotheses. Loogle found the exact square-zero retraction
lemma, and grep found the tensor comparison interfaces but no complete strict
intermediate result. The existing Sheaf differential-power and ideal-filtration
statements remain the planned dependencies, even where they rest on other holes.

## New nodes

`lem-weil-pbc-artinian-lifting-truncated-section`, in
`dag/nodes/sec-proper-base-change/`, records the conclusion of original steps 1--3
and universe transport: the canonical quotient map at each positive N has an
R-algebra section. Its proof cites the existing Artinian quotient, length-one
filtration, localization and local-unit nodes. Module:
`Sheaf.AlgebraicGeometry.ArtinianLiftingTruncatedSection`.

`lem-weil-pbc-truncated-section-conormal-residue-kernel`, in the same chapter,
records original steps 4--5 after Artin--Rees: an R-algebra section at N >= 2 and
`m^N ∩ J ≤ mJ` imply that the reduced conormal map has zero kernel. Its proof
cites the existing square-zero-section retraction, differential-power comparison
and module base-change nodes. No Noetherian hypothesis is needed once the bound
is supplied. Module: `Sheaf.AlgebraicGeometry.TruncatedSectionConormalResidueKernel`.

Updated only `proof`, `proof_deps` and `proof_origin` in the original node to match
the implemented route. No change records or forced adaptations are necessary.

## Second reading by D2

1. **Interfaces: PASS.** Read the diff against the repository module and compared
   the existing theorem signature byte for byte, from `theorem` through its final
   conclusion before `:= by`: identical. All five existing public imports,
   visibility, and the existing docstring are unchanged. No definition is changed
   or added, and no change record or forced adaptation is required.
2. **Proof and trust: PASS as a decomposition.** Compiled all three modules in
   dependency order with `lcompile.py --all`, and compiled scratch copies with
   explicit `#print axioms` for all four declarations, including the private
   helper. The helper uses only `propext`, `Classical.choice`, `Quot.sound`.
   The main theorem and the two intermediate theorems additionally use `sorryAx`,
   exactly as reported. There are two textual holes, each the entire proof of
   its public named intermediate theorem; no forbidden declaration, hidden hole,
   or data definition chosen from mere unproved existence occurs. The section
   witness is eliminated only inside the main existential theorem proof.
3. **Intermediate statements: PASS.** Read [Stacks Tag 02HT]
   (https://stacks.math.columbia.edu/tag/02HT), especially its truncated Artinian
   quotients, successive small extensions, localization and section construction,
   and tensor comparison paragraphs. In the section theorem, local surjectivity
   gives J contained in m, Noetherianity makes the truncations Artinian, and
   every filtered test retains inverse-image maximal ideal q. No finite-type
   assumption on A is needed for these steps. Universes are handled by ULift.
   In the kernel theorem, the square-zero retraction is linear over F because
   its kernel is annihilated by the quotient kernel; tensoring preserves the
   retraction equation. The modular law and explicit hAR identify its reduced
   source with J/(J squared + mJ). The two differential-power comparisons use
   positive exponents N-1 and 1, respectively, and identify the target and map
   on classes represented by j. Neither Noetherianity nor freeness is needed
   there. Checked J=0, N=1 for sections, N=2 for comparison, and the excluded
   J=(t squared), N=2 example: hAR fails because t squared is not in (t cubed).
   The source S is nontrivial by locality; a zero target ring cannot introduce
   a degenerate extension. Both holes are strict portions of the argument,
   with complete docstring proofs and matching nodes, not a renamed conclusion.
   Repeated LeanFinder searches using right inverses, length-one kernels and
   residue-field tensor injections. Hits such as
   `FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` require formal smoothness,
   while `FormallySmooth.iff_injective_lTensor_residueField` requires a formally
   smooth presentation with finite free differentials. Neither applies here.
   Grep of Sheaf, WeilConjectures and Mathlib's Smooth/Extension sources found
   the existing square-zero retraction and infinitesimal comparison interfaces,
   but no theorem covering either new intermediate under these hypotheses.
4. **Route and pruning: PASS.** The main Lean proof really establishes the
   Artin--Rees bound at c+2 and combines both intermediates with the proved
   residue-field splitting helper. Read `dag/units/sk-thm-p1.json` realized
   statement and all four step lists; none is bypassed by this below-unit split.
   Checked every old proof dependency: Artin--Rees remains direct; the other
   seven remain through the two new nodes and are explicitly listed above.
   The four old proof imports move to the intermediates, rather than leaving
   the target closure. Removed two redundant newly added proof imports after
   a scratch compile without them succeeded; retained all public imports.
5. **DAG agreement: PASS.** The original node changes only `proof`,
   `proof_deps`, and `proof_origin`. Its three direct dependencies agree with
   the calls in the main proof. Read both new nodes in full: their signatures,
   source, hypotheses, proof steps, dependency union, provenance, searches,
   created item/group, chapter/unit, and Lean records match their modules.
   Existing dependency declarations were read, notably the ideal filtration,
   Artin--Rees equality, square-zero retraction, and differential-mod-power
   statement. No unit realization or existing statement record was changed.

Second reading changed only the removal of two redundant private proof imports
and this report's explicit dependency-transfer list and independent review.
The two substantial intermediate holes cannot be closed by the search hits in
an immediate application; this delivery remains 1 upper hole closed, 2 added,
net -1, with no globally pruned module.
