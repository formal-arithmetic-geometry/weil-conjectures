## What changed

Proved `LocalizedModule.proj_away_degreeZero_exact` in
`Sheaf.Algebra.Module.ProjAwayDegreeZeroExact`, preserving its complete signature and existing
docstring. Its proof uses Mathlib's ordinary localization injectivity, exactness and
surjectivity, proves the two commuting chart identities from the fraction formulas, and
transports the resulting lifts through the injective alpha maps and their specified ranges.

Added `Sheaf.Algebra.Module.AwayDegreeZeroLift` with the proved general theorem
`LocalizedModule.away_degreeZero_lift`. It clears an equality of localized fractions and
projects the cleared equality onto the required homogeneous component of the original modules.
The private, proved `shift_component` helper establishes compatibility of additive homogeneous
projections with a degree shift by checking generators of the internal direct sum.
The new module is imported only for the target proof. Updated the target node's proof route.

Both modules compile without warnings using lcompile.py. The lifting proof explicitly handles
f=0 by subsingleton localization. The f≠0 branch covers zero numerators and images, arbitrary
annihilating powers and negative source components; its selected degree d*r is nonnegative.
The helper does not require positive d or scalar compatibility of the source grading. The
original target keeps all its hypotheses, including hd.

## Proved and sorry left

Proved the only original sorry: `LocalizedModule.proj_away_degreeZero_exact`
(node `lem-sc-p1-away-degreezero-exact`). Also proved `LocalizedModule.away_degreeZero_lift`
(node `lem-sc-p1-away-degreezero-lift`) and its private `shift_component` helper.
No sorry remains in either delivered module; no new sorry is added.

## No longer needed

Removed the proof import `Sheaf.RingTheory.GradedAlgebra.ShortExactGradedComponent`.
The node `lem-sc-p1-graded-degree-component-exact` and its module
`Sheaf.RingTheory.GradedAlgebra.ShortExactGradedComponent` are no longer needed by this item.
We do not construct a full internal grading on the localized modules: projecting a single
cleared fraction equality is enough. Ordinary localization
`lem-sc-p1-localization-short-exact` and the equal-degree fraction definition remain needed.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned construction of a full localized grading is
unnecessary. The target's unchanged docstring describes that longer plan; its updated DAG proof
and the new helper's docstring describe the actual denominator-clearing argument.

`blueprint_refs.py ancestor lem-sc-p1-away-degreezero-exact` returns None because the stage-3
node's created.item is a module name. For the new node, the blueprint origin is recovered from
the recorded parent links: away-degreezero-exact → proj-sheafification-exact → the imported
blueprint node lem-sc-p1-graded-resolution. Blueprint search for homogeneous localization found
no statement of the module lifting lemma. LeanSearch returned HTTP 500 and is recorded as
unavailable; LeanFinder, Loogle and source grep ran successfully. The local repository does not
contain the Stacks .tex files, so the proof-origin record is agent-written, retaining the
existing node's source reference; no literature was downloaded.

## New nodes

`lem-sc-p1-away-degreezero-lift` in
`dag/nodes/sec-picard-framework/lem-sc-p1-away-degreezero-lift.json` records the fully proved
homogeneous lifting theorem, in the new module `Sheaf.Algebra.Module.AwayDegreeZeroLift`.
It is strictly the lifting step for one graded map, with no short-exact-sequence hypotheses or
chart identifications. It supplies both the kernel lift and the surjectivity lift of the target.
No change record is needed: no existing definition or theorem signature changes.

## Second reading by X2

1. **Unchanged interfaces: pass.** Read both delivered modules and compared the existing
   module with the repository using `diff -u`. The complete signature and docstring of
   `LocalizedModule.proj_away_degreeZero_exact` are byte-for-byte unchanged. Its only changes
   are the proof and replacement of one plain proof import. No definition is changed and no
   change record is needed. The existing node differs only in `proof`, `proof_deps`, and
   `proof_origin`.
2. **Proof and axioms: pass.** Compiled both modules in import order with `lcompile.py --all`:
   no errors or warnings. Searched the delivered Lean for forbidden declarations and holes:
   none occur. Scratch copies with `#print axioms` show exactly `propext`, `Classical.choice`,
   and `Quot.sound` for the target, `away_degreeZero_lift`, and private `shift_component`.
   Thus the one original hole is closed without adding any lower hole.
3. **New lifting statement: pass.** The new theorem is fully proved, rather than a postponed
   restatement. It treats one graded map and one element in its localized range, with no
   short-exact-sequence or chart hypotheses. Checked the zero localization branch and the
   nonzero denominator degree calculation. Checked d=0, zero numerator, zero map, arbitrary
   annihilating powers, and negative source components: the chosen component d*r is always
   nonnegative, and the shift z+t is injective on integer degrees. Target scalar compatibility
   alone suffices because the additive map H=f^(l+m)*g shifts the source components into the
   target components. Its docstring and node spell out the full projection and fraction
   argument. Independent LeanFinder and Loogle searches used projection/degree-shift and
   homogeneous-preimage formulations, with Mathlib grep on decomposition maps and repository
   `rg` on both library roots. The nearest results are ring homogeneous localization and
   `DirectSum.decompose_map`/`GradedRingHom.exists_mem_of_surjective`; these require ring
   homomorphisms, not an additive map with a degree shift, and do not replace this module lift.
4. **Route and pruning: pass.** The target first uses the proved ordinary localization
   injectivity/exactness/surjectivity results, then proves commutativity from fraction formulas,
   then uses the proved homogeneous lift twice. The source projection argument avoids building
   a localized grading and uses no holed Sheaf lemma. All public imports supply signature
   vocabulary; localization exactness, decomposition, and the new lift are plain proof imports.
   The sole removed old proof dependency is `lem-sc-p1-graded-degree-component-exact`, and its
   module is listed under No longer needed. Read `dag/units/sk-thm-picard-duality.json`: neither
   that removed node nor this chart lemma is a realized unit step; no recorded unit route is
   bypassed or changed.
5. **DAG agreement: pass.** The exactness node's four steps match F/G localization,
   chart commutativity, kernel transport, and surjectivity transport in the Lean proof; its
   `proof_deps` is exactly their union. The lift node matches the stated hypotheses and
   conclusion, records its source, complete denominator-clearing proof, searches, blueprint
   ancestry, chapter/unit, creation record, and Lean declaration. Its only dependency is the
   equal-degree fraction definition. Both proof origins correctly identify the explicit
   agent-written argument.

Second reading changed only this report and added independent search records and scratch
axiom checks. No Lean or node repair was necessary.
