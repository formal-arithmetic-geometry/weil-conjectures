## What changed

Proved `CategoryTheory.filteredComplex_single_differential_descent` in
`Sheaf.CategoryTheory.FilteredComplexSingleDifferentialDescent`, preserving its complete
signature and public visibility. The proof uses the existing representative-cover
construction and `Abelian.epiDesc`, then checks arbitrary representatives by subtraction
on an epimorphic pullback. The two fully proved private helpers identify the graded
projection kernel and show that a zero source page class has zero differentiated class.

Repaired the returned duplicate-theorem finding: removed the private helper
`CategoryTheory.differential_image_le_pullback` and replaced its sole application with
`CategoryTheory.image_le_pullback` from
`Sheaf.CategoryTheory.FilteredComplexBoundariesLECycles`. Added a proof-only
`import all Sheaf.CategoryTheory.FilteredComplexBoundariesLECycles` to make that existing
private theorem available; the original public import stays identical. The other proof
imports are `Sheaf.CategoryTheory.FilteredComplexDifferentialRepresentativesCover` and
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject`.

Updated the existing node's proof and proof origin to record reuse of this theorem.
The proof dependency set is unchanged. No definitions, public statements, additional
modules, or new nodes are introduced. The unit record has no realized statement or
proof steps in this node, and no unit route is bypassed.

## Proved and sorry left

Closed the only original hole:
`CategoryTheory.filteredComplex_single_differential_descent`
(node `lem-sp-filtered-complex-single-differential-descent`).

Holes closed: 1. Holes added: 0. Sorries left in the delivered module: none.
The remaining private helpers `CategoryTheory.graded_kernel` and
`CategoryTheory.filteredComplex_differential_zero_class` are fully proved.
This is a proof, not a decomposition.

The repaired module compiles locally without errors or warnings. Validation also
includes the delivery dry run and its axiom probe; nothing is pushed.

## No longer needed

Removed the duplicate local theorem `CategoryTheory.differential_image_le_pullback`:
its existing counterpart is reused. No original imports or proof dependencies are
removed. The representative-cover construction and all original definition and
boundary-inclusion dependencies remain needed. No module is asserted to leave the
targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the statement and proof of the private theorem
`CategoryTheory.image_le_pullback` in `FilteredComplexBoundariesLECycles`. The earlier
second reading incorrectly said that its private visibility prevented reuse through
an import. Lean's proof-only `import all` provides this access without changing the
public interface. The duplicate is now removed and the existing theorem is applied.
The old second-reading section has been removed because it describes the returned
version; the independent second reader must review the repaired version.

No mathematical error was found. The planned two successive descents are implemented
as one descent along the epimorphic cycle representative map followed by the source
boundary cokernel projection. The zero-class calculation proves boundary compatibility;
pullback subtraction proves the universal representative equation. The helper works
for all integer r, while the public positivity hypothesis stays unchanged.

## Second reading by Y3

1. **Interface preservation — pass.** Compared the complete delivered module with
   the repository version, and compared the text from the public theorem's name
   through its signature byte for byte. The category and abelian hypotheses,
   integer r and positivity hypothesis, related bidegrees, concrete cokernels,
   all four universally quantified representative maps, all three equations,
   and the conclusion are identical. The original public import and public
   visibility are unchanged. Only proof imports, two proved private helpers,
   the proof, and its explanatory docstring were added or changed. No definition,
   target statement, or other module changes; no change record is required.

2. **Proof and trust — pass.** Independently compiled the delivered module with
   lcompile.py: no errors or warnings. Searched the complete file for forbidden
   constructs and sorry: none. Compiled a scratch copy with explicit
   `#print axioms` for `CategoryTheory.graded_kernel`,
   `CategoryTheory.filteredComplex_differential_zero_class`, and
   `CategoryTheory.filteredComplex_single_differential_descent`. Each lists
   exactly propext, Classical.choice, and Quot.sound, with no sorryAx.
   Read the zero-class proof: monoLift factors through source boundaries;
   epic refinement lifts to their graded representatives; evaluated exactness
   identifies the graded kernel; d squared = 0 and the image/pullback adjunction
   place both differentiated summands in d(F^(p+1)); the target intersection,
   monicity, cokernel condition and epic cancellation give zero. The main proof
   kills the kernel of the epic page representative map, applies epiDesc, and
   uses subtraction after a pullback to verify every test-object representative.
   The witness supplied by the cover is eliminated inside an existence proof,
   not used to define data from an unproved mere-existence assertion.

3. **Split statements and reuse — pass.** No new holed statements or nodes are
   delivered; no split-off statement to test or close. Both private helpers
   are proved. Searched Sheaf, the upstream WeilConjectures checkout, and
   Mathlib's abelian and short-complex files for graded kernels, differential
   zero classes, descent, image-to-pullback containment and cokernel kernels.
   Checked the reused `image_le_pullback` in FilteredComplexBoundariesLECycles
   and `Subobject.exists_fac` in the upstream abelian subobject module.
   The returned duplicate `differential_image_le_pullback` is absent and its
   application now uses the existing private theorem through `import all`.
   Checked the boundary calculation at r=1 (incoming target step p+1),
   zero differential, and zero graded pieces: all give zero target classes;
   the helper's index calculation also works for nonpositive integer r.

4. **Route and pruning — pass.** Read the concrete subquotient definitions and
   the cover theorem, and compared the node and representative equation with
   the displayed Z, B, E and differential formulas in
   [Stacks Tag 012K](https://stacks.math.columbia.edu/tag/012K), immediately before
   Lemma 12.24.2. No finiteness or countable-sum hypothesis is used or needed
   in this componentwise finite-limit argument. The library and Mathlib search
   found the universal descent machinery already used, but no theorem replacing
   the filtered boundary calculation. Removing each added proof import in a
   scratch copy gives the expected unknown identifier: image_le_pullback,
   filteredComplex_differential_representatives_cover, or Subobject.exists_fac.
   All original proof_deps are used; `No longer needed` is complete and no module
   is claimed pruned. Opened dag/units/sk-prop-av-pqf-finite.json: its realized
   statement and sole step are empty, so this node replaces no realized unit
   statement or step. The recorded unit route is unchanged.

5. **DAG agreement — pass.** Parsed both node versions: only proof and
   proof_origin differ. Their three steps match, respectively, the proved
   zero-class calculation, the epic-kernel descent, and pullback subtraction.
   Their cited dependency union is exactly the unchanged proof_deps, including
   the representative cover. Checked each dependency's statement and Lean
   record against its use. No new node or unsupported changed field occurs.

**Second-reader changes:** appended this independent review and its validation
 evidence to report.md. No Lean or DAG repair was needed in the repaired version.
Holes closed remain 1, holes added 0, split off 0, and modules pruned none.
