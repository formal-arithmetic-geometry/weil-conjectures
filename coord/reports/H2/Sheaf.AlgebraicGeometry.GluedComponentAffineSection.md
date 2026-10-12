## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_glued_component_affine_section` with its
original signature and docstring. The proof pulls T back to each component, uses the existing
finite-set affine-section theorem, proves discreteness of every overlap directly, and invokes
`glueComponentLineBundles`. It transports component ampleness across the restriction
isomorphisms and applies the proved compatible-section affine-locus lemma.

Added two modules with complete proofs and corresponding nodes:
`Sheaf.AlgebraicGeometry.AmplePositiveTensorPower` and
`Sheaf.AlgebraicGeometry.AffineLocusOfCompatibleComponentSections`.
Both have one public theorem, no new definitions and no holes. The previously duplicated
private helper calculations are reused from existing modules via `import all`; no copies of
those helpers remain in either module. No existing public import changed.

Positive-power ampleness uses local free frames, the existing source-library section-power
construction, a bijective scalar map on stalks, and `isUnit_pow_iff`. The affine-locus theorem
uses the existing `nonvanishing_tensorPullback` theorem,
explicit restricted closed immersions and `isAffine_of_finite_closed_cover`. It also transports
the fixed section along the inverse right unitor to L.tensorPow 1.

The existing unused existential witness name `hL` triggers the unused-variable linter once the
proof is complete. Suppressed only that linter for this theorem; kept its original binders.
Updated the assigned node's proof, dependencies and origin to match the compiled assembly.

Compiled all three modules in import order with lcompile.py, without errors or warnings.
Checked empty covers, empty T, zero sections and exponent one in the arguments: the general
finite closed affine-cover theorem handles the empty-cover case, and the positive exponent
hypothesis is essential for preserving the locus under section powering.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_glued_component_affine_section`
(node `lem-sc-glued-component-affine-section`).

Also fully proved:
- `AlgebraicGeometry.Scheme.Modules.isAmple_positive_tensorPow`
  (node `lem-sc-ample-positive-tensor-power`).
- `AlgebraicGeometry.Scheme.Modules.affine_locus_of_compatible_component_sections`
  (node `lem-sc-affine-locus-compatible-component-sections`).

No sorry remains in the assigned module or either new module. No holes were added or split
off. Existing imported theorem dependencies can still rest on their existing holes; this
report claims closure of this module's hole, not axiom-free closure of all targets.

## No longer needed

Removed the assigned module's direct proof import
`Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover`; the new proved affine-locus module
imports and uses it, so its node `lem-sc-closed-affine-union-affine` and module remain needed.
The old direct proof dependency `def-weil-pbc-ample-invertible-module` is no longer
listed among the assigned node's proof dependencies: it remains a statement dependency
and is used within the positive-power helper. The old direct dependency
`lem-sc-closed-affine-union-affine` is used through the affine-locus helper.
No dependency module is claimed pruned from the targets' import closure. The original planned
finite-set section, component-gluing, ampleness criterion and finite closed affine-cover
arguments are all retained. No unit statement or realized proof step is bypassed.

The second reading additionally removed direct proof imports
`Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`,
`Mathlib.LinearAlgebra.TensorProduct.Quotient`, and
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` from the new affine-locus helper.
Their calculation is supplied by the existing proved
`Sheaf.AlgebraicGeometry.NonvanishingTensorPullback`; its node
`lem-sc-nonvanishing-tensor-pullback` replaces the direct fibre-comparison dependency.
These modules remain needed transitively; this is local proof simplification, not global pruning.

## Where the brief, the DAG or earlier work was wrong

No disputed statements or source errors were found. An earlier second reader removed
an unreported private-to-public change in AmpleIso. The current reader also found
and removed a repeated pullback nonvanishing calculation; see the final reading below.
The original plan did not expose
positive-power ampleness or the final compatibility-to-affineness assembly as separately
usable declarations; both are now proved.

The helper calculations for stalk linearity, nonvanishing under an isomorphism, and
bijective scalar germs are provided by the existing `AmpleIso` and
`SectionNonvanishingZeroLocus` modules. They are imported with `import all` so their
existing private declarations remain accessible without duplicate statements.

Verified the mathematical sources directly: [Stacks 01PT](https://stacks.math.columbia.edu/tag/01PT)
is the positive-power ampleness result; [Stacks 09NX](https://stacks.math.columbia.edu/tag/09NX)
contains the component construction; [Stacks 09NL](https://stacks.math.columbia.edu/tag/09NL)
is the finite closed affine-cover result.

## New nodes

`lem-sc-ample-positive-tensor-power` states forward preservation of absolute ampleness under
positive tensor powers, sourced to Properties 01PT. Its full Lean proof keeps the original
pointwise affine opens and raises the witnessing sections. Empty schemes are included;
exponent zero is excluded. It is a genuine auxiliary theorem, not a restatement of the
assigned existential construction.

`lem-sc-affine-locus-compatible-component-sections` states the final affine-locus argument
for a fixed global bundle and section with compatible affine component loci. It assumes
neither reducedness nor ampleness nor finiteness/closedness of T; all bundle construction is
input. Its complete Lean proof uses the fixed section's open locus, the finite restricted
closed cover, and the right unitor. It cannot produce the bundle or compatible sections
required by the assigned theorem.

No change records: no existing definition or statement was altered.


## Earlier second reading (a previous round; superseded)

1. Compared the delivered existing module with the repository version and checked its
   declaration header separately: the existing signature and docstring are byte-for-byte
   unchanged. Only imports, the proof, and a theorem-scoped unused-variable linter setting
   changed. The two other modules are new. No definition or target statement changed;
   no change record is necessary. Verdict: pass.
2. Compiled all three files in import order with lcompile.py, without errors or warnings.
   Scanned all delivered Lean for forbidden declarations and sorry: none. Printed axioms
   in scratch copies: isAmple_positive_tensorPow uses only propext, Classical.choice,
   Quot.sound; affine_locus_of_compatible_component_sections and
   exists_glued_component_affine_section additionally use sorryAx from existing imported
   dependencies. No data definition or arbitrary existence witness was added. The existing
   chosen pullback adjunction is pinned by its sectionwise unit formula. Verdict: pass.
3. There are no statements left sorry or split-off holes. Read both new proved statements
   and their full proofs, including stalk scalar bijectivity, faithful residue-field
   extension, restricted closed covers and section transport. Empty cover/empty scheme,
   empty T, zero sections and k=1 are handled; k=0 is excluded appropriately. Repeated
   semantic Mathlib searches with different wording and searched the library for power,
   isomorphism and pullback nonvanishing results. No existing theorem proves either full
   new statement. Existing nonvanishing and section-power results are used where available;
   private helpers do not duplicate public declarations. Verdict: pass.
4. The assembly first uses the finite-set section theorem and gluing theorem, then the
   proved smaller ampleness and affine-locus arguments. The former unit route is retained:
   sk-thm-curveestimate.realized is unchanged, and no unit statement or step is bypassed.
   Inspected imports and tested privatizing ProjectionFormula: Lean rejects the public
   signature without its tensor-power invertibility instance, so that public import is
   necessary and was retained. The old direct dependencies are accounted for under
   No longer needed; the finite closed cover result remains used transitively. No module
   is claimed pruned. Verdict: pass.
5. Checked all three node records against declaration headers and actual proof steps.
   Existing-node changes stay in proof, proof_deps and proof_origin; new nodes have source,
   searches, creation, blueprint, chapter/unit and Lean records. Dependencies match the
   gluing, ampleness transport, section powering, fibre comparison and affine-cover route.
   Both new nodes are fully proved auxiliary steps, not restatements of the item.
   Verdict: pass.

Second reading changed the report only: clarified why ProjectionFormula must be public,
listed both old direct proof dependencies now used through helpers, and recorded the
independent compilation, axiom and mathematical checks. No Lean repair was needed.


## Earlier second reading (a previous round; superseded)

1. Compared every delivered existing module with the read-only repository. The assigned
   theorem's signature and docstring are byte-for-byte unchanged. Found an extra sandbox
   duplicate helper statements in both new modules (the earlier return). Deleted those
   copies and inserted `import all Sheaf.AlgebraicGeometry.AmpleIso`; the positive-power
   module also imports `import all Sheaf.AlgebraicGeometry.SectionNonvanishingZeroLocus`.
   Existing calls remain unchanged and resolve to the imported private helpers. The final
   delivery changes no existing definition, statement or visibility. Verdict: pass after
   repair.
2. Independently compiled all three final modules in import order through lcompile.py,
   with no errors or warnings. Scanned the delivered Lean: no sorry or forbidden declaration.
   Printed axioms from a scratch module importing the final compiled overlay:
   isAmple_positive_tensorPow uses only propext, Classical.choice and Quot.sound;
   affine_locus_of_compatible_component_sections and exists_glued_component_affine_section
   also use sorryAx from existing dependencies. No new data definitions or arbitrary
   unproved existence witnesses occur. The selected pullback adjunction has its unit fixed
   sectionwise by its existential specification. Verdict: pass.
3. No split-off holes remain. Read both new statements and proofs in full: the frame scalar
   map is bijective on stalks, unit status survives precisely positive powers, residue-field
   extension reflects zero, and the restricted closed cover is constructed explicitly.
   Empty scheme/cover, empty T, zero section and exponent one are handled; exponent zero
   is excluded. Fresh leanfinder search for positive powers and qualified loogle search for
   affine closed immersions found no replacement for either complete helper. Library rg
   searches found only relative projective ampleness (a different predicate), and existing
   nonvanishing results which do not prove these full statements. Verdict: pass.
4. The proof retains the finite-set section, discrete-overlap gluing, positive-power
   ampleness, and finite closed affine-cover route. sk-thm-curveestimate.realized is
   unchanged and no unit statement or step is bypassed. No longer needed lists both old
   direct proof dependencies now used within helpers; none is claimed globally pruned.
   The earlier duplicate-statement return is repaired: both helper modules now reuse the
   existing private calculations through `import all` (and retain existing calls), with no
   local copies. ProjectionFormula remains public because its tensor-power invertibility
   instance occurs in the public theorem type; tested the private alternative in scratch.
   Verdict: pass.
5. Checked all three node records against their Lean statements and proof bodies.
   Every proof_deps is exactly the union of the recorded step uses. Existing node changes
   are confined to proof, proof_deps and proof_origin. Both new nodes contain the required
   source, search, creation, blueprint, chapter/unit and Lean fields. Their statements are
   strictly smaller auxiliary arguments and fully proved. Verdict: pass.

Second reading changed: repaired the earlier duplicate-statement return by deleting the
local stalk-linearity, nonvanishing-isomorphism, and bijective-germ copies and adding
`import all` for `AmpleIso` (plus `SectionNonvanishingZeroLocus` in the positive-power
module). Existing calls are unchanged and resolve to the imported private helpers. No
 theorem statement, definition, hole count or unit route changed.


## Second reading by H2

1. Compared every delivered module with the repository. Only the assigned module exists
   there; its theorem signature is byte-for-byte identical, including all hypotheses
   and conclusions. Its docstring and public imports are unchanged. No definition or
   existing visibility changed and no change record is needed. Verdict: pass.
2. Compiled all three final modules through lcompile.py in import order, without errors
   or warnings. Scanned the delivered Lean for sorry, axiom, unsafe, opaque, extern,
   implemented_by and skipped kernel checks: none. Independently printed axioms against
   the final sandbox overlay: positive-power ampleness uses propext, Classical.choice,
   Quot.sound; the other two theorems also use sorryAx from existing dependencies.
   No data definition was added. The selected adjunction is fixed by its unit formula;
   existential witnesses for the target are assembled in a theorem proof, not used to
   define an arbitrary object from an unproved existence theorem. Verdict: pass.
3. No split-off statements or holes remain. Read the two new proved statements and proofs:
   the frame scalar map identifies nonvanishing with a unit coefficient; positive powers
   preserve unit status; section transport preserves the locus; component restriction
   reflects nonvanishing; and the restricted closed immersions explicitly cover U.
   Empty schemes/covers and empty T need no nonempty hypothesis. A zero section has empty
   locus; k=1 is included, k=0 excluded. Fresh leanfinder search for nonzero tensor powers
   returned basicOpen_pow results, and loogle for affine closed immersions returned only
   affine-target criteria. Library/upstream rg finds relative IsAmple.tensorPow, whose
   different predicate does not replace absolute ampleness. It also finds the exact
   nonvanishing_tensorPullback calculation, which is now reused. Verdict: pass after repair.
4. The finite-set section theorem, discrete-overlap gluing, component ampleness and finite
   closed affine-cover route are retained. sk-thm-curveestimate.realized is unchanged.
   Removed the repeated fibre calculation and its three direct proof imports, replacing
   them with NonvanishingTensorPullback. Remaining public imports provide the public
   statement's types and tensor-power invertibility instance. All old direct proof
   dependencies are accounted for under No longer needed; no module is claimed globally
   pruned. Verdict: pass after repair.
5. Checked the three DAG nodes against the Lean proof. The assigned node changes only
   proof, proof_deps and proof_origin. Both new nodes have the required source, searches,
   creation, blueprint, chapter/unit and Lean records; their Lean statements match their
   declaration headers exactly. Each proof_deps equals the union of step uses. Updated
   the affine-locus node to use lem-sc-nonvanishing-tensor-pullback instead of directly
   claiming the fibre comparison. Both auxiliary statements are fully proved and strictly
   smaller than the assigned construction. Verdict: pass after repair.

Second reading changed the affine-locus proof to apply the existing
nonvanishing_tensorPullback theorem, removed its duplicate fibre calculation and three
proof imports, updated that node's proof/dependencies, and corrected this report.
No statement, definition, visibility, unit route or hole count changed.
