## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineCapture` by a complete
Lean reduction through finite affine generators. The existing signature and public import
are unchanged. Added a proof-only import of the new
`Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineGenerators` and of the proved source module
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`.

The repair removes `quasiCoherent_slice_iff_open` and folds only the required transport
applications into `quasiCoherent_slice_image`, invoking Mathlib's public
`isQuasicoherent_pushforward_of_isLeftAdjoint` directly. No replacement equivalence
statement is introduced.

The witness Q is the actual abelian image of the finite free map. Proved private helpers
transport quasi-coherence through the slice/open-subscheme equivalence and prove the image
quasi-coherent using existing kernel and cokernel closure. Its finite global image generators
prove finite type directly. Restriction preserves the image inclusion's monomorphism; the
restricted free map is epi, so its image inclusion is epi and hence iso. Updated the original
node to this route and added the finite-numerator generating-family node.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_capture`
(node `lem-weil-pbc-module-finite-type-affine-capture`) by reduction. No sorry remains in the
item module. Added one sorry:
`AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_generators`
(node `lem-weil-pbc-module-finite-type-affine-generators`). This is a decomposition: one hole
closed, one strictly smaller finite-free generating-map hole added; net holes zero. It is
not claimed as a sorry-free proof of the capture theorem.

Both remaining private helpers are fully proved. The new theorem does not assert a submodule,
monomorphism, finite type of an image, or an isomorphism; all these parts are established by
the combining proof. Edge cases checked mathematically: empty K uses the zero free module;
K = V is a finite free surjection; n = 0 is permitted; no Noetherian, separation, or
quasi-compactness hypothesis on X is needed. Single-file and sandbox compilation succeeded
without warnings. The final delivery dry run also checks the allowed-axiom probe.

## No longer needed

The duplicate private slice/open equivalence helper is no longer needed. Its specific
transport applications now use Mathlib's existing general pushforward theorem directly.
`Sheaf.AlgebraicGeometry.AffineAlgebraModuleKernel` is not imported: its helper is private,
and its public algebra-kernel theorem is not needed by this image argument.

Removed the original proof-only import
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` from the capture module.
No existing module is claimed globally pruned. The separate localization-injectivity and inverse-gluing parts of the original
plan are unnecessary: the constructed image inclusion is mono, and its restriction is
mono and epi. The following old `proof_deps` are removed from the capture node's direct dependencies:
- `lem-weil-pbc-affine-tilde-gamma-adjunction`;
- `lem-weil-pbc-spec-module-tilde-sections`;
- `lem-weil-pbc-quasi-coherent-finite-type-affine`;
- `def-weil-pbc-quasi-compact-scheme`;
- `lem-weil-pbc-module-restriction-open-immersion-colimits`.

All five remain dependencies of the finite-generators lemma; none is claimed globally
pruned. The finite-type and module-category definition nodes remain direct dependencies.

The general finite-type epimorphic-image module `Sheaf.AlgebraicGeometry.FiniteTypeEpiImage`
was considered but is not imported. Direct finite global image generators avoid its
`Sheaf.AlgebraicGeometry.EpiOverFunctor` dependency. No unit statement or realized proof
step is bypassed; this node is below the unit level of `sk-thm-p1`.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned delivery: removed the duplicate private theorem
`AlgebraicGeometry.Scheme.Modules.quasiCoherent_slice_iff_open`. The existing declaration
in `Sheaf.AlgebraicGeometry.AffineAlgebraModuleKernel` is private, so it cannot be invoked
through an ordinary import, and changing that unheld module's visibility is not authorized.
Instead, the image proof directly uses the existing public Mathlib theorem
`SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint` for its source, target and
inverse transport. This removes the duplicate statement rather than renaming it or changing
its binders. No library module is adapted and no signature or visibility changes.
The two sandbox modules compiled after the repair (3.5 s and 18.8 s).
The second-reading section below records the earlier delivery, before this repair.

No mathematical error was found. The original plan leaves the finite-numerator selection
and the slice-site transport as substantial glue, despite its proof dependencies having
Lean declarations. The selection is now one precise, independently provable theorem;
the slice-site transport and image arguments are fully proved here. The source-library
quasi-coherent kernel and cokernel theorems give the image argument directly.

LeanSearch returned Internal Server Error; LeanFinder and source searches ran and found
local generating-data definitions, but no exact compact-open finite affine generators
lemma. The local Stacks source is not present on this machine; the referenced 01PF page
was read directly, including its final finite-numerator paragraph.

## New nodes

`lem-weil-pbc-module-finite-type-affine-generators`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-module-finite-type-affine-generators.json`,
states just the finite free map on V that generates on K. Its source is Stacks 01PF,
final paragraph, and 01PB. Its proof, dependencies, Lean signature, actual search records,
and blueprint ancestry are recorded. There are no statement changes or change records.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered capture module against the repository with `diff -u`.
   The existing declaration's signature is byte for byte unchanged, and its public
   import and visibility are unchanged. Only private proof helpers, proof-only imports,
   the proof body and its description were added or changed. There are no definitions,
   statement changes, forced adaptations or change records. No target changes.
2. Compiled both modules in import order through `lcompile.py --all`: generators 5.6 s,
   capture 26.7 s; no errors or warnings. Read every proof and scanned forbidden constructs.
   The sole sorry is the reported, public named generator theorem. The image witness is
   an actual kernel-of-cokernel construction inside a theorem proof; no definition chooses
   arbitrary data from an unproved existence theorem. The scratch-copy axiom probe passed: all three private helpers use only
   `propext`, `Classical.choice` and `Quot.sound`; capture and generators use those
   axioms and `sorryAx`, as expected from the one open generator theorem.
3. Read the generator statement, full docstring and new node, and checked the numerator
   argument against Stacks 01PF and 01PB. Empty K, zero H, zero ring, K = V and n = 0
   are compatible with the claim. Compactness transfers to the affine open; denominators
   are units on each selected principal open. The lemma isolates only the finite map
   generating on K, leaving quasi-coherence and finite type of the image, its mono and
   restricted isomorphism to the proved recombination. It is a decomposition, net zero
   holes, not a restatement proof or a sorry-free result. Independent LeanFinder search
   used “quasi-coherent sheaf compact open finitely many global sections generate stalks”;
   Loogle used `SheafOfModules.free, CategoryTheory.Epi`; grep used
   `finite_sections|generatingSections|localGeneratorsDataOfIsFiniteType`, plus source
   searches in lean/Sheaf and lean/WeilConjectures. Found generating-data primitives and
   the affine finite-sections criterion, no exact existing generator/capture theorem.
   These primitives do not close compact principal-cover numerator selection in a few minutes.
4. Read the proof from the target downward. The finite-free image route already replaces
   localization-injectivity and gluing with the shorter categorical mono/epi argument.
   Both added imports are proof-only and used; the original public import supplies the
   signature's module-ring and sheaf structures. Checked `dag/units/sk-thm-p1.json`:
   capture and generators realize no unit statement or unit step. Its route is retained.
   Corrected `## No longer needed` to list every removed old direct proof dependency,
   distinguishing that local dependency change from global pruning (none).
5. Compared the old and new capture nodes, checked the new node's required fields and
   exact Lean signature, and inspected their dependency declarations. The capture node
   now records generators, source kernel/cokernel closure, finite generating-data and
   the shared `moduleOverMap_limits` instance from DerivedHomMayerVietoris. Its proof
   dependency list is the union of its step uses. The generator node keeps the original
   affine numerator route and records source, searches, ancestry and the sole open theorem.

Changes by the second reader: completed the exact removed-dependency list and added this
review record. No Lean proof or statement repair was necessary.


## Second reading by E1

1. PASS: compared each delivered module against the repository baseline with diff.
   The existing capture signature is byte for byte unchanged; its public import and
   visibility are unchanged. Generators is a new module. The existing node changes
   only proof, proof_deps and proof_origin. No definition, existing statement, target,
   visibility or other held module is changed; no change record is required.
2. PASS: compiled both modules in import order through lcompile.py --all (4.1 s and
   24.0 s), without errors or warnings. Read both private helpers and the recombination.
   A scratch-copy #print axioms probe shows only propext, Classical.choice and Quot.sound
   for both helpers; capture and generators additionally use sorryAx from the sole
   reported generator hole. The only sorry is the named public generator theorem;
   no forbidden constructs or hollow definitions occur. Q is an actual abelian image,
   not arbitrary data chosen in a definition from an unproved existence theorem.
3. PASS: checked generators and its node against Stacks 01PF's final paragraph and
   01PB (https://stacks.math.columbia.edu/tag/01PF and
   https://stacks.math.columbia.edu/tag/01PB). Numerators generate after localization
   since the denominators are units. Empty K, zero H, the zero ring, K = V, and n = 0
   cause no exception. The full docstring supplies the numerator proof. This splits
   off only the finite free map, strictly below capture: quasi-coherence and finite
   type of its image, its monomorphism and restricted isomorphism are actually proved.
   Independent LeanFinder search used "finite family of sections of a quasi coherent
   module on an affine scheme generating on a quasi compact open subset"; Loogle
   searched SheafOfModules.IsFiniteType, and grep and rg searched finite generating
   families and section-cover statements. Read AffineFiniteTypeGeneratingSections
   and FiniteSectionsCover: the former handles a module finite type on all of an
   affine scheme; the latter concerns nonvanishing loci of invertible modules.
   Neither supplies compact-open numerator selection. No exact existing lemma found;
   the remaining localization/cover transport does not close in a few minutes.
4. PASS: read from capture downward. The image route already avoids localization
   injectivity and gluing; the two proof-only imports are used, and Coherent supplies
   the statement structures and shared open-restriction limit instance. Checked
   dag/units/sk-thm-p1.json realized: neither delivered node realizes a unit statement
   or proof step, and the unit route is retained. No longer needed now correctly
   names the removed QuasicoherentFiniteTypeAffine import and all five removed old
   direct proof dependencies. Global pruning is not claimed.
5. PASS: checked the two node Lean signatures verbatim, required new-node fields,
   sources, ancestry, searches and dependency declarations. Each proof_deps list is
   exactly the union of its proof-step uses. Capture records the generator reduction,
   proved source kernel/cokernel closure and shared finite-limit restriction instance;
   generators records the finite-numerator route and sole open theorem. No node or
   statement drift found.

Changes by this second reader: corrected the false claim that no original import was
removed, and appended this fresh review of the repaired two-helper version. No Lean
repair was necessary. One original hole is closed by reduction and one smaller hole
is added: decomposition, net zero holes, no sorry-free capture claim.
