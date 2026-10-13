## What changed

Proved `AlgebraicGeometry.gradedModule_realization_isFiniteType` without changing its
signature or existing docstring. Added the proof imports
`Sheaf.Paper.GradedRealizationLocalGeneratorsEpi` and
`Sheaf.AlgebraicGeometry.AffineModuleFiniteType`.

Added the fully proved local theorem
`AlgebraicGeometry.gradedRealization_local_generators_epi` in its own module. It proves
that the explicit finite free map is epi on one fixed generating open, for arbitrary
scheme morphisms and arbitrary modules. It assumes neither affineness nor
quasi-coherence. It proves epimorphy by testing two maps, restricting the coproduct,
inducting on the homogeneous span, and using a covering equalizer sieve. Thus it avoids
local representatives from sheafification. The target constructs the actual basis
sections and generating cover, then uses the existing affine correspondence lemmas.
No arbitrary realization or generators are chosen from an unproved existence theorem.

Both modules compile cleanly. The local proof includes r = 0 and U empty; the target's
cover includes X empty. The degree equality is explicitly resolved before eliminating
HEq. The original blueprint unit route is unchanged; only the item's lower-level route
was shortened.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.gradedModule_realization_isFiniteType`
(node `lem-weil-pbc-graded-module-realization-finite-type`): 1 of 1 holes closed.
The new theorem `AlgebraicGeometry.gradedRealization_local_generators_epi`
(node `lem-weil-pbc-graded-realization-local-generators-epi`) is proved, with no hole.
No `sorry` remains in either delivered module; no holes were added or split off.

The proof uses the existing declarations
`AlgebraicGeometry.Scheme.Modules.affine_module_correspondence` and
`AlgebraicGeometry.Scheme.Modules.affine_module_finite_type`; their existing downstream
proof obligations remain. This is a proof from existing named statements, rather than
an assertion that the complete target closure is already axiom-free.

## No longer needed

No original statement import was removed: the four original public imports supply the
unchanged statement's pullback, quasi-coherence, scalar endomorphism and moduleRings API.
The new module imports the free-module API, rather than the quasi-coherence API.

The following original planned dependencies are not needed by this item's proof:

- `lem-weil-pbc-module-sheaves-colimits-forgetful`, module
  `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`;
- `lem-weil-pbc-site-sheafification-sections-local`, module
  `Sheaf.Paper.SiteSheafificationSectionsLocal`;
- `def-weil-presheaf-modules-sheafification`, the planned explicit module-sheafification
  construction;
- `def-weil-sheaf-of-modules-category` is no longer a direct dependency of this
  item: the new local-epimorphism node records its use. Its Mathlib API remains
  required by the unchanged signatures and by that local proof.

The proof does not require their presheaf-colimit, sheafification-unit, local-finite-sum
or overlap descent steps. This is pruning of this item's direct proof route; it does not
claim those modules disappear from every other target's import closure.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid, but constructing local representatives of
coproduct sections is unnecessary. Coproduct hom_ext after open restriction, together
with separatedness, proves the explicit finite generator map epi directly. The
original statement and all hypotheses are preserved. No disputed statement, interface
change or forced adaptation was needed.

LeanSearch was unavailable (Internal Server Error). LeanFinder, Loogle and grep were
run; they located the free-Hom and finite-type APIs but no theorem covering the full
local homogeneous generation calculation. Blueprint search for homogeneous generators
found no existing node with this local epimorphism statement.

## New nodes

`lem-weil-pbc-graded-realization-local-generators-epi` records the proved fixed-open
local generation calculation in
`lean/Sheaf/Paper/GradedRealizationLocalGeneratorsEpi.lean`. Its scalar action is the
actual sectionwise direct-image algebra action, and its basis sections are explicitly
constructed by restriction. It is strictly the local generation step, not a renamed
version of the target: neither quasi-coherence, affineness, base change nor global
finite type occurs in its conclusion. There are no change records.

## Second reading by H1

1. PASS: compared the existing module with the repository by diff and checked the
   theorem signature byte for byte. Only its proof and two plain proof imports
   changed; its existing docstring, visibility and hypotheses are unchanged. The
   other delivered module is new. No definitions or existing statements changed,
   and there are no forced adaptations or change records.
2. PASS: compiled both files together through lcompile.py, with no errors or
   warnings (35.6 s and 14.4 s). No delivered file contains sorry, axiom, unsafe,
   opaque, implemented_by, extern or a hollow definition. Scratch-copy axiom checks
   show only propext, Classical.choice and Quot.sound for the local epimorphism;
   the original theorem additionally has sorryAx from existing affine correspondence
   obligations. One simultaneous scratch probe timed out; the unchanged local
   file's probe passed alone in 47.3 s. No timeout workaround or source change was
   needed. The cover and basis sections are actual constructions using hfinite,
   not witnesses selected from an unproved existence theorem.
3. PASS: no statement was split off with sorry. Read the new proved local theorem
   and its complete docstring argument. It is strictly the fixed-open epimorphism
   step, with no quasi-coherence or global finite-type conclusion. Checked r = 0,
   U empty, X empty, and m = 0: span induction and separatedness handle the empty
   cases, and d_i <= m is used before converting HEq. Independent LeanFinder,
   Loogle and grep searches found the free-Hom and generating-section primitives
   but no duplicate of this local graded argument. Also inspected the library's
   generating_sections_iff_stalk_span: it concerns scheme structure-ring stalks,
   not the direct-image algebra on a slice, and does not replace this argument.
   Checked the cited Stacks pages: https://stacks.math.columbia.edu/tag/0897,
   https://stacks.math.columbia.edu/tag/03DA and
   https://stacks.math.columbia.edu/tag/01B4 support the stated finite-type context.
4. PASS after reporting repair: read the proof from the original theorem down to
   the local epimorphism. Restriction preserves the coproduct, compatibility and
   span induction give local equality, and separatedness gives equality of maps.
   The original proof then constructs LocalGeneratorsData and applies the existing
   affine finite-type correspondence. All public imports supply names appearing
   in signatures; the two added imports of the original module are proof-only.
   The new module's Free import supplies freeHomEquiv in its conclusion. Compared
   old and new proof_deps and completed the pruning list below. Read
   dag/units/sk-thm-p1.json: neither this item nor the removed direct dependencies
   realizes a unit statement or step, and the unit's realized route is retained.
5. PASS: both nodes' proof_deps equal the union of their proof steps' uses, and
   proof/proof_origin describe the actual Lean route. Existing-node changes are
   confined to the permitted proof fields. The new node has its source, searches,
   creation/blueprint/chapter/unit records and a Lean signature matching the file
   verbatim. It is fully proved and introduces no hole.

Changed only report.md: completed `## No longer needed` with the removed direct
proof dependency `def-weil-sheaf-of-modules-category`, whose use is now recorded
under the local-epimorphism node, and added this independent reading. The Lean
proofs and DAG records needed no repair. Holes closed: 1; holes added: 0.
