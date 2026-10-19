## What changed

The unchanged theorem `SheafOfModules.ringedRefinementCoefficientSquare` now has a
complete Lean proof assembling ordinary and systems packages and their finite
comparisons. This is a decomposition, not a sorry-free proof of the mathematical
existence assertion.

Moved its existing presentation definitions verbatim into
`Sheaf.Paper.RingedRefinementModels`, publicly reexported by the item. This avoids
cycles between the presentation types, the three new obligations, and the theorem.
This relocation is not a response to a compile timeout. All existing signatures,
visibility and definition bodies are preserved; there are no other existing users.
The ownership node and change record cover the relocation.

`Sheaf.Paper.RingedRefinementAssembly` contains the proved construction and formal
argument: `canonicalCoefficients` is Mathlib's sectionwise pushforward compositor;
`canonicalShape` explicitly constructs the pullback in Over T, its section and both
projection equations, and obtains clopenness from `properOpenSectionProperties`.
`OpenComparisons.hom` is the actual three-factor natural transformation.
`canonicalRefinements` constructs its adjoint using the geometric unit.
The private `mate_square` proves the coefficient-square transfer by the counit
formula, naturality, and the injectivity of the adjunction Hom equivalence.
`laws_of_coherences` applies that proof, obtains input naturality directly, and
derives the commuting coefficient square from the coefficient cocycle and equality
substitution. `assemble` constructs the full Package, including its shapes and
refinements. No map is chosen from an arbitrary existence theorem.

The resumed session additionally proves `nonempty_shifts_of_elementary` and its
underlying comparisons. Exact localization transfers the termwise open-adjunction
shift equation. A generic inverse-transpose argument proves shifts of beta and
delta; composition proves shifts of the three-factor h map. Taking mates then
proves shifts of chi and the refinement, and composing proves shifts of both
square composites. Explicit unitors and associators keep the fixed structures.

`canonicalScalarShifts` and `canonicalScalarCounit` apply the proved universal
right-Kan-extension shift theorem to each scalar cochain pair. Its universal
property uniquely fixes the comparisons by the counit equation. These are actual
constructions, with no data taken from mere unproved existence. A resumed proof further establishes compatibility of the geometric adjunction
with the standard K-injective shifts, by restricting its derived unit to
K-injectives and descending its shift equation. The standalone experiment
`GeometricUnit.lean` compiled cleanly in 3.0 seconds. Its integration into Assembly
is being checked through lcompile.py. Thus only shifts of the inverse-scalar
comparison and clopen projection remain in `ElementaryShifts`. No extra hole was added.

Three new statement modules isolate the remaining normalized operation data,
pre-mate coherences and shifts, and constant finite-coefficient comparison. Their
source, proof in words, and individual nodes are included. Each is a strict part
of the original construction, not its statement under a new name.

Current-session checks (2026-10-19): the relocated Models namespace is
byte-identical to the current repository's namespace. The six delivery modules
contain three actual holes, exactly the named obligations listed below; Models,
Assembly and the item contain zero. Replaced a redundant proof-local `letI` in
Assembly by `let` to resolve the style warning recorded by the earlier compiler.
Corrected the Assembly node's stale description: geometric adjunction shift
compatibility is proved there, not a field of `ElementaryShifts`.

The required initial dry run refused the three split-offs at minute zero. The
subsequent full-sandbox lcompile request returned exit 124 after 501 seconds:
`no answer from the compile server ... (server busy or unreachable)`; it did not
compile even the first file. A separate small scratch proof also returned exit
124 after 208 seconds with the same no-answer diagnostic; its retry also
returned no answer after 192 seconds. A final single-file Assembly check also returned exit 124 with no server
answer after 190 seconds. These repeated service failures block validation.
These failures precede Lean diagnostics and are compile-service failures, not
Lean elaboration timeouts. The current changes have not been validated or pushed.

A scratch-only argument in `scratchpad/PiShift.lean` attempts to deduce the clopen
projection shift equation from its image equation: the latter makes it a natural
retraction of the open counit; a split subfunctor of the identity has a unique
natural retraction, and shifts transport this splitting. This argument is not yet
compiler-checked, is outside the delivery modules, and is not claimed as proved.
Earlier successful compiles and the preflight's 900-second timeout belong to
previous attempts and do not certify the current delivery.
No target statement changed.

Change record: `coord/changes/ringed-refinement-model-interface.md`.

Continuation checks (2026-10-19, after the provider interruption): the required
initial dry run ran and exited 1 without preparing or pushing a delivery; it
refused the three retained split-off holes. The first sandbox compile checked
Models, Assembly, FiniteComparison and Coherences, then found universe constraints
in the retained private ordinary-operation helper. Explicit ring types, the
sectionwise coefficient map, continuity, exactness and K-injective instances repair
that helper. Its coefficient equation remains definitional. The later full-sandbox
compile checked all six modules successfully, without warnings: Models 1.7 s,
Assembly 16.6 s, FiniteComparison 4.6 s, Coherences 4.4 s, NormalizedData 5.2 s,
and the item 4.7 s. No public statement or existing definition changed.

The continuation also proves the clopen-projection shift equation and integrates
it into Assembly. For ε:P→H and two natural retractions r,s:H→P, fullness of H and
naturality imply rε=sε, hence r=s. Shifting a retraction of a shift-compatible
ε:P→Id gives two retractions of the same transformed ε; fullness of the shift
functor identifies them. For pi, naturality of the open counit and pi_image make
counit≫pi=id by the left triangle. Consequently pi commutes with shifts with no
complementary-open detection assumption. ElementaryShifts now contains only the
inverse-scalar comparison equation. The integrated argument was part of the clean
six-module compile above. No additional hole was introduced.

The compile service has been intermittent: five single-file requests returned
exit 124 with no server response after 204, 182, 208, 194 and 205 seconds. These
precede Lean diagnostics and differ from the 60-second elaboration limit. Later
requests resumed and gave the clean compile recorded above. A scratch file outside
lean cannot see sandbox modules; such experiments must use the sandbox module
layout. No delivery has been pushed in this continuation.

## Proved and sorry left

Closed the one original hole, `SheafOfModules.ringedRefinementCoefficientSquare`
(node `lem-pur-ringed-refinement-coefficient-square`), by a complete assembly proof.
Added three holes; this is a decomposition (one closed, three added; net -2), not
one fully proved target or a claim that its axioms are already sorry-free.

Every remaining sorry in this delivery is the complete proof of exactly one public
named theorem:

- `SheafOfModules.RingedRefinement.exists_normalizedRefinementData`
  (`lem-pur-ringed-refinement-normalized-data`): still needs the module-operation,
  scalar and open-comparison constructions and their normalization transport to
  the exact presentation types. The ring compositor and clopen geometry are
  already constructed by Assembly and need not be repeated.
- `SheafOfModules.RingedRefinement.normalizedRefinementCoherences`
  (`lem-pur-ringed-refinement-coherences`): still needs the product-decomposition
  h-square, normalized coefficient/open/spatial/refinement equations and elementary
  pre-mate shift transport. The adjoint square, input naturality, commuting
  coefficient square, scalar shifts and counit, shifts of beta/delta/h,
  chi/refinement/both square composites, and package assembly are already proved
  and excluded from this obligation. The elementary shift data still needs
  compatibility of the inverse-scalar comparison.
- `SheafOfModules.RingedRefinement.exists_finiteRefinementComparison`
  (`lem-pur-ringed-refinement-finite-comparison`): still needs the section-preserving
  constant-ring realization and ordinary/derived operation comparisons, then
  transport of the three-factor map and its mate to the strict-tower gamma.

Models and Assembly have zero holes. The item itself now has zero holes.

## No longer needed

No original mathematical dependency is declared globally unnecessary: the three
remaining obligations retain the corresponding parts of the original proof plan.
No entire existing module is withdrawn or pruned.

The item no longer directly imports the old proof-dependency modules. Its imports
are now Models (publicly) and NormalizedData, Coherences, FiniteComparison (proof
only). The old public imports are preserved through Models, maintaining visibility.
The following eight proof-only imports were removed from the copied model interface:
ProjectionMateExact, SemilinearDerivedSections, DiagramSiteRealization,
Mathlib.Algebra.Category.Grp.FilteredColimits,
Mathlib.CategoryTheory.Abelian.FunctorCategory, Mathlib.CategoryTheory.Sites.Limits,
DerivedAdjunctionShift and RingedDerivedMonoidalComparisons. These are the three
Mathlib modules and five Sheaf modules. Their required construction uses are recorded in the relevant
new obligation modules; the redundant direct Mathlib imports are unnecessary
because the preserved public dependencies already provide them.

The main node's twelve old direct `tool_uses` approvals are removed:

- `def-weil-pbc-adjunction-mate`
- `lem-cbc-strict-tower-proper-open-calculus`
- `lem-coef-semilinear-derived-sections`
- `lem-pur-derived-change-of-rings`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-sf-open-tensor-normalization`
- `lem-sfb-ringed-derived-monoidal-comparisons`
- `lem-sfb-successive-derived-quotient-normalization`
- `lem-weil-pbc-derived-adjunction-shift`
- `lem-weil-pbc-diagram-site-realization`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-ringed-projection-mate-exact`

Assembly uses `WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction` for
shift-compatible mates, `WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`
for exact localization, and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift`
for the termwise adjunction unit. Its new public import
`Sheaf.CategoryTheory.RightKanExtensionCoherentShift` supplies the universal scalar
shift construction. These are used dependencies, not pruned modules.

This preserves no stale direct dependency claim: its implemented proof directly uses the four new
statement nodes. The old mathematical ingredients remain in the lower obligations'
proof_deps, so this is not counted as pruning their subgraphs.

## Where the brief, the DAG or earlier work was wrong

The original file has one sorry, not several independent diagrams. Its theorem
includes the existence of every normalized operation, comparison, law and finite
realization. The listed dependency declarations provide related site/derived
presentations rather than these exact combined records, so they cannot be applied
directly as a package constructor. The new obligations record the missing interface
construction and coherence work explicitly.

Edge-case checks: the generic mate proof needs no invertibility of chi; shape
construction uses only properness and the open legs, not a Cartesian refinement
triangle; coefficient-square substitution allows arbitrary rings and nonflat maps;
both modes use actual site-derived categories with no levelwise equality detection.
No statement is believed false and no signature or target meaning is weakened.

The resumed source and consumer checks confirmed that the model bodies are
byte-identical to their original definitions, the item has no downstream importing
modules, and the Package use search finds only the item itself. The actual paper
states compactification independence in 6.7.7; the stronger coefficient-ring
assertion is correctly identified in the node as an agent supplement.

The first resumed dry run reached the checks and refused the three split-offs
before minute 72. Work continued on the shift-transfer proof; this is recorded
as a decomposition, with all three remaining holes listed above.

## New nodes

`def-pur-ringed-refinement-models` owns the unchanged presentation types moved to
Models. This is ownership separation without a second definition of any notion.

`lem-pur-ringed-refinement-formal-assembly` records the proved geometric,
naturality, mate-square, coefficient-square, shift-transfer and package-assembly
argument.

`lem-pur-ringed-refinement-normalized-data` isolates existence of the underlying
normalized operations/comparisons, before any coherence law.

`lem-pur-ringed-refinement-coherences` isolates the pre-mate coherence and elementary
shift calculation on given normalized data. It does not repeat the theorem's
existential conclusion and excludes the three laws, the universal scalar shifts
and counit, the geometric adjunction shift compatibility, and the
beta/delta/pi/h/chi/refinement/square shift calculations proved by Assembly.

`lem-pur-ringed-refinement-finite-comparison` isolates only the finite
strict-tower identification. Its conclusion does not assert the coefficient-change
square or the existence of geometric/scalar packages.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
