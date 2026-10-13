## What changed

Proved the body of
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_formalGlueingData_affine_datum`
in `Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineDatum`, without changing its
signature or existing docstrings. Added the proved private helper `punctured_chart_cover`.
The proof establishes the cover and principal-open containment from the maximal-ideal generators,
then computes both families of kernels in `FormalGlueing.h0`. It proves the forward implication
by applying section identifications and the reverse implication by their injectivity.

Added the proof-only import
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineCoordinateSquares`.
That new module isolates the affine construction, with structural A-linear coordinate maps and
four explicit restriction/pullback squares. It assumes only containment of the principal charts
in U; it neither asserts a cover nor mentions H0. Updated the original node's proof and
proof dependencies to describe this construction followed by the actual Lean kernel argument.
All writes are in the sandbox; no delivery was pushed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_formalGlueingData_affine_datum`
(node `lem-sbc-punctured-completion-affine-datum`). The original module contains no sorry.
Its chart cover and containment, kernel expansion, and both directions of the characterization
are fully proved in Lean.

Added one hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_affine_coordinate_squares`
(node `lem-sbc-punctured-completion-affine-coordinate-squares`), whose whole proof is `by sorry`.
It constructs the modules and affine localization/tensor coordinate identifications, with their
four numerator formulas, and leaves the cover and the H0 calculation to the original module.
This is a decomposition: one hole closed and one added, net zero. The original declaration
still depends on this named geometric construction; it is not an axiom-free finished target.
No arbitrary witness is chosen to define any object, and no definition is added.

The empty index case is covered by the pointwise cover proof (hgen forces all image primes to
be the excluded closed point), and all kernel and compatibility equations are vacuous.
Zero or nilpotent generators give empty charts with zero section rings and localizations.
Redundant generators give repeated charts and the same restriction equations.

## No longer needed

No original import is removed: the two public imports are required by the unchanged statement.
No whole node or module is pruned from the construction. The original node no longer uses
`lem-weil-pbc-finite-morphism-permanence` directly; the new construction node still needs it.
Thus this relocation is not claimed as pruning.

The proof does not import the nearby modules
`PuncturedCompletionFormalGlueingPrime`, `PuncturedCompletionFormalGlueingData`, or
`PuncturedCompletionAffineChartRealization`: none supplies the required A-linear chart
coordinate interface. They were not imports of the original module, so their absence is not
counted as a removed import or global pruning.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies provide formal gluing definitions and finite-morphism
permanence, but no declaration constructing the affine coordinates with the required linear
structure. The affine/tensor identifications of its second step therefore need an explicit
interface before the kernel calculation can be formalized.

The nearby existing theorem `exists_affine_chart_realization` was read in full: its chart maps
are `≃+`, whereas this item's chart maps must be `≃ₗ[A]` for the displayed structural actions.
It does provide the four numerator squares, but supplies no chart scalar-compatibility theorem.
Its prime map is C-linear for a separate explicitly installed C-action. Applying that theorem
alone does not supply this item's required structural A-linear equivalences. The new construction
specifies these linear maps rather than silently treating additive equivalences as linear.
No existing statement or definition was changed; no forced adaptation is needed.

The source pages [Stacks 0BLH](https://stacks.math.columbia.edu/tag/0BLH) and
[Stacks 05EL](https://stacks.math.columbia.edu/tag/05EL) were read online, since this checkout
contains only literature indexes. They specify the affine chart construction and the two H0
families used here. No unit statement or unit proof route changes; the inherited unit is
`sk-prop-input-spreading`, whose realized lists contain no binding for this item.

## New nodes

`lem-sbc-punctured-completion-affine-coordinate-squares` in
`dag/nodes/sec-smooth-base-change/lem-sbc-punctured-completion-affine-coordinate-squares.json`
records `exists_affine_coordinate_squares` in the new module
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineCoordinateSquares`.
Its docstring and numbered proof describe finite affine chart sections, their localized scalar
actions, double/triple-chart fraction formulas, the affine fibre-product tensor formula,
and all four numerator squares. It is strictly the coordinate-construction part of the
argument: its hypotheses do not require a punctured complement or maximal-ideal generators,
and its conclusion does not contain either the cover or the H0 characterization.
Searches used LeanSearch (service unavailable), LeanFinder, Loogle for the local-prime cover
argument, Mathlib grep, and repository searches of Sheaf and WeilConjectures. Mathlib supplies
localization and affine-pullback constituents; the library's closest construction lacks the
required chart A-linearity. There are no change records because no existing interface changes.

## Second reading by G3

1. Compared both delivered modules with the repository. The coordinate-squares module is new.
   The existing affine-datum declaration signature is byte for byte unchanged, as are its
   existing docstrings and public imports. No definitions or target statements changed.
   The existing node differs only in proof, proof_deps, and proof_origin. Verdict: pass.
2. Compiled both modules in import order with lcompile.py, with no compiler errors. Scanned
   for forbidden declarations and hollow definitions: none. A scratch copy with #print axioms
   gives propext, Classical.choice, Quot.sound, and sorryAx for the two public theorems, and
   only the three permitted axioms for punctured_chart_cover. The sole sorry is the reported
   exists_affine_coordinate_squares. The kernel proof uses all four squares in both directions
   and injectivity in the reverse direction. Verdict: pass as a decomposition, not a finished
   axiom-free proof of the original theorem.
3. Read the split-off statement and its complete construction proof against Stacks
   [0BLH](https://stacks.math.columbia.edu/tag/0BLH) and
   [05EL](https://stacks.math.columbia.edu/tag/05EL). Checked t = 0, empty U and Y, nilpotent
   generators, and repeated generators: the indicated zero modules and empty families give
   the stated constructions. No punctured-complement or generation hypothesis is needed for
   the coordinate construction; principal-open containment suffices. This is the geometric
   part of the argument, omitting the cover and kernel characterization, rather than a
   renaming of the original conclusion. Repeated the search with LeanFinder for a linear
   equivalence between affine principal-open sections and module localization, and rg for
   linear coordinates and affine realization declarations in both library roots. The hits
   supply constituent localization APIs, not this construction. Read
   exists_affine_chart_realization: its additive chart equivalences do not give the structural
   A-linear equivalences needed here. Verdict: true and useful split; not closable by a short
   application of the available declarations.
4. Read the cover argument, principal-open containment, and H0 proof top downward. No shorter
   available route supplies the missing linear coordinates. Both existing public imports
   occur in the statement, and the new coordinate-squares import is correctly proof-only.
   The new module's two public imports are needed by its statement. No longer needed lists
   the sole old proof dependency absent from the revised parent node, finite-morphism
   permanence, and explains its relocation rather than claiming pruning. Read the unit's
   realized field: no binding for this item is bypassed. Verdict: pass.
5. Compared the Lean declarations with both node records, including the new node's verbatim
   Lean signature, source, construction proof, dependency union, searches, blueprint route,
   unit, chapter, and created metadata. The revised parent node follows the cover, coordinate
   construction, and actual kernel calculation. Verdict: pass.

Second reading changed only this report by adding the independent checks above. No Lean or
DAG repair was needed. One original hole is closed and one construction hole is added: net
zero, with no module pruned.
