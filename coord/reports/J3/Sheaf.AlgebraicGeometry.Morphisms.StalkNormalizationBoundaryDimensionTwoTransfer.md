## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoTransfer`.
Its theorem `AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two_transfer`
keeps its exact signature and visibility. The proof follows the planned normal-component
going-down route. It obtains source normality and density from
`stalk_normalization_normal_and_dense`, proves target normality by smooth ascent and
flat-preimmersion stalk isomorphisms, proves etaleness on the original open by relative
normalization and pullback identities, and applies the new geometric going-down lemma.
The final dimension comparison is proved in Lean: a local map with going down has
surjective prime spectrum by lifting below the maximal ideal, so the already proved
`ringKrullDim_le_of_goingDown_of_surjective` applies. Transitivity with the supplied
`hboundary` finishes the original theorem.

Added proof-only imports of StalkNormalizationNormalDense, FiniteNormalDenseEtaleGoingDown,
SmoothNormalRing, KrullDimension.GoingDown, FunctionField, and Morphisms.Flat.
Added one new module, `Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDenseEtaleGoingDown`.
All local helpers are private and proved. The new public theorem isolates the geometric
stalk going-down step; it does not mention depth, boundary points, Krull dimension, a
smooth base, or relative normalization. It requires no data construction from an
unproved existence statement. The unchanged theorem retains its now redundant boundary
minimality and depth binders; a declaration-local unused-variable linter setting records
this without changing its interface.

Updated the item's DAG proof, proof_deps and proof_origin to describe the actual proof.
No statement or definition was changed, and no consumer adaptation is included.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two_transfer`
(node `new-stalk-normalization-boundary-dimension-two-transfer`).
The item's module has no sorry left.

Added one hole:
`AlgebraicGeometry.Scheme.finite_normal_dense_etale_stalk_goingDown`
(node `new-finite-normal-dense-etale-stalk-going-down`), the sole declaration of the new
module. Its entire proof is `:= by sorry`. Its docstring and node give the affine
component, dominance, domain going-down, and localization argument.

This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
It is not a claim of an axiom-free proof of the whole dependency closure. Existing
normality/density and smooth normal-ring inputs retain their pre-existing dependencies.

Local compilation passed for both delivered modules, with no warnings after cleanup.
The delivery dry run supplies the final declaration and axiom probes.

## No longer needed

Removed the proof import
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore`
(node `new-stalk-normalization-boundary-dimension-two-target`) from this item.
The supplied `hboundary` already gives exactly that target dimension bound, so this
transfer proof does not prove it again. This is a pruning of this item's edge only:
the parent BoundaryDimensionTwo module still uses Core to supply `hboundary`.

The old direct proof dependency `lem-weil-pbc-going-down-normal-integral` is now used
inside the new geometric lemma's plan rather than directly by the item's Lean proof.
It remains needed; it is not pruned from the overall route. The normal/dense dependency
also remains needed. No unit statement or unit proof step is bypassed. No other old
proof import or old planned node is discarded. The original public imports remain.

## Where the brief, the DAG or earlier work was wrong

The original plan has the correct idea but does not supply a declaration connecting
finite relative normalization to going down on scheme stalk maps. In particular a finite
scheme morphism does not in general make its stalk ring map integral: source localization
can destroy integrality. The new lemma first applies 00H8 to finite injective maps of
normal affine component rings and then transports going down through both localizations.

Normality and density alone also do not guarantee component dominance for an arbitrary
finite map. Etaleness over the dense source open supplies openness and hence dominance.
The item's proof now establishes and passes that hypothesis explicitly. It does not
assume the smooth pullback is integral or that the finite etale source is connected.

Edge cases checked for the new statement: an empty source gives no points; an empty
chosen open can be dense only when the source is empty; disconnected normal schemes are
handled on their open-and-closed integral components; a finite map need not be globally
surjective. A closed-point inclusion in an integral affine line would violate the
etaleness hypothesis, so the invalid finite closed-immersion dimension inequality is
not asserted. The local spectrum-surjectivity proof uses localness and going down,
not integrality of the stalk map.

The new lemma follows the component argument already documented in
FiniteNormalDenseOpenComparison, combined with Stacks
[0357](https://stacks.math.columbia.edu/tag/0357),
[01UA](https://stacks.math.columbia.edu/tag/01UA), and the Mathlib instance marked 00H8
in IntegralClosure.GoingDown. The first two source pages were read; the 00H8 web page
returned 503, and its formal Mathlib instance and proof were read directly instead.
LeanSearch returned Internal Server Error; LeanFinder, Loogle, and source/DAG searches
were performed and are recorded. No matching existing scheme-stalk theorem was found.
The blueprint ancestor helper returned None because this item's created.item uses a
module name; the new node's blueprint ancestry was recovered by reading the parent
BoundaryDimensionTwo node and its ancestry. No project tool was changed.

## New nodes

`new-finite-normal-dense-etale-stalk-going-down`, in
`dag/nodes/sec-smooth-base-change/`, states going down on stalks of a finite map between
locally Noetherian normal schemes that is etale over an open with dense source inverse
image. Its Lean module is `Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDenseEtaleGoingDown`.
It is a strictly geometric part of the original argument: the separate normality,
etale restriction, density application, local prime lifting, and dimension transitivity
are genuine proved Lean in the assigned module. Its source, complete natural-language
proof, three search kinds, dependencies and blueprint ancestry are included.
No change record is needed because no existing signature or definition changed.

## Second reading by J3

1. Interface check: PASS. Diffed both delivered modules against the repository.
The sole existing public declaration is
`AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two_transfer`;
its complete signature was compared byte for byte and is identical. Its universes,
instances, boundary/depth assumptions, let-bound maps, finite-map premise and final
source-stalk dimension conclusion are retained. Existing public imports and
visibility are unchanged. No definition or other module is adapted.

2. Proof check: PASS as a decomposition. Both modules compile cleanly through
`lcompile.py --all`. The assigned module contains no sorry. The new module has
exactly the reported named theorem with `:= by sorry`, with a sourced complete
proof docstring and matching node. No forbidden declaration or hollow definition
is present. Scratch `#print axioms` checks cover the public declarations and all
five private helpers: only propext, Classical.choice, Quot.sound and sorryAx occur.
The pullback/restriction argument establishes the actual etale hypothesis; the
flat-preimmersion argument uses stalk isomorphisms, not an incorrect assertion
that arbitrary flat base change preserves normality. Localness identifies the
maximal ideals, and going down then gives the spectrum surjectivity needed for
the dimension inequality. One old hole is closed and one new hole added; net zero.

3. Split statement and search: PASS. Read every hypothesis and the conclusion of
`finite_normal_dense_etale_stalk_goingDown` against its node. Finite over locally
Noetherian gives locally Noetherian source; normality gives disjoint components.
Restricting to an integral affine target component preserves density. Each
source component meets the etale locus, whose nonempty image is open and thus
dense in that integral target. Its component-ring map is therefore injective
and integral, so normal-domain going down applies before both localizations.
Empty sources and empty dense opens are vacuous; disconnected targets reduce
componentwise. A closed-point inclusion in a line fails the etale premise.
The statement isolates a strictly geometric step and does not restate the
boundary dimension target. Independent LeanFinder search used "finite dominant
morphism normal scheme generalizing stalk local ring going down"; Loogle used
"IsLocalHom, Algebra.HasGoingDown"; launcher grep used
"generalizingMap|HasGoingDown|stalk.*dimension". Direct searches of the project,
upstream scheme modules and Mathlib found only flat generalizing-map results,
ring going-down instances and the already-used dimension inequality.
No existing theorem closes this geometric step in a few minutes. Read Stacks
0357 and 01UA and the Mathlib 00H8 instance; the 00H8 webpage again returned 503.

4. Route and pruning: PASS. The proof keeps the planned normal-component
integral going-down route, with proved smooth normality, etale restriction,
local prime lifting and dimension transitivity surrounding the geometric hole.
The removed Core import is correctly reported: hboundary supplies its bound.
The old normal/dense dependency remains used; the old normal-integral
going-down dependency remains in the new lemma's plan and is not globally
pruned. Read `dag/units/sk-prop-input-spreading.json`: its realized entries are
currently empty, and its extension/local-computation route is retained.
No unit file changes. Added proof-only imports to the new holed module for
its stated plan: NormalSectionsFiniteProduct, IntegralClosure.GoingDown, and
Morphisms.UniversallyOpen. Its public imports supply its statement's notions.
The assigned module's new imports are all proof-only and support actual steps.

5. DAG check: PASS after metadata repair. The existing node differs only in
proof, proof_deps and proof_origin. In both nodes proof_deps is exactly the
union of step uses; the statements and recorded Lean signatures match the
files. The new node has source, search records, ancestry, chapter, unit,
created and lean records. Added its missing lean_audit records with state none
for both source branches. Its blueprint ancestry leads back to the spreading
unit; no target, existing node statement or definition changed.

Second-reading changes: restored the new hole's three planned proof imports,
added its module-docstring blueprint tag and new-node lean_audit records,
and recorded this independent reading. No mathematical statement or proof
body needed repair. The dry run and final delivery are performed after this
reading through deliver3.py.
