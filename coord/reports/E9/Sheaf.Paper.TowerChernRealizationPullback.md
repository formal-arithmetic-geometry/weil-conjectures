## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_chernRealization_pullback`
by composition through the intermediate integral quotient tower. The transformation is the
composite of reductionY-whiskered scalar comparison and scalarX-whiskered reduction comparison.
The proved private categorical lemma `scalar_comparison_paste` combines each pair of endpoint
squares using naturality and functoriality. It is used once for integers and once for the
shifted full-units target. Existing statements, definitions, and public imports are unchanged.

Added three modules: `TowerChernPullbackData` defines the intermediate exact R inverse image,
its forgetful square, integer-normalized coefficient unit, and root comparison constrained by
a morphism of actual Kummer short complexes; `TowerChernReductionPullback` states the remaining
Z-to-R comparison; `TowerChernScalarPullback` states the remaining R-to-A comparison and
constructs the common intermediate data. Both theorem modules have one named public hole.
Both proof imports in the item are private. No other existing module is changed.

This is a decomposition, not a complete proof of geometric coefficient coherence. The new
obligations separate two actual stages of the original construction: the reduction theorem
never compares A-modules or scalar-extended lines; the scalar theorem starts on arbitrary
R-derived objects and contains neither the integral reduction functors nor their unit/root
identifications. The original theorem performs the nontrivial pasting at those identifications.
The data are eliminated inside proofs of propositions; no definition chooses arbitrary data
from an unproved existence assertion.

## Proved and sorry left

Original item: one hole, in `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_chernRealization_pullback`.
Its body is replaced by the complete composition proof; zero holes remain in that module.
`firstChern_eq_realization` stays proved with its original body.
The private `scalar_comparison_paste` is proved without holes.

Two holes are added:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_chernReduction_pullback`, node
  `lem-sp-tower-chern-reduction-pullback`, in `Sheaf.Paper.TowerChernReductionPullback`.
- `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_chernScalar_pullback`, node
  `lem-sp-tower-chern-scalar-pullback`, in `Sheaf.Paper.TowerChernScalarPullback`.

Thus one original hole is decomposed into two strictly smaller stage obligations; the textual
net is minus one closed-minus-added, with no claim of a sorry-free proof. There are no holes
in the data module and none inside definitions. Each remaining theorem has its source, complete
proof plan, and node. The sandbox compile completed successfully for all four modules; the item and both split statements
therefore typecheck with the current published library. Delivery preflight is the remaining check.

## No longer needed

No existing imports or modules are withdrawn. The item keeps both original public imports.
The data module imports TowerClassChern directly instead of the broader TowerClassPullback
interface used during development. No unused proof-dependency imports were added. The only new proof imports are the two theorems
used in the composition proof. Their common data module is publicly imported by each because
it occurs in their statements; the scalar module also imports the existing projective-class
interface containing `LinePullback.derivedIso`.

The item's direct proof dependencies are now the two new stage lemmas. The following original
planned dependencies are still needed below them, and are not claimed globally pruned:
`def-weil-proetale-inverse-image`, `lem-coef-semilinear-derived-sections`,
`det-prop-sfb-cartesian-coefficients-twists`,
`lem-pur-algebra-diagram-pullback-extension-coherence`,
`lem-weil-pbc-exact-functor-ses-triangle-image`,
`lem-pur-torsion-sheaf-constant-module`,
`lem-weil-pbc-derived-single-fully-faithful`, and `det-def-sp-tate-twist-locally-free`.

The following original direct proof dependencies are unnecessary for this argument:

- `lem-sfb-successive-derived-quotient-normalization`: pasting the two given extensions directly
  needs no comparison with direct Z-to-A extension.
- `lem-sf-derived-concentrated-single`: the given target normalization already identifies the
  adjunction transpose with the signed Kummer boundary; no cohomology concentration argument
  is required for the Z-to-R endpoint comparison.
- `lem-pur-derived-change-of-rings`: its general theory remains behind the algebra-diagram
  comparison, but no separate application is needed in the item's or the new lemmas' plans.
- `det-sp-tower-classes`: no existence theorem for TowerClasses is used; normalized Chern data
  and their exact Kummer sequence are already hypotheses.
- `det-sp-coefficient-towers-abelian`: the existing system-category and semilinear interfaces
  provide the structures used here; its bundled theorem is not applied independently.

This is pruning of this proof plan only, not a claim that the associated modules have left
all target import closures. No module is deleted.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The general algebra-diagram coherence declaration was read in
`AlgebraDiagramPullbackExtensionCoherence` and its data interface: it concerns its own diagram
sites and normalized scalar presentations, rather than the recorded Chern reductions and
section-normalized geometric coordinates directly. Transporting that comparison and verifying
the unit/root endpoints are the two remaining stage obligations, not an immediate application.
The declarations being proved below may themselves have holes; that was not treated as an
obstacle. The old plan's comparison with direct Z-to-A extension is unnecessary.

The quotient exponent is n+1 throughout the Lean definitions, including n=0. The split was
checked on the identity map, empty schemes, the trivial root tensor after a compatible-generator
cover, the first positive quotient, ramified E, and arbitrary nonflat f. For identity maps the
intermediate maps can be the identity after transporting the specified Chern models. Empty
schemes give the unique maps of the zero sheaf categories. No cancellation by a coefficient or
ell is used. Ramification affects A but not the integral reduction step. Exact geometric
inverse image, not flatness of the scheme map, is used. The root comparison is not a freely
chosen isomorphism: the first and last components of an actual Kummer short-complex map fix
its boundary compatibility. All shifts are the canonical exact-functor comparisons.

The current item source exists although it has an old quarantine row in `coord/rework.tsv`.
Work started from that current source, preserving its Lean attachment and public dependencies;
no quarantined path or declaration is withdrawn. The current E9 return file is empty.

## New nodes

`def-sp-tower-chern-pullback-intermediate` records the new intermediate pullback data and its
canonical exact-derived unit/root maps, together with the scalar root-target factor. This is
a structure with explicit normalization fields, not an existence assumption or a chosen witness.

`lem-sp-tower-chern-reduction-pullback` records the Z-to-R comparison for any such intermediate
pullback. Its proof plan uses algebra-diagram coherence, uniqueness of quotient-ring actions,
and adjunction transposes of the specified integer/Kummer normalizations. It has no A-stage
comparison in its conclusion.

`lem-sp-tower-chern-scalar-pullback` records construction of the intermediate inverse image and
the R-to-A comparison. Its endpoint equations are on the R coefficient and shifted root modules;
there is no integral-unit/root identification or line-bundle class. Its proof plan uses normalized
scalar association and the ordinary root-tensor counit. The item's node records the actual
composition proof. No change record is needed: only the item's proof, its node, and new modules
and nodes are changed. The unit route and all source-library declarations are preserved.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
