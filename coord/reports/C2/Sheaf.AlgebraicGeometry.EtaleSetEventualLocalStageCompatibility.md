## What changed

Proved `AlgebraicGeometry.etaleSet_eventualLocalStageCompatibility` in
`Sheaf.AlgebraicGeometry.EtaleSetEventualLocalStageCompatibility` without changing
its signature, visibility, definitions, or existing docstrings. Added ten private
proof imports and two fully proved private helpers, `comparison_equal_open` and
`comparison_eventually_equal`. No additional modules or public declarations are added.

The first helper applies the agreement-open criterion to sections on an arbitrary
stage object. The cartesian-unit equality theorem and injectivity of the inverse-image
composition isomorphism identify comparison equality with whole inverse image of the
agreement open. The second helper constructs the pullback diagram on the initial tail
`Over j.left`, proves that its cone is limiting using connected pullback limits, and
applies Mathlib `AlgebraicGeometry.exists_map_eq_top`. Equality remains true at every
later refinement by taking inverse images of that open.

The main proof uses `etale_pair_restriction_detection` to obtain each qcqs overlap,
derives equality of limit restrictions directly from comparison naturality and the
equations with the given section, and applies the second helper. Naturality and the
overlap detection theorem then give stable pairwise matching. Cofilteredness selects a
common stage for all finitely many ordered pairs, thinness identifies its composite
arrows, and cancellation of the final base-change isomorphism gives exactly
`Presieve.Arrows.Compatible`. Empty families and empty overlaps need no exceptions.
All classical witness choices occur inside proofs, not definitions.

Updated the existing node's `proof`, `proof_deps`, and `proof_origin` to record the
agreement-open route. The unit `sk-thm-iff` realizes its statement and step in
`lemma-weil-pbc-property-iff-acyclicity`; none of those unit realizations is bypassed.
The change is entirely below that unit level.

The unchanged signature includes a named `V'` used only through implicit object-family
arguments. The theorem locally disables only the unused-variable style linter to
retain that signature verbatim. No trust or axiom check is disabled.

Sources checked: [Stacks 09XM](https://stacks.math.columbia.edu/tag/09XM), the
agreement-open criterion, and [Stacks 01Z3](https://stacks.math.columbia.edu/tag/01Z3),
the compact closed-complement limit argument, together with Mathlib
`AffineTransitionLimit.lean`, lines 180–198. The actual limit-containment theorem is
already recorded by `lem-weil-pbc-limit-image-contained-in-open`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.etaleSet_eventualLocalStageCompatibility`
(node `lem-weil-pbc-sets-eventual-local-stage-matching-compatibility`).

Holes added: zero. Holes left in the delivered module: zero. Both private helpers
have complete Lean proofs. Existing imported statements remain separate items; this
report makes no assertion that all transitive dependencies are axiom-free.

Validation uses `lcompile.py` on the complete module and the `deliver3.py --no-push`
compile, axiom probe, and preflight. The first worker performed no library build,
landing, or push; the second reader performs the delivery below.

## No longer needed

Removed six original private proof imports: `AffineEtaleInverseImageComparison`,
`AffineEtaleSiteColimit`, `EtaleInverseImageAlgebraicStructures`,
`EtaleSetInverseImageCompositionUnits`, `FullAffineEtaleTopos`, and
`SiteSheafificationSectionsLocal` (the first five under
`Sheaf.AlgebraicGeometry`, the last under `Sheaf.Paper`). The algebraic-structures
and composition-units modules remain available transitively through the unchanged
public comparison import. Both original public imports are needed for the
unchanged statement and its comparison definition. Every added proof import provides
an API applied in the proof: agreement opens, cartesian units, overlap detection,
affine-transition limits, affine and qcqs permanence, initiality of the tail,
connectedness of a cofiltered category, connected pullback limits, or cartesian
pullback-map witnesses.

The following planned proof dependencies and their modules are not needed by this
proof and have been removed from this node's `proof_deps`:

- `lem-weil-pbc-affine-etale-site-colimit`:
  `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`.
- `lem-weil-pbc-affine-etale-site-topos`:
  `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`.
- `lem-weil-pbc-sets-affine-etale-inverse-image-comparison`:
  `Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison`.
- `lem-weil-pbc-site-sheafification-sections-local`:
  `Sheaf.Paper.SiteSheafificationSectionsLocal`.

`lem-weil-pbc-etale-inverse-image-algebraic-structures` is also no longer a direct
proof dependency: no clause of its theorem is applied. Its module remains needed
transitively for the existing `Scheme.etaleSetPullback` definition, so this delivery
does not claim that entire module is pruned from the targets' closure. Likewise the
original comparison-composition-units module remains necessary to define the
comparison and to provide its isomorphism. Qcqs permanence and base-change finite
limits remain used through Mathlib. Global reachability of the listed modules is for
the maintainer's queue to compute, not asserted by this report.

## Where the brief, the DAG or earlier work was wrong

The original colimit-site route is unnecessary for this statement: agreement opens
and the existing compact affine-transition limit theorem give eventual equality on
arbitrary stage objects directly. The existing finite-matching theorem could not be
applied unchanged because its objects descend from the initial stage, whereas this
statement allows arbitrary affine objects at stage j. No mathematical error in the
statement was found. No statement or definition correction, forced adaptation, new
node, or change record is needed.

## Second reading by C2

1. Compared the delivered Lean module and node with the repository versions. The
   sole existing declaration's signature and visibility are byte for byte unchanged;
   the declaration-diff tool reports `statement_changed []`. Both public imports
   remain unchanged. There are no definition changes, adapted modules, new public
   declarations, or change records. Verdict: pass.
2. Compiled the full module with `lcompile.py` without errors or warnings. Compiled
   a scratch copy with explicit `#print axioms` for both private helpers and
   `AlgebraicGeometry.etaleSet_eventualLocalStageCompatibility`: all three use only
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Scanned the
   delivered source for holes and forbidden trust mechanisms: none. Every selected
   witness is local to a proof; no data definition is added. Verdict: pass.
3. No statements were split off and no holes were added. Read the agreement-open,
   cartesian-unit equality, and overlap-detection APIs used by the private helpers.
   The agreement criterion is applied to the first projection of the cartesian
   pullback, not asserted as injectivity of an arbitrary unit. The compactness
   hypothesis follows from quasi-compactness of the overlap structure map and the
   compact base. Empty overlaps satisfy the same open-containment argument; for
   n = 0 the finite set of pair witnesses is empty and the inserted j still supplies
   a refinement. Verdict: pass.
4. Searched the library by eventual equality, finite matching, and open containment;
   read `etaleAffineSection_sameStageEquality`, `etaleSetSectionEventualEquality`,
   and `etaleSetSection_finite_matching`. Their objects descend from the initial
   base, unlike the arbitrary objects at j here; they are not direct replacements.
   Read Mathlib `exists_map_eq_top` and checked its cofiltered, compact-stage,
   affine-transition, and limiting-cone hypotheses against the constructed diagram
   on `Over j.left`. The proof uses this existing theorem directly and leaves no
   lower holes. All new imports are private and provide APIs used by this argument.
   Checked `dag/units/sk-thm-iff.json`: its statement and step are realized by
   `lemma-weil-pbc-property-iff-acyclicity`, which is not bypassed by the change to
   this node below the unit level. The no-longer-needed list includes every removed
   old proof dependency and distinguishes direct-import removal from global pruning.
   Verdict: pass after correcting the import-removal report.
5. Checked the node diff: only `proof`, `proof_deps`, and `proof_origin` change.
   The union of step dependencies equals `proof_deps`; the steps follow the Lean
   argument (overlaps, agreement open, initial-tail pullback limit and eventual
   containment, stable equality and finite common refinement). No new node is
   needed for a holed statement because there is none. Verdict: pass.

Second reading changed only this report: corrected the false claim that no original
imports were removed, listed all six removed private imports, clarified that the
first worker had not pushed, and recorded the independent compilation, signature,
axiom, dependency, and unit-route checks. No Lean repair was necessary. Closed holes:
`AlgebraicGeometry.etaleSet_eventualLocalStageCompatibility` (one of one). Added
holes: none. Delivery is a proof, not a decomposition. No whole-module pruning is
claimed without the maintainer's reachability computation.
