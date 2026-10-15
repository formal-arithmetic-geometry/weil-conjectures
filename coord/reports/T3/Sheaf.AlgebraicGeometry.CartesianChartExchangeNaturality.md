## What changed

Repaired reviewer X-ff7e3's forced-adaptation return. The packet contains only
CartesianChartExchangeNaturality and the new RawRestrictedCohomologyClass and
CartesianChartRestrictedMapEvaluation modules. CartesianHigherImageChartSystem,
RawAffineRestrictedCohomology, RestrictedOverAbelianComplexData, and
CartesianChartClassPullback are used unchanged from the repository; their
rejected adaptations, wrappers, generic pullback, and obsolete change record
are excluded. No repository module or node is deleted.

The item's original exchange theorem is proved with its byte-for-byte original
signature. It combines the existing chartRawAdj_classPullback calculation with
the evaluation of the restricted cone map. The second reader closed that
remaining evaluation obligation using the existing chartRestrictedMap_eq_rawAffine,
rawRestrictedCohomologyClass_map, the explicit cached-class equation, and the
existing chartCohomologyIso_eval. The newly written private duplicate of
chartRawAdj_classPullback was removed in favor of its library theorem, imported
only for the proof. No new statement is left open.

The canonical raw class is the inverse of the specified evaluation isomorphism.
The chart raw class is its explicit raw pullback with the upperStarComp
coefficient map. The inverse is uniquely determined by that isomorphism; no data
are supplied by arbitrary witnesses of an unproved existence statement.

## Proved and sorry left

Original hole closed:
AlgebraicGeometry.Etale.cartesianChartCohomologyLift_exchange
(node lem-sc-cartesian-chart-exchange-naturality), the item's sole original hole.

The second reader also closed the proposed split-off hole:
AlgebraicGeometry.Etale.cartesianChartRestrictedCohomologyMap_eval
(node lem-sc-cartesian-chart-restricted-map-evaluation).

The new constructions and all their properties are proved:
AlgebraicGeometry.Etale.rawRestrictedCohomologyClass,
AlgebraicGeometry.Etale.rawRestrictedCohomologyClass_spec,
AlgebraicGeometry.Etale.rawRestrictedCohomologyClass_map,
AlgebraicGeometry.Etale.rawRestrictedCohomologyClass_naturality,
AlgebraicGeometry.Etale.cartesianChartRestrictedRawClass, and
AlgebraicGeometry.Etale.cartesianChartRestrictedRawClass_eq.

Holes added by the delivery: none. Holes left in delivered modules: none.
This closes one original hole without adding a lower hole. This is not a
one-for-one decomposition. The scratch axiom audit of all eight public declarations listed above reports
only propext, Classical.choice, and Quot.sound. In particular, the exchange
theorem has no inherited sorryAx either.

## No longer needed

Removed direct proof imports from the item's repository version:
Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality,
WeilConjectures.SixFunctors.BaseChange.DerivedComparison,
Sheaf.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility, and
Sheaf.AlgebraicGeometry.CartesianHigherImageTransitions.
The original unused private cartesianChartAdjunct_spec is removed. The second
reader also removed the new private chartClassPullback_exchange duplicate and
replaced the direct Comparison import with the existing Conclusion theorem.
All newly added proof imports are plain import/import all, not public import.

All three old proof_deps are replaced as direct edges:
lem-sbc-raw-restricted-cohomology-comparison-naturality is used through the
canonical raw-class API;
def-sc-cartesian-derived-image-map and
lem-sbc-abelian-higher-direct-image-class-compatibility remain in the existing
raw-adjunction calculation's dependency route. They are not claimed as pruned
from the targets' import closure. No existing library module is withdrawn, and
no module is claimed pruned from that closure.

The rejected definition adaptations, integer wrappers, generic chart pullback,
lift-equation declarations, and explicit cone-leg replacement are unnecessary.
The unlanded def-sc-cartesian-chart-cohomology-pullback node is excluded.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous packet claimed four definition adaptations were necessary for
performance, but reviewer X-ff7e3 compiled their originals against the delivered
dependencies. This delivery accepts that finding and uses those originals.
There is no forced adaptation to a module held by another group.

The first repair report called the evaluation identity unfinished. The second
reader found and reused the existing chartRestrictedMap_eq_rawAffine bridge.
Explicitly typing the cone leg and reducing the cached-class equation's local
lets allowed the final equality to close without changing any definition.
The existing chartRawAdj_classPullback also made the newly written private
exchange helper unnecessary.

The original node's blueprint.from names a support node rather than a blueprint
node. The new nodes retain the existing ancestor route through
sbc-thm-algebraically-closed-invariance. The unit record sk-thm-vanishing already
has empty realized lists; this support-node delivery changes no unit record or
unit step, and continues the same geometric comparison-square route.

## New nodes

- def-sc-raw-restricted-cohomology-class: the uniquely specified inverse of raw
  evaluation, with its proved evaluation and pullback equations, in
  RawRestrictedCohomologyClass.
- lem-sc-cartesian-chart-raw-adjunction-pullback: attaches the existing proved
  chartRawAdj_classPullback in CartesianChartExchangeConclusion, which combines
  chartRawAdj_pullback and chartClassPullback_postcomp. No duplicate theorem or
  module is added for it.
- lem-sc-cartesian-chart-cohomology-evaluation: attaches the existing proved
  private chartCohomologyIso_eval in CartesianChartExchangeEvaluation. It is
  reused via proof-only import all; no duplicate theorem or module is added.
- def-sc-cartesian-chart-restricted-raw-class: the explicit raw pullback of the
  inverse-evaluation stage class, with its proved defining equation, in
  CartesianChartRestrictedMapEvaluation.
- lem-sc-cartesian-chart-restricted-map-evaluation: the now-proved evaluation
  of the actual restricted cone map. It contains neither exchange nor stage lift.

The change record is
coord/changes/T3-cartesian-chart-exchange-proof-local-attributes.md.
It documents proof-local attributes and the original private helper's removal,
which the static visibility check conservatively flags. No existing public
signature or definition changes.

## Second reading by T3

1. Interface check: read the complete three delivered modules and diffed the
   existing one against the repository. The signature of
   cartesianChartCohomologyLift_exchange is byte-for-byte identical. The only
   original declaration removed is the unused private cartesianChartAdjunct_spec;
   no public declaration, definition, hypothesis, or conclusion changes. The four
   rejected adaptation files are absent from the delivery, so the original
   diagram, cone, cohomology bodies, map bodies, and stage lift are preserved.
   Verdict: passes.

2. Proof check: compiled the original proposed packet, then the repaired lower
   theorem and the final delivered set through lcompile.py. Searched the entire
   delivered Lean tree for sorry and prohibited declarations/options: none.
   The raw-class definitions use an inverse isomorphism and an explicit raw
   pullback, with no hollow data. The scratch axiom audit prints the axioms of
   every new public declaration and the original exchange theorem. All eight
   report exactly propext, Classical.choice, and Quot.sound, with no sorryAx.
   Final set compilation took 3.6 s, 53.0 s, and 57.7 s respectively, within
   the single-file limit. Verdict: passes.

3. New-statement check: read Stacks Tags 0EYM (second proof's canonical
   comparison square) and 03Q8 (restricted cohomology presheaf), and matched each
   new statement's objects and coefficients to the actual constructions. The
   raw class is uniquely specified by evaluation; its evaluation and naturality
   equations follow from the isomorphism identities and existing naturality.
   The cached chart class is exactly the displayed raw pullback, not a chosen
   witness. The evaluation theorem is strictly the evaluation side of the
   square, and is now proved rather than split off. It requires no exchange
   invertibility, affineness, qcqs, or cofilteredness. Checked degree zero, the
   identity leg, zero coefficients, and empty test schemes: the same evaluation
   and inverse identities apply; no nonzero or nonempty hypothesis is used.
   An empty indexing category is vacuous because i is an input. Repeated
   LeanFinder and Loogle searches with evaluation/adjunction terminology, and
   rg over lean/Sheaf and lean/WeilConjectures, found the existing map bridge,
   raw-adjunction conclusion, and chart evaluation ingredients, all reused.
   Generic search hits did not state the complete chart-cone equation.
   Verdict: passes; no split-off sorry remains.

4. Route and pruning check: read the original plan, its dependency declarations,
   and sk-thm-vanishing.json. The proof still compares raw pullback and derived
   exchange through the specified chart comparisons; it changes no unit-level
   step. The second reader removed the duplicate private exchange helper and
   imported the exact existing conclusion theorem. The map conversion is the
   existing reflexivity theorem rather than another newly stated lemma. The
   four original unused direct proof imports and all three replaced direct DAG
   edges are accounted for above, without claiming transitive modules pruned.
   Public imports serve signatures or actual definitions; new imports serving
   proofs are plain import/import all. Verdict: passes.

5. DAG check: opened all six delivered node records. The item's proof_deps name
   its actual raw-class, chart-class, raw-adjunction, and evaluation ingredients.
   The raw-adjunction attachment now names the existing class-pullback conclusion
   actually applied. The evaluation node records the literal-map bridge,
   naturality, cached-class equation, and chart evaluation, with proof_deps the
   union of its steps' uses. Its declaration list no longer also claims the
   separate definition node's declarations. New nodes retain their sources,
   three search kinds, creation record, ancestor, chapter, unit, and Lean record.
   No new assumption was substituted for the old item. Verdict: passes.

Second-reading changes: closed cartesianChartRestrictedCohomologyMap_eval;
added its two proof-only imports; removed the duplicate private exchange helper
in favor of chartRawAdj_classPullback; corrected the raw-adjunction attachment,
evaluation proof records, pruning account, and report. No existing statement or
definition was changed.
