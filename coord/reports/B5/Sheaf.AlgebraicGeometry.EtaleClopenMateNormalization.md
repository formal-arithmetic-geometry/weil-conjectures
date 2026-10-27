## What changed

Proved the two remaining theorems in `Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization`.
The proof follows the clopen lift, open-unit, support-inclusion, termwise transpose,
and derived-adjunction route. The existing `Sheaf.CategoryTheory.DerivedExactMate` theorem supplies the derived-unit
calculation. The existing helpers in
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` transport the unit
between homotopy complexes and complexes. The return identified four duplicate private
helpers: `exact_factor_Q`, `right_derived_plus_unit`, `right_unit_Q_naturality`, and
`right_unit_Q_obj_iso`. They are now removed from the item. Their existing declarations
are reused through the proved conjunction
`CategoryTheory.derivedComplexUnitCompatibility`. Its proof module uses `import all`
to access the existing private proofs; the item imports the compiled conjunction
module normally. The comparison module is unchanged. `derivedComplexUnit` explicitly
constructs the same quotient-unit-quotient composite. The geometric support-inclusion proof retains the explicit isomorphism
epimorphism used in its open-unit cancellation.
The derived normalization and ambient compatibility use right-derived uniqueness.
The localization constructors share their generic terms, and the final theorem
applies the proved formulas directly. The four-module packet compiles without warnings
(`repair-original-normalized-packet2.log`).
All five unchanged consumer checks pass: site transport 6.2 s, alpha site transport
3.3 s, single-level transport 3.1 s, strict-tower calculus 56.4 s, and system
compositor normalization 8.4 s (`repair-consumer-original-*.log`).
Both existing item theorem signatures are textually unchanged.
The new data module’s accessors are proved theorems with explicit equation types.
Their proofs extract the two conjuncts, while their public types omit the rest of
the coherence conjunction. This avoids carrying the full predicate into each use.
The current source has four consumers of the changed declaration interfaces:
`Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport`,
`Sheaf.AlgebraicGeometry.FiniteClopenAlphaSiteTransport`,
`Sheaf.AlgebraicGeometry.SingleLevelFiniteProperOpenTransport`, and
`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`. Their original sources are checked alongside the retained transitive consumer
`Sheaf.Paper.SystemCompatibleCompositorNormalization`.
Consumer checks identified required public unfolding interfaces. `derivedMatePlus`
remains exposed, and `normalizedComparison` retains its original second coherence
choice. The bundle is used only through a proved family equation in the normalization
proof. All consumer sources remain unchanged; no forced adaptation is needed.

Simplified identity associators in `alpha` and identity chain compositors in
`resolutionArrow` and `transposeArrow`, and the identity exact-functor D+/D factors in
`sourceCompatibility` and `targetCompatibility`; made the existing natural-transformation result
types of `derivedMate` and `derivedMatePlus` explicit. These retain the same maps and
mathematical statements. See `coord/changes/etale-clopen-mate-identity-compositors.md`.
No source-library declaration or public import is removed.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.ClopenMateNormalization.etaleClopenMateNormalization`
and `AlgebraicGeometry.Etale.ClopenMateNormalization.etaleClopenMateResolution`, both
attached to `lem-cbc-etale-clopen-mate-normalization`: 2 of 2 existing holes closed.
No holes added or split off. The previously proved `lift_clopen` remains proved.
There are zero `sorry` in the item module and in all three new modules.

## No longer needed

Removed the four duplicate private helper declarations listed above and the duplicate
private `right_unit_Q` construction. The four proofs are reused through the
conjunction interface; its unit is an explicit construction of the same map. No module is withdrawn.

The proof does not use these declared proof dependencies:

- `lem-cbc-derived-extension-zero-base-change-underived-compatibility`: use the existing
  open-base-change unit equation directly, without the chosen-square comparison layer.
- `prop-weil-pbc-kinjective-resolutions-exist`: representatives and the resolution map
  are supplied in the theorem.
- `lem-weil-pbc-kinjective-total-derived`: use the existing right-derived-value
  isomorphism on a K-injective complex.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`: no K-injectivity of the pushed-forward
  complexes is needed in the derived-unit argument.
- `lem-weil-pbc-kinjective-hom-derived`: use compatibility of induced derived adjunctions
  with their ordinary units and counits instead of a separate derived-Hom computation.

Corresponding unused private imports from the working proof were removed:
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility`,
`Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`, and
`Sheaf.CategoryTheory.KInjectiveTotalDerived`.
The obsolete entries in `proof_deps`, proof-step `uses`, and top-level `tool_uses` are
removed. These are direct dependencies pruned from this proof; no claim is made that
other consumers cease to need those modules. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The return was correct: four helper statements were already present, but private,
in the comparison module. The proved conjunction interface permits reuse of those existing private
declarations rather than another proof. The mathematical statements are unchanged. The planned proof via K-injective pushed-forward complexes
is unnecessary: the induced derived-adjunction unit/counit equations already determine
the mate on arbitrary complexes, and the stated K-injectivity hypotheses suffice to
invert the required value maps. The unit route is retained. Identity associators and
identity chain compositors in the original definitions caused expensive conversions;
the change record documents their removal and the consumer checks.

## New nodes

`def-cbc-clopen-mate-composite` is a proved definition and component equation in
`Sheaf.CategoryTheory.ClopenMateComposite`. It packages the whiskered composite as
an irreducible definition with an explicit component API; no assumption is added.

`def-cbc-proper-open-interchange-data` is a structure and proved definition in
`Sheaf.AlgebraicGeometry.ProperOpenInterchangeData`. It bundles the same selected
comparison families with their normalization proof, preserving the uniquely
specified data while avoiding repeated dependent-choice conversion inside the item
through irreducibility. Its proved derived-field equation identifies the original
second coherence choice for consumers. Its inclusion and
derived-unit accessors expose the two normalization equations without unfolding the
entire coherence predicate.

These are definition repairs with no holes, not unfinished proof splits. They are
recorded in `coord/changes/etale-clopen-mate-identity-compositors.md`.

`def-cbc-localized-clopen-square` records the two exact-localization constructors in
the item module. `derivedAlpha` and `derivedAlphaPlus` are their direct applications
to `alpha`, removing duplicate concrete localization terms without changing the maps.

`lem-cbc-derived-complex-unit-compatibility` packages four already proved compatibility
laws in `Sheaf.CategoryTheory.DerivedComplexUnitCompatibility`. Its proof applies the
existing private helpers directly; it adds zero holes and no mathematical assumption.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
