## What changed

Completed all four proofs in `Sheaf.Paper.CanonicalOriginCompactSupportComposition`.
The two unit laws and associativity descend the existing specified etale equations through
the fully faithful etale-origin equivalence. Private comparison-component lemmas establish
the actual transported model equations. A private categorical diagram lemma proves the
associativity calculation before specializing to the derived categories, avoiding expensive
unfolding. `originWitnessFixed_property` transports the retained witness through the derived
finite-coefficient equivalence and its unit isomorphism.

All public signatures, visibility, docstrings and public imports are preserved. Three
`preimageIso` calls have their already-inferred endpoints made explicit; the canonical
constructions and their elaborated meaning are unchanged. This is documented in
`coord/changes/S4-origin-composition-preimage-endpoints.md`.

The node's proof, proof dependencies and proof origin now describe this reuse of the
existing etale tower implementation. No new public result or module is introduced.

## Proved and sorry left

Closed 4 original holes, all on node `thm-sf-comp-composition`:

- `AlgebraicGeometry.ProEtale.originComposition_id_left`.
- `AlgebraicGeometry.ProEtale.originComposition_id_right`.
- `AlgebraicGeometry.ProEtale.originComposition_assoc`.
- `AlgebraicGeometry.ProEtale.originWitnessFixed_property`.

Holes added: 0. Holes left: 0. No split-off theorem, axiom or hollow definition.
All private helper theorems are proved. The complete module compiled without warnings
or errors using `lcompile.py`; the delivery dry run repeats validation and axiom checks.
This closes the local proofs from existing declarations, without claiming that every
upstream dependency has already been proved.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`.
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`.
- `Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`.
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.Paper.CompactificationCoherence`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.Paper.FiniteDirectImageComposition`.
- `Sheaf.Paper.RefinementComparisonIsomorphism`.
- `WeilConjectures.Compactification.NagataCompactification`.
- `WeilConjectures.Compactification.Refinement`.

The removed imports are not required by any new proof or public construction. In particular,
we do not redo Nagata compactification, compatible triangles or compatible towers,
proper/open interchange, refinement normalization, direct-image composition or their
coherence here: the specified `Etale.rightDerivedLowerShriekPlusCompIso` implementation
already carries that tower route and its coherence laws. That implementation is the
existing declaration recorded by `lem-amb-etale-compact-comparisons`, now a direct proof
dependency; the source construction itself is unchanged.

Removed direct proof dependencies:

- `lem-weil-pbc-finite-type-over-noetherian`.
- `lem-weil-pbc-locally-noetherian-quasi-separated`.
- `lem-weil-pbc-qcqs-morphism-permanence`.
- `def-compact-support-direct-image-detailed`.
- `lem-weil-extension-by-zero-exact`.
- `lem-sf-comparison-pullback-exact`.
- `lem-cbc-proetale-extension-zero-comparison`.
- `prop-weil-pbc-comparison-direct-image`.
- `thm-nagata-compactification`.
- `lem-weil-pbc-compatible-compactification-triangle`.
- `def-weil-compactifications-refinements`.
- `lem-weil-extension-by-zero-adjunction`.
- `lem-cbc-proper-open-interchange-coherence`.
- `lem-sf-proper-open-comparison-site-normalization`.
- `def-sf-refinement-comparison-isomorphism`.
- `prop-compactification-coherence-detailed`.
- `lem-weil-derived-direct-image-composition`.
- `lem-cbc-compactifiable-compatible-tower`.
- `def-pc-fibre-product`.

These nodes may remain needed inside the imported comparisons or the canonical etale
implementation, and by other targets. This report claims direct dependency pruning,
not their global unreachability. The old explicit tool-use approvals
`lem-cbc-proetale-extension-zero-comparison`, `lem-weil-extension-by-zero-adjunction`,
`lem-cbc-proper-open-interchange-coherence`, and `lem-cbc-compactifiable-compatible-tower`
are removed from this node because their work is delegated to the existing implementation.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's geometric argument is implemented already by the
canonical etale API, so duplicating it in this module is unnecessary. The full-subcategory
and precomposition functors retain all ambient morphisms, and the proof uses their
actual fully faithful preimage operations, without choosing an unrelated isomorphism.

The interrupted sandbox contained substantial unverified work and no report or delivery;
it was retained, checked against current sources, completed and compiled. Low-heartbeat
and profiling options used during diagnosis were removed. Local irreducibility and the
transparency setting prevent large comparison constructions from being unfolded in the
coherence calculations. No external module required an adaptation.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
