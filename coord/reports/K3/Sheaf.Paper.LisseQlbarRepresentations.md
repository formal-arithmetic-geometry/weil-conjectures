## What changed

The theorem keeps its exact statement. Its proof now obtains the finite Galois
correspondence, assembles three independent source steps, derives normal algebraic-closure
integrality from the existing finite-field descent theorem, proves the representation
field-of-definition clause, and applies the existing regular-scheme normality theorem.

`Sheaf.RepresentationTheory.ContinuousAlgClFiniteModel` proves
`Representation.isLAdic_of_continuous_dual_coefficients`. It uses the already proved
`PadicAlgCl.exists_finiteDimensional_forall_mem`, then constructs an actual invariant
finite-field subspace with its continuous action and canonical tensor comparison.
The two finite-basis transport helpers reproduce the proved private arguments in
`Sheaf.RepresentationTheory.LAdicSubrepresentation`; no source-library file is changed.
An additional generic helper corestricts continuous entries through a closed embedding.

The 36 existing data declarations are extracted verbatim to
`Sheaf.Paper.LisseQlbarRepresentationDefs`, which the item publicly imports, so independent
proof-step modules can import their statements without a cycle. The definitions are not
split to evade the compile-time limit. The change record is
`coord/changes/lisse-representation-data-extraction.md`; there are no external consumers
of the item to adapt.

Validation: the final server `lcompile.py --all` accepted all six modules without
errors or warnings. The main assembly took 37.5 seconds and the proved representation
module 13.0 seconds. A separate profiled data-module compile took 38.0 seconds; all
profiling options were removed before the final compile. The final wrapper reported
68.1 seconds for that data module while accepting it; delivery preflight performs the
independent compile-limit check. Local irreducibility attributes keep the large predicates
folded during interface checking and do not alter exported reducibility attributes.

## Proved and sorry left

The original single hole in
`AlgebraicGeometry.ProEtale.LisseRepresentation.lisse_qlbar_representations` is closed
by a complete proof FROM three smaller statements. This is a decomposition, not a claim
that the whole representation theorem is proved without sorry: 1 upper hole closed,
3 lower holes added, net -2. No sorry remains in the item or in its data module.

The following named public theorem proofs are exactly `by sorry`:

- `AlgebraicGeometry.ProEtale.LisseRepresentation.exists_normalized_coefficient_correspondences`
  (`lem-sfb-normalized-lisse-coefficient-correspondences`): only the normalized
  correspondences and comparisons of clauses (1)--(3), given the finite correspondence.
- `AlgebraicGeometry.ProEtale.LisseRepresentation.lisse_geometric_fibres_finite_free`
  (`lem-sfb-lisse-geometric-fibres-finite-free`): only the actual free-fibre calculation,
  without connectedness, normality or Noetherian assumptions.
- `AlgebraicGeometry.ProEtale.LisseRepresentation.has_lattice_of_normal`
  (`lem-sfb-normal-lisse-finite-coefficient-lattice`): only finite-coefficient lattice
  existence on normal schemes, independent of any representation correspondence.

The new theorem `Representation.isLAdic_of_continuous_dual_coefficients` is completely
proved, including its private helpers. The existing finite-field descent supplies the
normal algebraic-closure clause in Lean, and regular-implies-normal is proved from the
existing stalk theorem. None of these arguments adds a hole. Each new obligation has
its source, complete proof in words, edge-case discussion and matching DAG node.

## No longer needed

The original direct imports for the unfinished construction and normal-lattice argument
are removed from the assembly module. Their dependencies are retained below the matching
new nodes, and are NOT claimed as mathematically pruned:
`ContinuousRingUniverseRealization`, `EmbeddedLatticeCoefficientComparison`,
`IntegralLisseReductionEquivalence`, `LisseModuleInverseImage`,
`ProEtaleInverseImageStalk`, `ProEtaleComparisonStalk`, `ProEtaleConstantSheafStalk`,
`CartesianCoefficients`, `IntegersProfiniteTower`, `NormalizedTowerFree`,
`CompletedCondensedCoefficients`, `CoefficientFiniteDescentSections`,
`ProEtaleInverseImageTensorComparison`, `ProfiniteStableLattice`,
`LocalFieldIntegralBasis`, `LisseLatticeClassSheaf`, `NormalLocallyConstantFiniteSection`,
and `ContinuousFiniteEtaleLatticeDescent`.

The standalone countable-field/Baire/open-coset assembly is replaced by the proved compact
matrix descent theorem. The direct import
`Sheaf.NumberTheory.Padics.CountableClosedFiniteCover` and the direct proof dependencies
`lem-sfb-algcl-countable-closed-finite-cover`, `lem-sfb-baire-closed-cover-interior`,
`lem-dl-a1-open-subgroup-finite-cosets` are therefore unnecessary in this proof route.
The explicit `Mathlib.Topology.Baire.Lemmas`, `Mathlib.Topology.Baire.LocallyCompactRegular`,
`Mathlib.Topology.Algebra.OpenSubgroup` and `Mathlib.Topology.Algebra.Group.Quotient`
imports are removed from the item. The compact matrix theorem retains its own Baire proof.

The item also no longer directly imports `WeilConjectures.RingTheory.RegularRingNormal`:
the existing `IsRegular.isIntegrallyClosed_stalk` API supplies the regularity clause,
which is clause (1) of `rem-pc-regular-normal`. The DAG cites this existing
regular-scheme assertion; the proof uses its source-library implementation directly.
`lem-weil-pbc-regular-ring-normal` is no longer a direct proof dependency. This is a
proved source-library alternative, without modifying or withdrawing any source declaration.
The extracted data module imports only data: the original public imports of
`GaloisLisseRepresentations` and `CoefficientFiniteDescentLisse` become private proof
imports of the assembly. Its unused public imports of `FLCFiber`,
`ProEtaleFiniteLocalSystemsTwist`, `ProfiniteFiniteConstantLocalModel`,
`SeparablyClosedLisseSplitTrivialization`, `CondensedPointCoefficients`, and
`StratifiedLattice` are removed. The underlying proof ingredients remain recorded
in the new obligations where needed; this is not a claim they are globally obsolete.

The direct `Mathlib.AlgebraicGeometry.Noetherian`, `Mathlib.Topology.NoetherianSpace`,
and `Mathlib.Order.WellFounded` imports are unnecessary for the assembly. The noetherian
space fact remains in the normal-lattice obligation; quasi-separatedness is used by the
assembly through the existing public Noetherian API.

The nodal-curve paragraph is a warning in the source, rather than a conjunct of the
Lean Conclusion. It is not used in the proof of that Conclusion, so
`sk-lem-stratified-lattice` and the warning's second use of
`lem-pod-profinite-stable-lattice` are removed from the item's proof steps.
The existing statement dependencies and all upstream declarations remain intact;
no whole-library pruning count is asserted. The following top-level tool approvals move out of the assembly node; their uses in
the new proof obligations remain recorded there where needed. The independent reader
may record tools for the new nodes. Removed approval IDs:

- `def-weil-l-adic-coefficient-extension`
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`
- `lem-sfb-continuous-ring-universe-realization`
- `lem-sfb-embedded-lattice-coefficient-comparison`
- `lem-sfb-integral-lisse-reduction-equivalence`
- `det-pe-finite-local-systems-twist`
- `lem-sfb-lisse-module-inverse-image`
- `lem-sfb-separably-closed-lisse-split-trivialization`
- `det-pe-condensed-point-coefficients`
- `lem-pur-proetale-inverse-image-stalk`
- `lem-cbc-proetale-comparison-stalk`
- `lem-weil-proetale-constant-sheaf-stalk`
- `sk-prop-sfb-cartesian-coefficients`
- `lem-sfb-integers-profinite-tower`
- `lem-per-normalized-tower-finite-free`
- `sk-prop-sfb-qlbar-colimit-x`
- `det-lem-coefficient-finite-descent-sections`
- `lem-pur-proetale-inverse-image-tensor-comparison`
- `lem-sfb-local-field-integral-basis`
- `lem-weil-pbc-lisse-lattice-class-sheaf`
- `lem-a1-normal-locally-constant-finite-section`
- `lem-weil-pbc-lisse-lattice-finite-etale-descent`
- `lem-weil-pbc-regular-ring-normal`
- `lem-sfb-algcl-countable-closed-finite-cover`
- `lem-sfb-baire-closed-cover-interior`
- `lem-dl-a1-open-subgroup-finite-cosets`
- `sk-lem-stratified-lattice`

## Where the brief, the DAG or earlier work was wrong

The existing `new-e4-galois-adic-from-finite` and the adic conclusion of
`Scheme.galois_lisse_representations` require separatedness and invertibility of ell,
and use a different lisse-adic source category. They cannot establish this item's
unrestricted condensed-coefficient clauses merely by instantiation. Its finite
correspondence conclusion does apply with the present hypotheses and is used directly.

Conversely, steps 14--15 had an exact proved matrix-descent ingredient in
`WeilConjectures.RepresentationTheory.IntegralModel`. Reusing it eliminates a separate
countable-cover/open-coset development. The invariant-subspace construction and topology
comparison still need proof and are supplied here; an arbitrary scalar isomorphism is
not used as a descent witness.

The shared `dag/units/sk-lem-finite.json` currently records the Poincare-duality
perfectness unit, while this node lies in sec-six-functors. Its realized fields do not
name the representation theorem. This is existing unit-ID bookkeeping; no unit or
chapter is changed. The representation theorem's own clauses and their source route
are retained, including integral reduction before rationalization and finite-field descent.

Edge cases checked: rank zero gives an empty coordinate basis and zero invariant space;
free geometric fibres need no normality; lattice existence includes zero rank;
normality is assumed only for the two integrality conjuncts. For an arbitrary supplied
finite correspondence, its finiteEvaluationAction compares every coefficient action
with the same c.γ, so quotient compatibility is retained. There is no separatedness,
residue-characteristic or ell-invertibility assumption added to any existing statement.

## New nodes

`def-sfb-lisse-representation-data` records the 36 unchanged data declarations extracted
from the item. It introduces no arbitrary object from a mere existence theorem.

`lem-sfb-normalized-lisse-coefficient-correspondences` carries the original steps 1--11,
with the independent free-fibre calculation as an explicit dependency. It is strictly the
correspondence construction, not the whole Conclusion under a different name.

`lem-sfb-lisse-geometric-fibres-finite-free` carries the source's Fibres paragraph.
Its planned proof pulls back a lisse module, splits a trivialization, and evaluates the
point coefficient ring; it does not construct any monodromy correspondence.

`lem-sfb-normal-lisse-finite-coefficient-lattice` carries original step 12, using the
existing lattice-class sheaf, finite normal section, finite-etale lattice descent and
embedded coefficient comparison. The algebraic-closure normality clause is derived
from this in the item rather than added as another hole.

`lem-sfb-continuous-algcl-finite-model` records the completely proved dual-coordinate
continuity to IsLAdic implication. Its matrix-descent dependency is the already closed
`lem-real-compact-matrix-coefficient-descent`.

Change record: `coord/changes/lisse-representation-data-extraction.md`.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
