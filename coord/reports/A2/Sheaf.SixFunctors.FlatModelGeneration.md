## What changed

Completed all three pro-etale proofs in `lean/Sheaf/SixFunctors/FlatModelGeneration.lean`.
The ordered stratification uses the constructible etale origin and the existing open-chain
refinement. The filtration is the exact comparison-realization of the proved etale filtration,
with its prescribed quotient objects identified by the canonical pullback and extension
comparisons. Thick generation transfers the proved etale generation theorem, after proving
intrinsic thickness and identifying intrinsic bounded constructible finite-Tor objects with
etale comparison objects. All existing public signatures, definitions and public imports are
unchanged. All added helpers are private and proved; no other Lean module is changed.

The coefficient bridges identify realization after scalar restriction, transport flatness
through its tensor comparison, and construct the linear geometric-stalk comparison from the
actual colimit cocone. For intrinsic generators, projectivity of geometric stalks detects
flatness only after descent to the etale site; conservativity of arbitrary pro-etale geometric
stalks is never assumed. The zero ring, empty scheme and empty partition are included by the
same categorical arguments. Nonreduced stratum domains are preserved throughout.

Updated `det-sf-flat-model-generation` to describe these compiled proofs and their actual
proof dependencies. The unit's stratification, extension-filtration and thick-generation route
is retained. No statement or definition repair, consumer adaptation, new node or withdrawal.

The added `CategoryTheory.Pretriangulated` namespace opening is documented in
`coord/changes/A2-flat-model-generation-proof-scope.md`, as required by preflight's
visible-command check. It changes name resolution in this file; existing public declarations
and target statement meanings are unchanged. The downstream-source scan reports no importers.

Validation: remote single-module compilation passed with no warnings or errors, in 32.1 s,
after import pruning. All lines have at most 100 characters. The existing three etale proofs
also compile. Delivery preflight supplies the final independent packet checks.

## Proved and sorry left

Closed all 3 original holes, each belonging to `det-sf-flat-model-generation`:

- `AlgebraicGeometry.proEtale_flatConstructible_orderedStratification`.
- `AlgebraicGeometry.proEtale_flatConstructible_extensionFiltration`.
- `AlgebraicGeometry.proEtale_flatConstructible_thickGeneration`.

Holes added: 0. Holes remaining in the item: 0. Statements split off: 0. This is a proof from
the existing library declarations, including the fixed-module constructible-origin theorem;
its downstream proof obligations retain their existing nodes. No assumed result or axiom was
introduced by this packet.

## No longer needed

Removed these 19 direct proof imports:

- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`.
- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`.
- `Sheaf.AlgebraicGeometry.GeometricStalkToposPoint`.
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`.
- `Sheaf.AlgebraicGeometry.OpenClosedRecollement`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.AlgebraicGeometry.SurjectiveClosedModuleInvariance`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`.
- `WeilConjectures.SixFunctors.Etale.Derived.Triangulated`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`.

The direct finite-coefficient model comparison, reduced-tail induction and surjective-closed
invariance route are unnecessary: exact comparison transports the already proved etale tower.
The pro-etale generation proof uses etale origin and the existing etale generation theorem,
so it needs no separate construction of a pro-etale bounded flat constructible model.

Removed the following old direct proof-dependency edges from this node. Definition nodes
among them remain in `stmt_deps` wherever the unchanged statements need them:

- `def-kun-derived-tensor`.
- `def-weil-closed-immersion`.
- `def-weil-constructible-subset`.
- `def-weil-derived-tensor`.
- `def-weil-pbc-direct-image`.
- `def-weil-pbc-etale-constructible-sheaf`.
- `def-weil-pbc-noetherian-ring`.
- `def-weil-pbc-proetale-operations`.
- `def-weil-proetale-constructible-sheaf`.
- `det-pe-finite-tor-comparison-noetherian`.
- `lem-cbc-open-closed-recollement`.
- `lem-fix-geometric-stalk-topos-point`.
- `lem-kun-derived-tensor-triangulated`.
- `lem-sf-comparison-pullback-exact`.
- `lem-sf-derived-homology-long-exact`.
- `lem-sfb-locally-closed-extension-coherence`.
- `lem-sfb-surjective-closed-module-invariance`.
- `lem-weil-pbc-closed-immersion-base-change`.
- `lem-weil-pbc-extension-by-zero-unit-iso`.
- `lem-weil-pbc-fibre-product-points`.
- `lem-weil-pbc-immersion-base-change-lft`.
- `lem-weil-pbc-independent-bounded-flat-kflat`.
- `lem-weil-pbc-locally-noetherian-quasi-separated`.
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`.
- `lem-weil-pbc-proetale-ringed-open-closed`.
- `lem-weil-pbc-reduced-induced-closed-subscheme`.
- `lem-weil-pbc-ringed-topos-flat-module-pullback`.
- `lemma-openclosed-vanishing-lowershriek`.
- `lemma-openclosed-vanishing-lowerstar`.
- `prop-openclosed-lowerstar-fully-faithful`.
- `sk-thm-pe-constructible-comparison`.

No Lean module is withdrawn and no source-library declaration is removed. Some of the removed
direct imports remain reachable through other imported library proofs; they retain those
consumers and their obligations. In particular, maintainer `tool_uses` approvals are retained
for nodes whose modules remain in the transitive import closure. Obsolete approvals removed:

- `det-pe-finite-tor-comparison-noetherian`.
- `lem-cbc-open-closed-recollement`.
- `lem-fix-geometric-stalk-topos-point`.
- `lem-sf-comparison-pullback-exact`.
- `lem-weil-pbc-algebraic-inverse-image-tensor-comparison`.
- `lem-weil-pbc-proetale-ringed-open-closed`.
- `sk-thm-pe-constructible-comparison`.
- `lem-weil-pbc-immersion-base-change-lft`.
- `lem-weil-pbc-fibre-product-points`.
- `new-lem-weil-pbc-proetale-surjective-closed-cover-refinement`.
- `lem-cbc-proetale-extension-zero-base-change`.
- `lem-weil-pbc-closed-immersion-base-change`.
- `lem-sfb-locally-closed-extension-coherence`.

## Where the brief, the DAG or earlier work was wrong

The live module was already restored by A4 after quarantine, with its complete etale proofs
and three pro-etale holes. This packet works from that restored source and preserves its Lean
attachment; it does not treat quarantine as withdrawal.

The old remaining pro-etale proof plan was longer than necessary. The existing fixed-module
constructible-origin theorem allows reuse of the proved etale ordered refinement and exact
filtration. The earlier etale generation theorem can itself be transported after proving the
intrinsic closure properties. No mathematical statement was disputed or weakened.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
