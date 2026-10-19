## What changed

`Sheaf.Paper.WeilCompletedTensorReflector` proves
`AlgebraicGeometry.Scheme.wfCompletionReflector` with its existing signature,
definitions and public imports. A proved private categorical lemma transports
idempotence through unit-compatible object comparisons with a fully faithful functor,
then proves the Hom bijection by cancellation and an explicit extension formula.
The application uses the existing Cech two-unit idempotence theorem and the prescribed
localization representative and unit. No arbitrary completion object or map is chosen.
`wfCompletionMap_laws` retains R5's already landed proof.

The unclaimed dependency `Sheaf.Paper.IntrinsicCompletion` now also proves
`intrinsicPresentationRoundTrip_exists` and `intrinsicCompletionUnitComponent_comm`.
The former constructs the identity-on-sections isomorphism from Mathlib's restriction
composition and identity isomorphisms, then proves its uniqueness by extensionality.
The latter applies backward restriction to the published chain-map equation and
uses naturality of that actual round trip. Both statements, every definition and
all imports remain identical. This closes the two holes directly beneath the
coefficient transport used in the new construction comparison. The proof-only
adaptation is recorded in `coord/changes/D8-intrinsic-coefficient-transport-proofs.md`.

Five new supporting modules record the construction comparisons:

- `Sheaf.Paper.WeilCompletedKoszulRoosComparison` explicitly constructs the small
  ringed site, completed coefficient sheaf, scalar sections, module equivalence and
  derived equivalence, and proves the natural termwise-limit comparison. Its only
  remaining source theorem is `completedKoszulFiniteComparison`: finite tower levels,
  their consecutive power transitions and the augmentation. It contains no products,
  cones, inverse limits or derived-category assertion.
- `Sheaf.Paper.WeilCompletedKoszulProductComparison` proves
  `completed_fiber_roos_comparison_on_complex` from that finite comparison. It proves
  that backward coefficient restriction preserves limits, using the existing
  module-to-sheaf preservation and reflection API. The site equivalence preserves
  products. Product projections prove conjugacy of 1-shift; the additive mapping-cone
  and shift comparisons and an explicit sign isomorphism identify the signed fibers.
  The comparison preserves zero-homotopy lifts. The actual coefficient round trip and
  the explicit composition comparison for mapping complexes identify the transported
  unit. Limit projections then prove its exact termwise-limit normalization.
  A private generic composition lemma checks the product and zero-lift equation
  before specializing to the actual coefficient restrictions. The rebuilt tower's
  adjacent differential is identified explicitly using `CochainComplex.of_d`, so
  this check does not unfold the completed coefficient construction.
  All generic helpers are private and fully proved; no data is extracted from the
  finite source theorem in a public definition.
- `Sheaf.Paper.WeilCompletedKoszulRepresentativeComparison` proves the derived
  comparison for every specified representative. It proves naturality of the actual
  tensor-level units, ordinary-limit unit and Roos unit. Combining the existing
  descended tensor tower with strict Roos derivation supplies a factorization of the
  actual tensor/Roos functor. Mathlib's `Localization.liftNatTrans` descends its unit;
  naturality transports the unit along the supplied realization. The final proof
  localizes the source chain isomorphism and cancels the exact module functor's
  localization factorization. This removes representative independence and its unit
  normalization from the remaining source hole.
- `Sheaf.Paper.WeilCompletedKoszulLimitComparison` proves the strict derived-limit
  comparison from that explicit-fiber comparison. It transports exact countable
  products along the module equivalence, applies the existing strict Roos derivation,
  and uses uniqueness of right derived functors after the termwise-limit isomorphism.
  The unit equation cancels that same isomorphism and is definitionally the published
  strict-limit unit on its specified localization preimage.
- `Sheaf.Paper.WeilCompletedCechComparison` proves the Cech comparison by composing
  the strict-limit comparison with the existing single-site Cech--Koszul comparison
  and canceling its unit isomorphism.

The existing reflector node and all new nodes describe the actual proof and imports.
The new site, coefficient and category constructions are real definitions with
proved laws. The remaining existential comparison is used only in proofs of
propositions; no definition extracts arbitrary data from it.

Validation: `lcompile.py --all` compiled all seven active modules together in import
order with exit code 0. The product/cone comparison took 44.9 seconds, representative
transport 37.0 seconds, strict-limit comparison 13.6 seconds, Cech comparison 4.1 seconds
and the item 7.3 seconds. The product/cone comparison and representative transport were
also compiled separately while developing their coordinate and localization proofs.
The first completed preflight rejected two new nodes for lacking LeanSearch records:
LeanFinder and Loogle count as one search kind. Actual LeanSearch searches were then
run and recorded for both nodes; the representative search returned the component
formula already used in the proof. The final required delivery probe checks the
complete packet. The accounting below distinguishes the complete item
proof from the remaining separate finite source calculation.

## Proved and sorry left

Original item holes: one,
`AlgebraicGeometry.Scheme.wfCompletionReflector`, node
`lem-weil-pbc-ringed-koszul-completion-reflector`.

That hole is closed by a complete Lean proof from the named comparisons and the
existing Cech-unit idempotence theorem. The item has zero `sorry` left.
The new `AlgebraicGeometry.Scheme.completed_fiber_strict_limit_comparison`, node
`lem-weil-pbc-completed-fiber-strict-limit-comparison`, and
`AlgebraicGeometry.Scheme.completed_fiber_cech_comparison`, node
`lem-weil-pbc-completed-fiber-cech-comparison`, have complete proofs.
`AlgebraicGeometry.Scheme.completedKoszulTermwiseLimitIso` is also fully proved.

One new hole remains:
`AlgebraicGeometry.Scheme.completedKoszulFiniteComparison`, node
`lem-weil-pbc-completed-fiber-roos-comparison`, in
`Sheaf.Paper.WeilCompletedKoszulRoosComparison`.
Its proof is exactly `by sorry`. Its docstring and node give the source, complete
finite-coordinate argument and edge cases. This is the finite-free Koszul duality
identification in Stacks Tag 0A0E, compatible with power transitions and augmentation.
It asserts no product, mapping-cone, inverse-limit, Cech, completeness or reflection
result. These later steps all have complete Lean proofs in this delivery.

`AlgebraicGeometry.Scheme.completed_fiber_roos_comparison_on_complex`, node
`lem-weil-pbc-completed-koszul-product-comparison`, is fully proved in
`Sheaf.Paper.WeilCompletedKoszulProductComparison`. In particular, no preservation of
products, signed-cone comparison or fiber-unit equation is left in the source hole.
`AlgebraicGeometry.Scheme.completed_fiber_roos_comparison`, node
`lem-weil-pbc-completed-fiber-roos-representative-comparison`, is fully proved in
`Sheaf.Paper.WeilCompletedKoszulRepresentativeComparison` by localizing that comparison
and descending the actual unit. The source result is strictly finite and separate
from both the product calculation and the reflector assertion. No elapsed-time split,
renamed reflector statement or new hole inside a definition is used.

Two further existing holes are closed in `Sheaf.Paper.IntrinsicCompletion`:
`AlgebraicGeometry.Scheme.intrinsicPresentationRoundTrip_exists` and
`AlgebraicGeometry.Scheme.intrinsicCompletionUnitComponent_comm`, both under
`def-weil-pbc-intrinsic-completion`. That dependency has zero textual `sorry` left.

Accounting: the original item hole and two existing dependency holes are removed;
one separate lower comparison hole is added. The item itself is proved from named
statements. The item-to-comparison step is a decomposition; the additional transport
proofs close two net holes in the packet. This is not a fully axiom-free proof of the
import closure. Existing holes in other imported modules are used as the stage-3
brief specifies; none is copied or newly added here.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`;
- `Sheaf.CategoryTheory.RingedCechKoszulDualLimit`;
- `Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal`;
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`;
- `Sheaf.Paper.RingedLocalizationRHomCalculus`.

The strict-limit interface and the single-site Cech comparison still occur below the
new comparison modules; they are not globally pruned. Public imports are retained
as the existing interface. No whole module is claimed pruned. In the new comparison interfaces,
`StrictRoosModel` is publicly imported by the product-fiber module, whose statement
uses it, rather than by the finite-tower module.

The actual-universe specialization no longer follows the generator-localization and
local ideal-characterization route. Its direct proof no longer uses
`lem-weil-pbc-ringed-derived-complete-elements-ideal`,
`lem-weil-pbc-ringed-localization-rhom-calculus`, or
`def-pur-derived-internal-hom`. The full local-ideal reflector of
`Sheaf.Paper.ExtendedCechCompletionModel` is not used; that module remains for its
proved unit naturality, `lem-weil-pbc-ringed-completion-unit-naturality`.
The reason is that `WfIsComplete` already means invertibility of the specified unit,
so two-unit idempotence gives exactly the required Hom bijection.

The new strict-limit proof uses `lem-weil-strict-roos-derivation` directly;
it does not need the larger `lem-weil-strict-roos-comparison` or the
K-injective computation clause of `lem-weil-pbc-ringed-strict-tower-homotopy-limit`.
The existing Cech--Koszul theorem still supplies its own strict-limit presentation.
No blueprint unit statement or realized step is bypassed: these are supporting
completion tools below the proper-base-change unit's fixed route.

## Where the brief, the DAG or earlier work was wrong

The general ringed-site reflector cannot be directly instantiated on the actual
pro-etale site: its object and Hom universes coincide, whereas those of the actual
site differ. The explicit `AsSmall` site equivalence solves the size issue without
changing the published completed coefficient ring, fiber or unit.

There is also a substantive construction distinction: the published fiber uses
exterior Koszul complexes and a signed mapping cocone, while the general ringed-site
interface uses tensor-dual factors. They are not definitionally identical. The
remaining finite source lemma records that identification rather than assuming it silently.
The unit equation is necessary; an arbitrary object isomorphism would not suffice.
Its proof in words checks the empty list, zero or invertible generators, zero ring,
and empty site. The categorical reflector argument works in arbitrary categories.

The new strict-limit proof uses `det-pe-products-exact` as a generic exact-products
tool on module sheaves, and `lem-weil-strict-roos-derivation` and
`def-weil-strict-roos-model` as generic homological tools. These have other unit
owners. The proof requires their exact-product and normalized derived-functor
interfaces; it does not replace a step of those units or the proper-base-change unit.
No maintainer-owned `tool_uses` approval was added by the worker.

Earlier sandbox drafts stay under `scratchpad/`, outside the active Lean set. They
were never landed modules and require no withdrawal. Existing signatures,
definitions, visibility and public imports are unchanged. No forced consumer
adaptation is required. The newly completed coefficient-transport proofs are in an
unclaimed module and have their own proof-only change record. All 1,597 transitive
consumers retain their signatures and definitions; the only textual uses of the two
proved theorem names are in that module itself.

The initial resumed probe reported 19 elapsed reference minutes, while the retained
`scratchpad/dry-run-resumed.log` reports 31 minutes in an earlier attempt. The
reference clock was therefore reset across interruptions; no budget metadata was
changed by this worker. Work continued on the actual proofs.

## New nodes

`lem-weil-pbc-completed-fiber-roos-comparison`, declaration
`AlgebraicGeometry.Scheme.completedKoszulFiniteComparison` in
`Sheaf.Paper.WeilCompletedKoszulRoosComparison`, is the only new hole. Source:
Stacks [Tag 0664](https://stacks.math.columbia.edu/tag/0664), the finite tensor
decomposition, and [Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E), finite-free duality in the proof of
`lemma-derived-completion-koszul`. The actual site and coefficient constructions and
natural termwise-limit comparison are also attached to this node and fully proved.
LeanFinder, Loogle and grep searches, both library roots, the blueprint and local
sources were read. Existing results give exterior bases, last-generator scalar-cone
coordinates and tensor-dual tower APIs. The proved source-library
`KoszulTensorConeCoordinates` supports induction on the finite list but supplies no
ordered tensor-dual tower identification with its transition and augmentation equations.
It is not imported by an unfinished calculation. The decomposable-wedge transition
formula compiled in `scratchpad/KoszulTransitionBasis.lean`, including degree zero and
repeated indices, and is not counted as delivered. After the final dry-run gate,
`FiniteKoszulUnitCheck.lean` also compiled: `exteriorPower.zeroEquiv_naturality`
proves that every degree-zero exterior power transition is the identity, and
extensionality proves that the empty-list generator map is the identity. These
scratch checks test the augmentation edge cases and do not add delivered declarations.
The same file then compiled the degree-two contraction formula
`d(e_i * e_j) = a_i * e_j - a_j * e_i`, using
`CliffordAlgebra.contractLeft_ι_mul` and `contractLeft_ι`. This checks the first
nontrivial alternating differential, including repeated indices, over arbitrary rings.
A further search found no tensor-comparison API for the actual
`completedConstantExtension` or `adicLisseConstantModules`; the remaining comparison
must construct this finite-free transport as well as the ordered tensor-dual coordinates.

`lem-weil-pbc-completed-koszul-product-comparison`, declaration
`AlgebraicGeometry.Scheme.completed_fiber_roos_comparison_on_complex` in
`Sheaf.Paper.WeilCompletedKoszulProductComparison`, is fully proved. Source: Stacks
Tags 0A0E and 0941. Mathlib searches found `piComparison`, the additive mapping-cone
comparison and its shift comparison. The proof uses those APIs, proves the projection
conjugacy and zero-lift compatibility, and identifies the exact ordinary-limit unit.
It concludes the actual chain isomorphism before any localization. The module uses
the existing module-sheaf limit preservation and reflection theorem to prove preservation
of products by the actual backward coefficient restriction.

`lem-weil-pbc-completed-fiber-roos-representative-comparison`, declaration
`AlgebraicGeometry.Scheme.completed_fiber_roos_comparison` in
`Sheaf.Paper.WeilCompletedKoszulRepresentativeComparison`, is fully proved.
Source: Stacks Tag 0A0E, Tag 0941, and the localization universal property.
The exact products theorem and the existing tensorTower and Roos factorizations
supply a descended functor. Its actual unit is proved natural, descended using
Mathlib's localization API, and transported along the prescribed realization.
LeanSearch, Loogle/LeanFinder and source grep found `Localization.liftNatTrans`
and its component formula;
they are used directly. No new roof-independence assumption is left behind.

`lem-weil-pbc-completed-fiber-strict-limit-comparison`, declaration
`AlgebraicGeometry.Scheme.completed_fiber_strict_limit_comparison` in
`Sheaf.Paper.WeilCompletedKoszulLimitComparison`, is proved from the preceding explicit
comparison, exact products and strict Roos derivation. Source: Stacks Tag 0941 and
the right-derived uniqueness universal property. Its proof preserves both the
termwise-limit normalization and the specified representative normalization.

`lem-weil-pbc-completed-fiber-cech-comparison`, declaration
`AlgebraicGeometry.Scheme.completed_fiber_cech_comparison` in
`Sheaf.Paper.WeilCompletedCechComparison`, is proved by composing the strict-limit
comparison and the existing single-site Cech--Koszul comparison. Source: Stacks
Tag 0A0E and sites-cohomology.tex Tags 0A0A and 0941. Its unit equation is proved by
hom/inv cancellation, without adding completeness or reflection as a hypothesis.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
