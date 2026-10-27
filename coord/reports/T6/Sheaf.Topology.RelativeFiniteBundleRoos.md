## What changed

The three original statements in `Sheaf.Topology.RelativeFiniteBundleRoos` keep their
signatures and public imports. Their proofs now combine two geometric lemmas with existing
source-library and Mathlib APIs:

- `relativeContinuousRing_exact_products` lifts each component on a Stonean test, assembles
  the lifts by the sectionwise limit equivalence, checks every projection using `limMap_π`,
  and applies `hasExactLimitsOfShape_of_preservesEpi`.
- `relativeContinuousRing_termwise_derived_product` installs the universe-compatible
  Grothendieck and exact-product instances, then applies the already proved product
  preservation of `DerivedCategory.Q` to the actual termwise cone.
- `relativeFiniteBundle_roos` uses the general tower kernel calculation to construct the
  canonical vanishing composite and kernel fork. The finite-bundle epimorphism supplies
  short exactness. Product preservation transports along `singleFunctorsPostcompQIso`,
  preserving the actual projections; `singleδ` and `singleTriangle_distinguished` give
  exactly the stated triangle and arrows.

The two new modules are `Sheaf.Topology.RelativeModuleStoneanEpi` and
`Sheaf.Topology.RelativeFiniteBundleRoosEpi`. The former is precisely the local lifting
and detection step; the latter is only epimorphy of the Roos differential. Neither states
the original conjunction under another name. The main proofs contain no local holes,
and the two remaining theorems have full source/proof docstrings and matching DAG nodes.
No definition, target, source-library declaration, consumer, or existing signature changes.

## Proved and sorry left

Original holes closed by complete proofs from named statements:

- `Profinite.relativeContinuousRing_exact_products`.
- `Profinite.relativeContinuousRing_termwise_derived_product`.
- `Profinite.relativeFiniteBundle_roos`.

Two new holes, each exactly `:= by sorry`:

- `Profinite.relativeContinuousRing_epi_iff_stonean`, node
  `lem-sfb-relative-module-stonean-epi`, in `RelativeModuleStoneanEpi`.
- `Profinite.relativeFiniteBundle_roos_epi`, node
  `lem-sfb-relative-finite-bundle-roos-epi`, in `RelativeFiniteBundleRoosEpi`.

This is a decomposition: three original holes closed, two strictly smaller holes added,
zero direct holes in the item, two direct holes in the packet. The original declarations
still depend on the new holes; this does not claim an axiom-free proof of the full result.
The sectionwise product argument includes the empty index set. The tower kernel requires
no bundle hypothesis; that hypothesis is used exactly for epimorphy. The solution-cover
argument includes empty base/test spaces, zero fibres and arbitrary transitions. The
Stonean criterion includes zero rings and unrestricted scalar actions. The naturality
in a section presentation is essential: it recovers actual continuous bundle transitions
by evaluating the represented transformation on the source total space.

Validation: both new lemma modules compiled (12.0 and 13.8 seconds). The complete
main module compiled cleanly in 11.3 seconds against those modules, with zero local
holes. All original theorem signatures and public imports were compared verbatim.
The overlay DAG closure has 282 nodes, no missing dependencies, and no cycles. All
Lean lines are at most 100 characters. The prescribed delivery tool performs the
remaining server/preflight/axiom checks before pushing.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`: work directly in the
  sectionwise encoding already fixed by the statements.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Mathlib.CategoryTheory.Sites.EpiMono`.
- `Sheaf.Topology.StoneanProjective`.
- `Sheaf.Topology.StoneanCover`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`: supplied by
  the proved source `TowerLimit` interface used here.
- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`: the source `TowerLimit` interface
  already proves product preservation through its own complete K-injective argument.
- `Mathlib.Topology.Compactness.Compact`.

The geometric inputs are now dependencies of the new geometric nodes, rather than
unused imports of the main module. No global withdrawal is requested: all existing
source-library declarations remain, and other parents may still need these modules.
The main node no longer directly uses `def-sfb-continuous-map-condensed-ring`,
`lem-weil-pbc-sheaf-tensor-closed`,
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`,
`det-pe-stonean-projective`, `det-pe-stonean-cover`,
`lem-weil-pbc-tychonoff-product-quasi-compact`,
`lem-weil-pbc-closed-in-quasi-compact`, or
`lem-sfb-compact-closed-finite-intersection` in its proof; the ones needed for the two
remaining steps are explicitly retained in those child nodes.
`lem-pc-ringed-space-product-kinjective` is replaced by the already proved source
product-preservation API. It is not needed as a separate Sheaf-module dependency.
The stale direct tool approvals for tensor sheafification, exact forgetting, Stonean
projectivity/cover, and the separate K-injective product lemma are pruned from the main
node. The two new geometric nodes use the corresponding previously approved generic
inputs for their actual local lifting steps. The unit statement and its realized steps
remain untouched.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The DAG's resolution/product and
kernel arguments already have complete general implementations in
`WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit`; the original module did
not import them. Mathlib `SingleTriangle` also already supplies the exact degree-zero
triangle with the original arrows. Reusing these avoids recreating their theory.

The source Lemma 1.2.7 motivates the finite-bundle argument but does not state the full
arbitrary-topological-ring relative version. The two new nodes explicitly identify
the relative argument and its Stacks inputs, rather than attributing that version to
the paper. Read the paper's Lemma 1.2.7 and Stacks `lemma-abelian-abelian`,
`lemma-abelian`, `lemma-limits-colimits`, `theorem-tychonov`,
`lemma-closed-in-quasi-compact`, `lemma-intersection-closed-in-quasi-compact` and
`proposition-projective-in-category-hausdorff-qc`. Searches found the fixed-discrete-ring
CondensedMod Stonean criterion, which does not cover this ring sheaf on the slice.

## New nodes

`lem-sfb-relative-module-stonean-epi` isolates original steps 1--2: exact forgetting,
local lifting, the finite disjoint union of a covering, a Stonean section, and detection
using Stonean covers. Its single public theorem is in `RelativeModuleStoneanEpi`.

`lem-sfb-relative-finite-bundle-roos-epi` isolates original steps 5--7 up to epimorphy:
representable bundle sections give continuous transitions; a closed profinite solution
space is surjective by finite backward recursion and compactness; its coordinate
sections prove local surjectivity. It omits the original kernel, exact products,
derived product and distinguished triangle. Its single public theorem is in
`RelativeFiniteBundleRoosEpi`.

Both inherit the item's unit/chapter and nearest blueprint ancestor. Whole-blueprint
searches for finite bundles, Roos and Stonean found no existing statement of either
relative lemma. Each new node records the actual logged LeanSearch, Loogle or
LeanFinder, and Mathlib grep searches. No change record is required because no existing
statement or definition changes.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
