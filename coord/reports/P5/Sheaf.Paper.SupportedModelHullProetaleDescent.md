## What changed

Replaced the single hole in
`AlgebraicGeometry.ProEtale.supportedModelHull_proetale_descent` by a complete Lean
assembly of three strictly separate obligations and the existing
`proetale_supported_model_coinduction` declaration. The theorem's signature,
universes, coefficient alternatives and public imports are unchanged.

The proved private helper `directImage_preimage_class` builds the admissible class
`P.inverseImage (Rb_*)`. Triangulatedness and repleteness follow from the actual
derived functor. It maps retract equations explicitly, transfers limiting product
cones using right-adjoint limit preservation, applies the bounded strict-colimit
obligation for that clause, and accepts the supported-generator clause explicitly.
The main proof supplies that clause from the existing generator coinduction theorem,
restricts each given local hull object to every qcqs refinement, applies the
intersection property to this admissible class, and invokes Cech recovery for P.
Finally it quantifies over all admissible P, exactly as the hull definition requires.
The original weak-contractibility hypothesis remains in the signature; the assembly
retains an explicit reference to it; geometric recovery needs only the affine cover.

Three new modules each state one independent part of the original nine-step plan:
`Sheaf.Paper.SupportedModelHullPullback` (steps 2--3),
`Sheaf.Paper.SupportedModelPushforwardStrictColimit` (steps 5--6, only the colimit
closure clause), and `Sheaf.Paper.ProetaleCechProductClassRecovery` (steps 1, 7--9).
The assigned node now records this exact reduction. Its previous low-level tool
approvals are retained only when still directly used; the corresponding old
arguments and dependencies remain in the three new nodes rather than disappearing.
No adopted source-library module, existing definition, existing statement or target
has been changed, and no arbitrary data is chosen from an unproved theorem.

Validation: all three new statement modules compiled separately through lcompile.py;
the main module then compiled in 13.2 seconds after its product-cone and shift-instance
assembly were repaired. The first delivery check compiled all four files, then flagged the unused original
weak-contractibility hypothesis when cleared. An explicit reference restores the
previous warning-free proof. The final delivery tool performs the axiom probes.
The statement modules compile in 9.7, 41.5 and 39.4 seconds respectively, below the
single-file limit. No local Lean or Lake invocation was made.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.ProEtale.supportedModelHull_proetale_descent`
(node `lem-sfb-supported-hull-proetale-descent`). The private helper
`directImage_preimage_class` is completely proved and has no hole.

Added exactly three public theorem holes, each the whole proof `:= by sorry`:

- `AlgebraicGeometry.ProEtale.supportedModelHull_pullback_single`, in
  `Sheaf.Paper.SupportedModelHullPullback`, node
  `lem-sfb-supported-model-hull-pullback`.
- `AlgebraicGeometry.ProEtale.supportedModelClass_pushforward_strictColimit`, in
  `Sheaf.Paper.SupportedModelPushforwardStrictColimit`, node
  `lem-sfb-supported-pushforward-strict-colimit`.
- `AlgebraicGeometry.ProEtale.proetale_cech_product_class_recovery`, in
  `Sheaf.Paper.ProetaleCechProductClassRecovery`, node
  `lem-sfb-proetale-cech-product-class-recovery`.

This is a decomposition (one upper hole closed, three lower holes added), not a
claim of net sorry reduction or an unconditional axiom-free proof of hull descent.
The already-stated coinduction theorem remains a dependency, with its existing
proof status unchanged. The assigned module itself has zero holes.

## No longer needed

No mathematical branch of the original plan is pruned: its localization,
base-change, bounded-resolution and Cech-totalization work is retained in the
appropriate new nodes. No module is withdrawn; global modules pruned: none.
The following direct proof imports are removed from the assigned module because
the new interfaces hide their low-level work (they are not claimed globally unused):

- `Sheaf.Paper.FiniteAffineProEtaleRefinement`.
- `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.RingedSheafSliceAdjunction`.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.
- `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates`.
- `Sheaf.Paper.CondensedConstantConstructibility`.
- `Mathlib.Topology.Compactness.Compact`.
- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `WeilConjectures.CategoryTheory.CartanEilenbergAllLowerBounds`.
- `WeilConjectures.CategoryTheory.CartanEilenbergTotalResolution`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage`.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`.
- `Sheaf.CategoryTheory.FiniteProductInjectiveResolutions`.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.

The old parent proof dependencies not directly retained are now dependencies of
one or more of the three new nodes, as shown in their `proof_deps`. Obsolete
parent-level `tool_uses` entries were removed accordingly; no approval was added
or reordered. In particular finite affine refinement, finite-family geometry,
weakly etale localization, ringed slice adjunction, module transport, products in
the derived category, base-change mates, small diagram resolutions, bounded
continuity, finite-product injective resolutions and short-exact triangles remain
required below the new interfaces. The new class-recovery statement does not need
weak contractibility, retract closure or filtered-colimit closure; it is the pure
Cech reconstruction part, with coinduced intersections as inputs.

The exact parent-level tool approvals removed (all retained as dependencies below
the new interfaces) are:

- `lem-sfb-finite-affine-cover-refinement-general`.
- `lem-weil-pbc-proetale-qcqs-finite-family-geometry`.
- `lem-weil-proetale-weakly-etale-localization`.
- `lem-weil-pbc-ringed-sheaf-slice-adjunction`.
- `lem-sfb-internal-module-operations-transport`.
- `def-sfb-module-upper-lower-adjunction`.
- `lem-weil-pbc-left-adjoint-preserves-colimits`.
- `det-pe-products-derived`.
- `lem-sf-exact-functor-derived-triangulated`.
- `lem-sf-ring-sheaf-base-change-mates`.
- `sk-def-sfb-constructible`.
- `lem-weil-pbc-closed-in-quasi-compact`.
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`.
- `lem-weil-pbc-small-module-diagrams-grothendieck`.
- `lem-sp-grothendieck-enough-injectives`.
- `lem-weil-pbc-ce-resolution-all-lower-bounds`.
- `lem-sp-cartan-eilenberg-total-resolution`.
- `det-pe-bounded-continuity-direct-image`.
- `lem-weil-pbc-ring-sheaves-grothendieck`.
- `lem-sfb-cech-pushforward-augmented-model`.
- `lem-weil-pbc-finite-product-injective-resolutions`.
- `lem-weil-pbc-complex-ses-triangle`.
- `lem-weil-pbc-bounded-below-injectives-kinjective`.

## Where the brief, the DAG or earlier work was wrong

The old declaration docstring calls generator coinduction and the augmented Cech
model “not yet stated”; both now have Lean declarations, and their actual signatures
were read. The existing docstring was preserved rather than silently rewritten.
The proof uses the actual coinduction declaration and the new Cech assembly node
still depends on the actual coherent-model declaration. The blueprint unit record
is an older smooth-purity text; its `realized` statement and steps are not this
node. The current latest blueprint compactification route and the parent node's
exact descent obligation were kept.

The parent proof's final sentence refers to an algebraic-closure coefficient, but
its current Lean signature and node statement contain only the five coefficient
cases. The new proofs do not add a sixth case. HRS supplies ambient coefficients
and bounded continuity only: no claim that HRS Corollary 4.7 proves this generated
hull descent is made. The exact full-hull reference remains WANTED.

Searches actually run: semantic LeanFinder, LeanSearch, Loogle and Mathlib grep
through msearch.py, plus project/DAG rg. The logged results supplied general
triangulated subcategories, module presentations, colimits and products, not these
specialized statements. Whole-blueprint searches for “supported hull”, “strict
filtered” and “Cech product” each returned zero nodes. Existing supported model,
coinduction, continuity, finite-affine refinement, exact localization, transport,
base-change and Cech-model declarations were read before splitting.

Edge cases checked against the definitions and the new interfaces: on empty V,
the module category is zero and Cech recovery uses triangulated zero and
repleteness; empty I is possible only there. Zero rings, zero modules and all
integer lower bounds remain allowed. The identity cover is included, and
refinement arrows need neither be covering nor affine. All original U_i are affine
and thus qcqs; arbitrary Cech intersections are required to be only qcqs. Every
composite direct-image arrow is genuinely the composition r followed by b_i.
Local expressions can have unrelated construction lengths; the reduction takes no
uniform bound on them. The strict-colimit lemma requires only the common termwise
bound already specified by the hull definition. The Cech truncations are quotient
complexes with outgoing differential discarded, and their projections split only
as graded maps, which is what the product-fibre argument needs.

## New nodes

`lem-sfb-supported-model-hull-pullback`: only restriction stability, with no cover
or coefficient-admissibility hypotheses. This is original steps 2--3, distinct
from descent; all geometric base-change and exact-localization dependencies remain
recorded. Its Lean conclusion is restricted to degree zero, the only case the
assembly uses.

`lem-sfb-supported-pushforward-strict-colimit`: only the strict bounded filtered
colimit clause for the inverse image of an admissible class under derived direct
image. It asserts neither preservation of generators nor preservation of the
whole hull. Its source is original steps 5--6, Stacks Tag 013K for common-bound
resolutions and HRS Lemma 5.3(1) for bounded continuity.

`lem-sfb-proetale-cech-product-class-recovery`: recovery for an arbitrary replete
triangulated class closed under products, assuming membership of all the needed
coinduced refinements. It has no hull, no generators and no local-hull membership
hypothesis. The main proof must establish its stronger intersection-term inputs
using the other two pieces and existing coinduction. This is original steps 1 and
7--9, preserving the coherent Cech model, finite intersections, finite total
truncations and product-fibre argument. Each new node has a separate Lean module,
source, complete proof in words, statement attachment and logged searches.

No existing public interface was changed, so no definition/statement change record
or forced consumer adaptation is necessary.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
