## What changed

The original theorem in `Sheaf.Paper.FiniteFreeCompactSupportComposition` is assembled from two independent compatibility statements. The original hypothesis list and conclusion are unchanged. The Lean assembly proves coefficient-map naturality on both sites, bounded-below etale origins, bounded-below scalar origins, etale coefficient-map invertibility, and transfer of invertibility to proetale constructible finite-Tor inputs. Finite freeness is supplied by the existing same-level stage theorem; no quotient-ring construction is duplicated.

The nine canonical definitions moved verbatim to `Sheaf.Paper.FiniteFreeCompactSupportData`, publicly re-exported by the item, to avoid an import cycle with the independent square modules. Their names, signatures and bodies are unchanged. The item privately imports the two new square modules and `Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension`. No adopted `WeilConjectures` file changes.

The mixed square only identifies the concrete scalar/site map. The geometric squares only prove composition/refinement equalities for retained bounded origins. Neither new theorem repeats the original conjunction or supplies existence, naturality or invertibility. Edge checks: identity scalar maps and identity refinements reduce to canonical naturality; empty schemes and zero objects give zero arrows; arbitrary origin automorphisms are handled by conjugation, not by assuming the witnesses canonical. The finite-free hypothesis allows rank zero (the zero coefficient ring), where these are equations in the zero derived category. No faithfulness of restriction of scalars is assumed.

## Proved and sorry left

One original hole is closed as a **decomposition**, not a complete axiom-free proof: `AlgebraicGeometry.FiniteFreeCompactSupport.finite_free_compactSupport_composition` (node `lem-pur-finite-free-compact-composition`). Its body contains no `sorry`.

Two holes are added, each exactly one public theorem with `:= by sorry` and a source/proof docstring:

- `AlgebraicGeometry.FiniteFreeCompactSupport.finiteFree_site_square`, node `lem-pur-finite-free-compact-site-square`, in `Sheaf.Paper.FiniteFreeCompactSupportSiteSquare`.
- `AlgebraicGeometry.FiniteFreeCompactSupport.finiteFree_geometric_squares`, node `lem-pur-finite-free-compact-geometric-squares`, in `Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares`.

The item has 0 holes left; the delivery has 2 new holes. The first full compile accepted the data and both new theorem modules; subsequent compiler-guided edits preserve that interface. All six private helpers in the item are proved, and all nine relocated definitions have real construction bodies. Net holes closed minus added for this packet: -1. The result still transitively uses existing unfinished theorem dependencies; this is not reported as an axiom-free proof of the target.

## No longer needed

The item no longer directly imports these original proof modules:

- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`.
- `Sheaf.Paper.OpenExtensionFiniteTor`.
- `Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage`.
- `Sheaf.Paper.ProperOpenCoefficientRefinement`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.SfDirectImageCTFNonproper`.
- `Sheaf.Paper.UnboundedProperOpenInterchange`.
- `Sheaf.SixFunctors.ComparisonOpenTensorCoherence`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`.

These imports were speculative support for a monolithic proof. The concrete assembly instead uses the proper finite-coefficient theorem, adjunction naturality, finite-Tor reflection, and the two independent squares. Public statement/definition imports are preserved through the data module.

At the item assembly level, the old direct proof edges for compatible towers, proper/open interchange, its normalization, compact-support site coherence, the scalar pullback cube, fixed comparison mates and open tensor coherence are replaced by the two square statements. They remain prerequisites of those statements where needed; none is globally withdrawn or claimed pruned. The finite compact-support domains package is not needed to obtain either bounded origin: the proof uses finite-Tor lower bounds directly and the existing proetale origin field. The finite-free-extension arithmetic edge is replaced by `lem-pur-stage-same-level-finite-free`, which matches the actual same-level Arrow. Constructible intermediate compact-support domains are not needed to formulate or assemble the geometric equations. No module is withdrawn.

Obsolete top-level tool approvals removed from the item's node (preserving the order of the remaining origin approval):

- `lem-coef-finite-free-extension`.
- `lem-coef-finite-direct-image`.
- `lem-sf-proper-open-coefficient-refinement`.
- `lem-trf-open-ctf`.
- `cor-sf-direct-image-ctf-nonproper`.
- `cor-sf-direct-image-ctf-proetale`.
- `lem-sf-comparison-open-tensor-coherence`.
- `lem-amb-etale-compact-comparisons`.
- `lem-amb-unbounded-compact-support-comparisons`.
- `lem-amb-unbounded-proper-open-interchange`.
- `lem-cbc-compactifiable-compatible-tower`.
- `lem-cbc-proper-open-interchange-coherence`.
- `lem-pur-compact-support-site-coherence`.
- `lem-sf-proper-open-comparison-site-normalization`.
- `lem-sfb-etale-proetale-scalar-pullback-cube`.
- `lem-sp-finite-compact-support-domains`.
- `lem-weil-pbc-comparison-direct-image-canonical-mate`.

These removals only describe the item's direct assembly; lower geometric and site nodes retain the relevant mathematical dependencies. No source-library declaration is removed or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

The latest blueprint numbers the change-of-coefficients compatibility as Step 4, with Step 3 identifying the ordinary compact-support adjunction; the original item still calls this Steps 1 and 3. The new nodes cite the current source.

The original DAG's general topos lemmas use abstract adjunction presentations. Their Lean signatures do not directly identify all the concrete chosen compact-support wrappers in this item's equation. The two remaining obligations record those exact normalized equations, with the existing abstract lemmas retained in their proof plans. The library already has an etale compact scalar coherence package, which shortens the etale part of the geometric obligation. The ambient bounded-origin and naturality clauses can be proved directly without the full constructible-domain package. The original theorem is not disputed and no target statement changes. The unit's finite-coefficient transport route is preserved.

## New nodes

`def-pur-finite-free-compact-support-data` owns the nine unchanged canonical constructions in the independent data module. This is a relocation, with no new hole. The consumer audit and old definitions are in `coord/changes/K9-finite-free-compact-support-data.md`.

`lem-pur-finite-free-compact-site-square` states only the mixed scalar/site equation for bounded etale inputs and finite-free scalar extension, with a proof plan identifying the concrete right and left mates and then pasting.

`lem-pur-finite-free-compact-geometric-squares` states only the two geometric equations for retained bounded origins, with the compatible-tower/refinement argument followed by normalized site transport and naturality. It does not assert any of the other conjuncts of the original theorem.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
