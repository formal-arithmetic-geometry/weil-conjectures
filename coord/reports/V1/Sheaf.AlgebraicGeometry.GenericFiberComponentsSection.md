## What changed

Restored `Sheaf.AlgebraicGeometry.GenericFiberComponentsSection` from its rework archive
and replaced its sole theorem hole by a complete Lean combination of the geometric,
ordinary-module and derived comparisons. During work the shared checkout restored the
same source verbatim; the delivered theorem signature still matches that source exactly.
The actual component quotient, component functor, geometric morphisms, coefficient maps,
terminal evaluation and all five localization universes in the original statement remain.

Proved a ring-valued presentation theorem for arbitrary internal abelian ring sheaves.
The main proof constructs the three coefficient presentations using this theorem before
applying the remaining geometric coefficient comparison; noncommutative rings are allowed.

Moved the six canonical data declarations verbatim into `GenericComponentData` and publicly
reexported them from the item. This permits separate comparison statements without an
import cycle. No construction has been replaced by an arbitrary existence witness, and
no target definition has changed. The extraction and downstream checks are recorded in
`coord/changes/generic-component-data-extraction.md`.

Proved the generic-fibre component section using flat going-down, actual fibre-product
points, the affine spectrum homeomorphism and Gleason projectivity. Proved terminal scalar
transport for any continuous site functor with a normalized terminal test isomorphism.
Proved transport of arbitrary unbounded left derived functors across additive equivalences
by their universal right Kan extensions. These give both clauses of the original derived
scalar predicate, with independent derived-category universes and without choosing
resolutions. Constructed the geometric morphisms required by the original conclusion.

Also filled the existing, unclaimed `spectralSpace_connectedComponents_profinite` using the
compactness and Hausdorff instances already supplied by its existing proof import and
Mathlib's total-disconnectedness instance. Its signature, imports and consumers are unchanged.
No source-library module under `WeilConjectures` was changed or removed.

## Proved and sorry left

Closed the original body hole in
`AlgebraicGeometry.Scheme.ProEt.generic_fiber_components_section` (one of one in the item).
This is a decomposition into two separate source arguments, not a completed proof of all
its dependencies. The item itself now contains zero `sorry`.

Also closed the existing hole in `spectralSpace_connectedComponents_profinite`.

The new proved public results, with no body holes, are:

- `AlgebraicGeometry.Scheme.ProEt.generic_fiber_component_section`;
- `CategoryTheory.module_terminal_scalar_comparison`;
- `CategoryTheory.internal_ring_sheaf_presentation`;
- `CategoryTheory.LeftDerivedEquivalenceSquare.comparison`;
- `AlgebraicGeometry.Scheme.ProEt.generic_component_ordinary_scalar_transport`;
- `AlgebraicGeometry.Scheme.ProEt.generic_component_derived_scalar_transport`.

Every hole added by this packet is listed here:

- `AlgebraicGeometry.Scheme.ProEt.generic_component_site_comparison`, node
  `lem-zl-generic-component-site-comparison`: affine ind-etale geometric-field site
  equivalence and the two ordinary set-sheaf comparison squares. It does not assert a
  section, coefficient-ring or module comparison, or any derived consequence.
- `AlgebraicGeometry.Scheme.ProEt.generic_component_coefficient_comparison`, node
  `lem-zl-generic-component-coefficient-comparison`: ordinary coefficient-ring and additive
  module transport for any given ring-valued presentations, including the constant-ring module comparison. It assumes the set
  equivalence and contains no derived-category or localization assumptions or conclusions.

Thus this packet closes two existing theorem body holes and adds two separate ordinary
comparison holes. It has no hole in a definition, instance, private helper or partial proof.
The existing `affine_component_site_projection` remains an existing dependency; its hole
was not added or moved by this delivery.

All ten delivered Lean files compiled through `lcompile.py`, without warnings. Both
unchanged downstream consumers, `CondensedDualizableLocalPerfectModels` and
`TAdmissibleDualizableTruncations`, also compiled against the packet. Their temporary
unchanged verification copies are excluded from the delivery. Axiom probes for the terminal scalar comparison,
left-derived equivalence square, ring presentation and both scalar-transport results
show only `propext`, `Classical.choice` and `Quot.sound`. Recompiling the unchanged
`AffineComponentSiteProjection` against the filled spectral theorem also makes the section
and `componentProfinite` probes show only these three axioms. This unchanged reference
source was used for verification only. The two newly stated comparison lemmas retain
`sorryAx`.

## No longer needed

The main proof no longer uses the approved tools
`lem-weil-pbc-equivalence-injective-resolutions` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Their two top-level `tool_uses` entries
are removed, preserving all remaining approvals in order. Exact equivalences and the
localization universal property supply the needed derived square directly. In particular,
this argument does not require an unbounded tensor-pullback theorem or K-flat resolutions.

Removed direct proof imports from the item:
`Sheaf.AlgebraicGeometry.ProEtalePointPullback`, `Sheaf.Paper.CondensedPointBasis`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.RingTheory.IndEtaleStability`, `Sheaf.RingTheory.IndEtaleUniverseTransport`,
`Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`,
`WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`,
`WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites`, and
`WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`.
The geometric-field evaluation import is retained. Canonical-data public imports have
moved into the publicly reexported data module where appropriate. The remaining site
comparison still mathematically needs the ind-etale classification, basis and component
projection, as its node records; removal of a direct import is not a claim to withdraw
those results. The spectral-component module is retained and proved here.

No module is withdrawn. No upstream declaration is removed, and no unit-level statement
or proof step is bypassed. The geometric diagram and coefficient/module consequences
of the original unit remain the route of the main proof.

## Where the brief, the DAG or earlier work was wrong

The old proof was a plan rather than a Lean proof. In particular it did not supply the
ordinary ring-valued lifts, their normalized terminal evaluation, or the constant-ring
module transport needed by the actual theorem's much larger conclusion. The two new
comparison statements isolate these ordinary geometric arguments; neither merely renames
or repackages the entire item. The topological and derived arguments joining them are
now real Lean proofs.

The existing exact-equivalence derived-square theorem takes simultaneous left- and
right-derived data. Here only left-derived data are supplied, so a proved left-only
universal-Kan-extension comparison was added rather than assuming unnecessary right
adjoints or resolution data.

The generic-fibre section needs flatness, not the whole ind-etale classification or an
algebraic closure assumption; its new theorem states that shorter route. Empty affine
sources are covered by the proof. Empty sites and zero coefficient rings cause no
exception in the comparison statements. The terminal scalar lemma in fact works for any
specified pair of isomorphic test objects and does not need an extra terminal hypothesis.

The shared source was initially quarantined, not withdrawn. Its archive and Lean attachment
are preserved. There were no forced adaptations of modules held by another group.

## New nodes

`def-zl-generic-component-data`: attaches the six unchanged canonical definitions to their
new data module. They are reexported by the original module; no semantic definition change.

`lem-zl-generic-fiber-component-section`: proved continuous section, by the generalizing-map
and actual pullback-point argument followed by projectivity of the extremally disconnected
component quotient.

`lem-zl-generic-component-site-comparison`: the separate source site comparison of HRS (4.4),
including the geometric-field equivalence and structural-point square; one retained hole.

`lem-zl-generic-component-coefficient-comparison`: the separate ordinary ring and module
comparison following HRS (4.4); one retained hole, with the full natural-language proof
and the exact normalized fields of the original theorem.

`lem-zl-internal-ring-sheaf-presentation`: proved sectionwise ring reconstruction and
recovery of the internal ring by monoidal sheafification, without commutativity.

`lem-zl-module-terminal-scalar-comparison`: proved natural semilinear evaluation comparison,
linear after the normalized scalar map, and uniqueness of the composite left adjoint.

`lem-zl-left-derived-equivalence-square`: proved transport of universal right Kan extensions
across exact equivalences, requiring only the supplied left-derived counits.

`lem-zl-generic-component-derived-scalar-transport`: proved passage from ordinary discrete
and constant-ring scalar squares to the original unbounded derived scalar predicate.

Change record: `coord/changes/generic-component-data-extraction.md`.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
