## What changed

Implemented `AlgebraicGeometry.ProEtale.CondensedRing.supported_three_term_scalar_rigidity`
without changing its signature. Its private helpers prove exactness of every actual support
path and the two-short-exact-sequence argument in an arbitrary abelian category. The proof
uses the existing conditional image comparison twice and the existing normalized restriction
triangle interface. The final arrow is the original `rightDerivedPullback`, not a newly
chosen comparison.

Separated the independent single-model comparison (old steps 2--5) into
`Sheaf.Paper.SupportedFiniteModelScalarRigidity`. This is the remaining mathematical work:
finite discrete etale descent and integral reconstruction, followed by the already stated
conditional coefficient transfers. The main theorem really combines the middle comparison,
two image comparisons, exact support extension, two distinguished triangles, and the canonical
homology/cokernel isomorphism. The new statement concerns one finite local model; it does not
assert comparison for arbitrary images or homology. In particular it is not the original
three-term statement with its hypotheses repackaged. No source-library file was changed.

## Proved and sorry left

Closed 1 of the item's original 1 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.supported_three_term_scalar_rigidity`.

Added 1 hole:
`AlgebraicGeometry.ProEtale.CondensedRing.supported_finite_model_scalar_rigidity`, node
`lem-sfb-supported-finite-model-scalar-rigidity`. Its proof is exactly `by sorry` in its own
module, with the source and full argument in its docstring. The item's module has zero
remaining holes. This is a decomposition: one upper hole closed, one strictly smaller
single-model obligation added, net zero holes. The private kernel/image and exact-path
lemmas are fully proved. Existing dependencies may still contain their own holes.

The two formal helper proofs compiled independently. The combined module compiled with no
errors or warnings in 52.6 seconds; the new single-model module compiled in 3.2 seconds.
The triangle morphism is constructed directly from naturality and the existing shift
compatibility. This avoids elaborating the much larger triangle-existence projection.
Local irreducibility of the ordinary pullback and adjunction definitions prevents needless
unfolding; no global definition or attribute is changed. Final delivery checks are recorded
by the delivery tool.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
- `Sheaf.Paper.FiniteDiscreteScalarConstantModels`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`
- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.DerivedModuleUnderlyingComparison`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions`
- `Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`

The finite-discrete and coefficient-transfer dependencies below remain required by the
new single-model node, so they are moved below that node, not withdrawn or globally pruned:

- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-pe-finite-discrete-scalar-constant-models`
- `det-pe-finite-local-systems-twist`
- `sk-def-sfb-constructible`
- `det-pe-constructible-comparison-classical`
- `sk-thm-pe-classical-sheaves`
- `sk-prop-sf-comparison`
- `lem-weil-pbc-comparison-pullback`
- `lem-weil-pbc-derived-module-underlying-comparison`
- `lem-sfb-supported-integral-model-restriction-tower`
- `lem-sfb-supported-rational-model-rigidity-transfer`
- `lem-sfb-supported-norm-algcl-model-rigidity-transfer`

The following old direct proof dependencies are superseded in this module by exact support
instances, `closedSupport_lowerStarExact`, Mathlib's SES triangles, and the existing
`closed_restriction_derived_operations` interface:

- `lem-sfb-internal-module-operations-transport`
- `det-prop-sfb-module-pullback-exact-main`
- `lem-weil-pbc-exact-functor-complex-cohomology`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-injective-resolution-ses`
- `lem-sp-kinjective-comparison-principle`
- `lem-weil-pbc-horseshoe-morphism-lift-exact-source`
- `lem-sp-grothendieck-enough-injectives`
- `lem-weil-pbc-bounded-below-injectives-kinjective`
- `def-weil-pbc-proetale-site`

Some remain transitive dependencies of those existing interfaces. No existing declaration
or module is withdrawn; no global module pruning is claimed. Removed obsolete top-level
`tool_uses` entries only; did not add or reorder maintainer approvals. The two newly used
existing generic nodes are `det-lem-formal-closed-support-adjunction` and
`lem-sfb-closed-restriction-derived-operations`.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan is mathematically retained, with its
single-model stage separated. The long horseshoe construction in old step 8 is already
encapsulated by the normalized restriction-triangle interface; repeating it is unnecessary.
Exactness along closed branches follows directly from the closed support adjunction.
The integral tower dependency now returns a normalized strict-tower arrow isomorphism;
it does not directly return invertibility. Applying the torsion cohomology hypothesis to
that strict tower, with all evaluation/forgetting identifications, remains part of the new
single-model obligation. No arbitrary data are chosen from an unproved existence theorem
by this delivery: only propositions from the existing theorem interfaces are used.

Further exploration compiled the final integral-arrow transport in
`scratchpad/TowerTransport.lean`: assuming the strict etale tower restriction is invertible,
functoriality of derived inverse limit and
`Arrow.isIso_hom_iff_isIso_hom_of_isIso` give exactly the integral arrow in the source
interface. The scratch file is not a delivered library module. The remaining single-model
work includes the normalized evaluation/forgetting cohomology square, finite-discrete
support descent, and transport of the canonical restriction along coefficient isomorphisms;
these are not consequences of the arrow-isomorphism field alone. The new node records the
correct order of these steps.

## New nodes

`lem-sfb-supported-finite-model-scalar-rigidity` states old steps 2--5 for one supported
finite local model, uniformly in all paths and all six original coefficient cases. Its
proof is finite-discrete classical descent, torsion cohomology comparison, integral strict
tower reconstruction and the existing rational and norm-algebraic-closure transfers. Zero
rings, zero modules, empty schemes and identity paths impose no additional hypothesis.
It is separate from the conditional image theorem: that theorem takes the universal
single-model assertion as a premise, which the new node supplies. The main proof uses it
also on the middle term. Three Mathlib searches found no matching result. No change record
is needed because no existing statement, definition or public signature was changed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
