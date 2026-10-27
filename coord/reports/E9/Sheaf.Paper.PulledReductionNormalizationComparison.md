## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.PulledNormalization.pulled_reduction_normalization_comparison`
in `Sheaf.Paper.PulledReductionNormalizationComparison`.
The construction uses the published scalar presentations, ordinary tensor-generator
formulas, normalized derived adjunctions, exact-square/mate compatibility, and comparison
on flat-term K-flat resolutions. Private helpers establish the finite square, triple,
unit, and all required representative equations. The theorem signature and 16 of the original 18
public data declarations are unchanged.
Repaired `thetaN` and `quotientAssociator` by transporting their whole scalar isomorphisms
along coefficient-map equalities. The private proved theorems `thetaN_legacy_eq` and
`quotientAssociator_legacy_eq` identify them with their complete original definitions;
these are representation repairs with exactly the same mathematical values.

Added proof imports for the existing scalar adjunction/cochain/mate APIs, flat scalar
restriction, completed coefficient flatness, and the original-site resolution comparison.
Updated the existing node's proof, proof dependencies and proof origin to this route,
including the used `OrderedExchangeCoefficientComparison` normalization node.
No target signature, statement, other Lean module, or source-library declaration is changed.
Change records: `coord/changes/pulled-normalization-thetan-transport.md` and
`coord/changes/pulled-normalization-quotientassociator-transport.md`. The source-only
`downstream.py --uses` check lists no downstream modules and this module as the sole user
of each repaired declaration. Their use in this node's `Comparison` requires the normal
independent definition review; the legacy equality proofs certify that its meaning is preserved. All
scratch diagnostics live outside `lean/` and are not delivery modules.

## Proved and sorry left

The proposed proof closes the one original hole:
`AlgebraicGeometry.Scheme.PulledNormalization.pulled_reduction_normalization_comparison`
(node `lem-weil-pbc-pulled-reduction-normalization-comparison`).
Actual holes in the delivery module: zero. Holes added: zero. Statements split off: zero.
A complete proof compiled in 59.0 seconds; unused-helper cleanup compiled in 54.8 seconds.
The complete proof with explicitly pinned derived categories and objects compiled
without warnings in 57.4 seconds. The final version additionally uses the proved
`thetaH_hom_app` component API; its real prefix compiled in 40.5 seconds.
The delivery tool runs its final compile and preflight.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: use the existing
  original-site flat-term resolution wrapper instead.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: use the published scalar
  counits and normalization interface.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`: the actual finite pullback is
  exact; its existing localization factorization suffices.
- `Sheaf.Algebra.Homology.FlatCoefficientReductionAdjunct`: cancel fully faithful
  restriction in the already normalized ordinary coefficient comparison instead.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`: derive the representative equation
  directly from normalized adjunction transposes and the exact restriction square.
- `Sheaf.Paper.RingedTopoiTensorSections`: use the existing tensor-section API of the
  adic datum, with explicit adjunction arguments for the needed extensionality.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`: use the
  existing comparison-on-resolutions and natural-transformation extensionality APIs.

Removed direct proof dependencies:

- `def-weil-pbc-ringed-tensor-section-calculus`
- `lem-sfb-kflat-scalar-comparison-normalization`
- `lem-weil-pbc-flat-coefficient-reduction-adjunct`
- `lem-weil-pbc-ringed-topoi-derived-pullback`
- `lem-weil-pbc-site-derived-tensor-descent`
- `def-pc-tensor-complex-sheaves` (retained as a statement dependency)

Removed the obsolete approved tool-use entry
`lem-sfb-kflat-scalar-comparison-normalization`; other approvals are retained in order.
These are removals from this item's proof route, not module withdrawals. In particular,
the strict-tower interface remains publicly imported and still uses some of these
modules. No claim of a global module pruning is made, and no file is deleted.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. Both public data repairs are proved
equal to the previous constructions. The planned generic comparison and
tensor descent steps can be replaced by existing normalized-adjunction and resolution
APIs. The scalar-descent import is used only for its proved generic fully-faithful
restriction construction, not its integral-lisse theorem.

The retained earlier draft did not compile. A kernel timeout in identifying the ordinary
cochain balancing map was repaired by abstracting its isomorphism and generator formula,
so the normalization witness is not unfolded. A universe inference problem came from an
imported universe-raising `EssentiallySmall` instance; a private fixed-universe instance,
scoped after all original public definitions, resolves it. All public signatures and the 16
unchanged public data bodies were compared against the
shared source. The two changed bodies are reproduced verbatim in their change records,
with their proved legacy equalities. Several compile-server requests returned code
124 without diagnostics; these were retried and were not treated as proof failures.

Fully faithful cancellation uses the supplied preimage data with a proved map equation;
the section formula uses that equation instead of expanding the cancellation witness.
Exact-square symmetry and equality transport likewise avoid expanding derived comparison
witnesses. These are private implementation helpers, with no new public statements.

The generator extensionality calculations use private adjunction lemmas with explicit
module objects. The unit generator formula is named separately, so these proofs do not
expand the chosen scalar adjunction while evaluating sections.

The private ordinary scalar collapse uses the same whole-isomorphism equality transport;
its generator and cochain formulas are proved. Compact component constructions for the
ordinary pullback/scalar comparisons avoid identity-map compositions. The derived
normalizations have an irreducible private interface with representative and associativity
lemmas, so proofs do not unfold the chosen scalar functors.

The unused private whiskering-coherence and generic cochain-compositor helpers were removed. Derived
categories and all source and target objects
are pinned explicitly in the compositor application; this avoids reverse instance
inference and repeated comparison of completed coefficient constructions. The original
public theorem docstring is retained; the updated DAG records the actual proof route.

Quotient maps are locally irreducible in the final derived proof section. Their
compatibility and component calculations use the already proved APIs; elaboration
therefore does not compare the direct and successive quotient maps by evaluating
completed-coefficient limit projections.

The private `thetaH_hom_app` lemma states the component formula for the unchanged
public derived mate composite. The representative proof uses this theorem with
`proEtaleReductionPullbackInv` locally irreducible, rather than unfolding the mate
while working with concrete cochain objects. No resource limit is changed.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
