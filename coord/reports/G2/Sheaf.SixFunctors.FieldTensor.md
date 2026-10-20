## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.tensorClosureRational` in
`Sheaf.SixFunctors.FieldTensor`, preserving its complete signature and all public imports.
The coefficient hypothesis remains an isomorphism of monoid objects, including the ring
structure. No definition or consumer interface changes.

The shorter route uses clause (4) of `finiteCoefficientDescentTwoColimit` to compare the
constant-model predicate with the existing bounded-constructible predicate for finite
coefficient fields and the algebraic closure, then applies
`boundedConstructible_tensor_closure`. Three proved private helpers transport this through
the coefficient isomorphism using restriction of scalars, homology comparison, and the
derived tensor comparison. The `import all` of `IntegralConstantModelHeartClosure` reuses
its proved generic `constantModel_comap_iff` and `constructible_iso` helpers; the integral
weak-Serre theorem is not applied and no integral hypotheses are assumed.

Two further proved private helpers show that inverse image under an exact left adjoint
preserves the localizing property and assemble the two minimality arguments. Tensoring is exact and a left adjoint in both variables;
two applications of minimality prove closure of the localizing category. These are the
original node's two localizing minimality arguments. The node proof, proof dependencies,
proof origin, and obsolete tool approvals now record this route. No blueprint unit is
bypassed; the unit's tensor assertion is proved here.

Isomorphism invariance of bounded constructibility is proved directly from boundedness
and the homology functors; `ConstantModelTorAmplitude` is no longer imported.

The localizing helper is formulated for an arbitrary exact bifunctor with left adjoints
in both variables. A sixth proved private helper, `derivedTensor_eq_curriedTensor`, identifies
the public derived-tensor wrapper with the canonical bifunctor used by the shift API. Both generic helpers accept the wrapper equalities explicitly and eliminate them in the
abstract setting, avoiding repeated expensive instance conversion in the concrete module
category. The complete revised proof passed a profiled compile in 43.6 seconds and a
clean compile in 42.8 seconds; profiling options were removed. Local irreducibility attributes keep the derived
comparison constructions folded during elaboration.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.ProEtale.CondensedRing.tensorClosureRational`
(node `det-thm-sf-pf-field-tensor`). Actual remaining holes in the item: **0**.
Added holes: **0**. Split-off statements: **0**. All six new private helpers are proved: `localizing_inverseImage`,
`localizing_tensor_closed`, `derived_tensor_transport`,
`constantModel_derived_comap_iff`, `constantModel_tensor_transport`, and
`derivedTensor_eq_curriedTensor`.
This closes the item's proof from existing declarations; it does not claim that all
pre-existing proof dependencies in the target closure are already free of holes.

## No longer needed

The direct proof imports removed are:

- `Sheaf.Paper.ConstantModelTorAmplitude` (removed from the retained attempt)
- `Sheaf.Topology.ProfiniteCondensedRing`
- `Sheaf.Algebra.Homology.KFlat`
- `Mathlib.Algebra.Homology.Bifunctor`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.Paper.CoefficientHeartTriangulated`
- `Sheaf.SixFunctors.IntTensorProjection`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`
- `Sheaf.Paper.CoefficientHeart`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CoefficientHeartGeneration`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The following old direct node dependencies are unnecessary for the new argument:

- `det-def-sfb-constructible-tor-amplitude` (removed from the retained attempt)
- `def-pc-kflat-complex`
- `def-pc-tensor-complex-sheaves`
- `det-cor-coefficient-heart-ii-generation`
- `det-cor-coefficient-heart-ii-triangulated`
- `det-lem-int-tensor-projection`
- `det-sf-open-closed-sequence-ring-sheaf`
- `lem-sfb-locally-closed-extension-coherence`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `sk-lem-coefficient-heart`
- `sk-prop-sfb-cartesian-coefficients`

The existing coefficient comparison and bounded-constructible tensor theorem replace
the generator, base-change, projection-formula and five-stratum calculation. The derived
tensor API supplies exactness and adjoints directly, without reconstructing total tensor.
These are removals from this item's direct route, not assertions that no other target
needs the corresponding modules or their transitive infrastructure.

Removed obsolete top-level tool approvals, preserving the remaining approval's order:
`det-cor-coefficient-heart-ii-generation`, `det-cor-coefficient-heart-ii-triangulated`,
`sk-lem-coefficient-heart`, `det-sf-open-closed-sequence-ring-sheaf`,
`lem-weil-pbc-noetherian-open-subscheme-noetherian`, `det-lem-int-tensor-projection`,
`lem-weil-pbc-finite-type-over-noetherian`,
`lemma-nagata-scheme-theoretic-closure-minimal`, and
`lem-sfb-locally-closed-extension-coherence`.
No new top-level tool approval is added; the new route's existing-declaration uses are
listed in the proof steps and `proof_deps` for independent review.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface repair. The static interface scanner reports the new
`open` commands and local irreducibility attributes as a command-context change. The change
record `coord/changes/G2-field-tensor-proof-context.md` explains their scope. Public imports
and the theorem's full signature remain identical; no consumer needs adaptation. The original route was longer than necessary:
its first six steps duplicated the existing bounded-constructible tensor closure after
coefficient comparison. Its final two minimality arguments remain the proof of clause (2).
The monoid-object isomorphism repair in the existing statement is respected explicitly.

The argument applies to the empty scheme, zero objects, empty coproducts and both
canonical coefficient cases. Coefficient transport uses the inverse monoid-object
isomorphism, so it transports the specified ring structures. The localizing proof uses
only closure under existing coproducts, exactly as in `IsLocalizingSubcategory`, and
works for arbitrary generating classes without a smallness assumption.

The sandbox reference clock was reset externally during provider-error resumption:
previous observed start `1792426049.0841417`, later observed start `1792436021.6218174`.
No budget metadata was edited by this worker; the original dispatched session remains
this item. The reference-clock reset did not justify any split (none was added).

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
