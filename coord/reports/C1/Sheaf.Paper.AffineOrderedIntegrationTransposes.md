## What changed

In `Sheaf.Paper.AffineOrderedIntegrationTransposes`, proved
`AlgebraicGeometry.ProEtale.AffineOrderedIntegration.coordinate_coherence` from the
existing compact-support site compositor square, ordinary projection-composition
identity, and the generic ordinary/pro-etale compactification tensor-action laws.
The four private helpers apply these laws with respectTransparency enabled.
Added the public definitions ProTensorActionEquationForCategory and
OrdinaryTensorActionEquationForCategory, which write the same two literal
canonical equations before specializing the coefficient category. The existing
ProTensorActionEquation and OrdinaryTensorActionEquation keep their signatures
and become specializations of those definitions. This shares the derived
structures in kernel checks rather than repeatedly comparing concrete instance
terms. Local irreducibility handles the separate site-comparison elaboration.
The proof uses proof-only `import all` access to the private generic lemmas of
`Sheaf.Paper.CompactSupportSiteCoherence`, `Sheaf.Paper.FiniteProjectionActionLaws`,
and `Sheaf.AlgebraicGeometry.ShriekTensorComposition`.

Removed the already disputed, unrestricted auxiliary `coefficient_plus`.
The only caller, `integration`, now uses the existing fully proved
`coefficient_plus_on_base P Y aY d`, which was made public because it occurs in a
public definition. Only a proof argument changes, so the integration morphism
is definitionally unchanged by proof irrelevance. The target declarations and
all actual coefficient, trace, comparison and transpose constructions are unchanged.
Change records:
`coord/changes/C1-affine-coefficient-bound-domain.md`,
`coord/changes/C1-affine-pro-action-sharing.md`, and
`coord/changes/C1-affine-ordinary-action-sharing.md`.
The definition body edits are submitted for the usual target-meaning review;
their canonical maps and mathematical predicates are unchanged.

Updated the item's node attachment and proof account to record the proved
coherence specialization, the two definitional APIs and the supported-base
coefficient argument. No other
Lean module is adapted; there are no new modules or nodes.

Validation: the complete item compiled through lcompile.py in 59.6 seconds,
with no errors or additional warnings. Delivery runs the required server preflight.

## Proved and sorry left

Of the five original holes, one is proved, one disputed auxiliary assertion is
withdrawn, and three are left untouched. No holes are added or split off.
The withdrawal is not counted as a proof.

Proved:
`AlgebraicGeometry.ProEtale.AffineOrderedIntegration.coordinate_coherence`.
Its four clauses are supplied by existing proved generic laws. The generic
helpers added in this delivery are private and have complete proofs.

Withdrawn, not proved:
`AlgebraicGeometry.ProEtale.AffineOrderedIntegration.coefficient_plus`.
The previously proved `coefficient_plus_on_base` supplies the bound actually
needed by integration, under the structure map already present there.

Exactly these three public theorem holes remain in the item, all attached to
`lem-pur-affine-ordered-integration-transposes` and retaining their original
source and natural-language proof docstrings:

- `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_formula`.
- `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.pro_coordinate_projection_composition`.
- `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordered_integration_transposes`.

## No longer needed

The unrestricted `coefficient_plus` declaration and its use as the bound in
`integration` are no longer needed. No public import, module, or DAG node is
removed. The remaining proof dependencies are retained because the unfinished
main transpose argument still uses that route. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The published file already marks unrestricted `coefficient_plus` as
STATEMENT-DISPUTED: it lacks the invertibility condition needed on an arbitrary
base. The existing supported-base proof makes that unrestricted assertion
unnecessary. This delivery removes it rather than claiming to prove it.

The coherence result does not require re-proving a site-transport argument:
the private generic laws already state all four clauses at the required scalar
ring. The public finite-setting specializations use a different presentation
of the coefficient ring, so using the generic laws avoids unnecessary scalar
transport. Earlier attempts unfolded large site-comparison data during
elaboration; locally irreducible named data resolve that part. Profiling then
showed that the tensor-action proof elaborated quickly but its kernel check
repeatedly normalized the concrete scalar category structures. The generic
predicate definitions resolve that separate issue while retaining exactly the
same associators, projection maps, inverse-image comparison and tensor order.
They add no existence witness, arbitrary map or hypothesis.

For the remaining projection-composition hole, its arbitrary tensor factor H
is not assumed to have an ordinary antecedent, so bounded ordinary transport
alone does not supply the full statement. The ordinary counit hole still
requires identification of the ordered coefficient/source/comparison with the
normalized affine counit construction. Those identifications and the final
ordered-transpose induction are not asserted proved by this partial delivery.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
