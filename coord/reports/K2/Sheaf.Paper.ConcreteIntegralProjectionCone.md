## What changed

Proved `WeilConjectures.ConcreteIntegralProjection.concreteIntegralProjectionCone`
with its original hypotheses and conclusion. The proof follows the five concrete
steps, using the existing lower domain helpers rather than the projection-formula
theorem. Constructibility gives the uniform residue-Tor bounds. The canonical
coefficient-change square and naturality identify the actual reduced arrow under
its specified endpoint comparisons. Counit-normalized exact scalar extension and
TR3 give the finite cone triangles with the required first two components.

For the chain-map model, Mathlib's `DerivedCategory.right_fac` followed by an
actual flat-term K-flat resolution replaces the planned map-factorization lemma.
The existing coefficient-independent cone-closure theorem makes this cone K-flat.
The universal reduction counit and representative normalization give both cone
comparisons. A proved generic degreewise signed-cone naturality calculation and
uniqueness on pure tensors identify the strict and derived quotient transitions.
The cone-transition construction retains the original two-summand cone map of the
unrestricted quotient transitions; it is not replaced by transport through the
cone comparisons.

The finite-arrow and comparison endpoints are written explicitly, with the same
maps and definitionally identical types. Cone comparisons and transitions are
irreducible; their equations are explicitly unfolded in proofs. The coefficient-data definition is unfolded through a private `import all`;
the two ambiguous legacy instances exposed by that import are excluded just as
in the defining module. The shared
unrestricted scalar-extension witness is unchanged, avoiding the universe issue
in the previous delivery. Definition edits are recorded in
`coord/changes/K2-finiteArrow-explicit-endpoints.md`,
`coord/changes/K2-coneComparison-explicit-endpoints.md`,
`coord/changes/K2-coneTransition-explicit-endpoints.md`, and
`coord/changes/K2-targetUnit-explicit-endpoints.md`.

## Proved and sorry left

Closed the original hole:
`WeilConjectures.ConcreteIntegralProjection.concreteIntegralProjectionCone`.
There were one original hole and no definition holes. No new `sorry` declaration
is introduced; the delivery has zero remaining holes. All private helpers are
proved. The imported, already stated
`WeilConjectures.PurCompactSupport.compactSupportProjectionCoefficientChange`
is used for the ordinary coefficient square; it is not a new split in this
delivery. Other unfinished dependencies remain separate existing items.

## No longer needed

`lem-pur-kflat-map-factorization` and
`Sheaf.Paper.KFlatMapFactorization` are unnecessary: right fractions and a
resolution of the roof's source give the representing chain map. The generic
`lem-sfb-kflat-homotopy-triangulated` and
`Sheaf.Algebra.Homology.KFlatHomotopyTriangulated` are unnecessary: the existing
proved coefficient-independent cone-closure lemma suffices.

The absent wrapper module `Sheaf.Paper.OrdinaryProjectionInnerConstructible`
and node `lem-sf-ordinary-projection-inner-constructible` are not needed by this
proof. Their actual constituent pullback/tensor domain proofs already exist and
are applied directly through a private `import all` of
`SfProEtaleProjectionFormula`; the item node lists the underlying mathematical
dependencies. Removed the unused private imports of
`Mathlib.Algebra.Homology.DerivedCategory.Basic`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Sheaf.Paper.IntegralCompactSupportPrescribedReductions`,
`Sheaf.Paper.BasicOperationsCoefficientReduction`, and
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`. The needed compact-support
interfaces are the qcqs realization/finite comparison and the canonical
coefficient-change square; ordinary derived change of rings is reached through
the generic counit-normalized interface and existing proved cone-closure lemma.
No module or DAG node is deleted, and no unfinished parent or unit
route is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous D6 proof delivery was rolled back after its auxiliary shared
reduction-witness change caused universe failures in downstream importers.
This delivery preserves that witness and all other shared modules. The existing
item node still mentioned the rolled-back ordinary-inner wrapper; its step 2 is
updated to the existing constituent domain proofs. The coefficient-change square
has since been restored as an independent existing declaration, so no new split
is necessary.

Finite-type schemes here need not have separated structure morphisms. The domain
proofs used have precisely that generality. No invertibility of the projection
map, faithfulness of reduction, or lifting of unrelated finite-level arrows is
assumed. The generic cone equations also apply to zero complexes and zero maps;
the geometric argument applies to empty schemes and identity morphisms and the
first quotient level.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
