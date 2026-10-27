## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_square_scalar_comparison`
without changing its statement or either comparison construction in the assigned module.
The module pullback comparison gains `@[irreducible]` for categorical unification.
Seventeen proved private helpers give the coefficient equation, adjunction argument and
exact derived descent. Local transparency attributes prevent unnecessary unfolding.

The unclaimed operations module gains a definition boundary for its square comparison,
with a proved public equality to the former explicit construction. The unclaimed
base-change-mates module uses that equation in its monoidality proof. The unchanged
open/closed-sequence module compiles against the repair. No source-library file changes.

The coefficient equation is the existing proved square clause of
`profinite_point_pullback_abelian_coherence`, specialized to the pullback square with
its condition reversed. A generic composition lemma handles reassociation.
Generic symmetry equations and a component equation for the square comparison
avoid unfolding equality transports between concrete inverse-image functors.
The former square-comparison abbreviation caused kernel timeouts while converting its
component object from `condensedRingObj` to its defining point-pullback object.
The repaired definition chooses an isomorphism with a proved equality to the existing
compositor. This equality uniquely determines the object; no existence proof is postponed.
Its public equation is `AlgebraicGeometry.ProEtale.ringSheafSquareComparison_eq`.

Define the inverse module comparison as the adjunct of the required unit-square composite.
The open unit is invertible by full faithfulness. The target lies in the essential image of module extension by zero: extension
along the coefficient isomorphism identifies its underlying sheaf with ordinary pullback,
and existing abelian open base change identifies that pullback with an extension by zero.
Its open counit is therefore invertible. The adjunction's explicit inverse Hom formula
makes the comparison a composite of isomorphisms. This also fixes its normalization
without identifying a separately transported scalar action.

For the derived comparison, precomposition by the localization Q is fully faithful.
The two exact-functor factorization isomorphisms transport the termwise comparison to a
natural isomorphism between the two composites after Q. Its preimage is the required
comparison. The map-preimage equation gives the displayed normalization. Termwise
natural transformations, termwise compositors and exact derived factorizations commute
with shifts; essential surjectivity of Q detects the same property for the preimage.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_square_scalar_comparison`.
Added zero holes; split off zero statements.
The base-change-mates module had zero holes and still has zero holes.
No `sorry` remains in any delivered module.
All private helpers and the new public definition equation are proved.
The operations module had zero holes and still has zero holes.
Existing imported statements remain valid stage-3 inputs;
this report does not claim that every imported module is free of holes.

The argument is uniform for the empty open immersion, identity open immersions, arbitrary
pullback maps and the zero module. It uses the full-faithfulness and essential-image
criterion rather than choosing noncanonical witnesses of a mere existence statement.
The derived argument applies to unbounded complexes and every integer shift.

Validation: the assigned proof compiled cleanly in 20.9 seconds before moving its
construction equation to the operations API. The operations API and both direct
consumers then compiled cleanly in 7.9, 29.3 and 25.7 seconds respectively.
The final packet and the delivery checks verify the moved-equation version.

## No longer needed

Removed direct imports (some remain transitively available through the required interfaces):

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.CategoryTheory.Monoidal.Mod`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates`
- `Sheaf.CategoryTheory.ExactDerivedComposition`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.Paper.CartesianCoefficients`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`
- `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`

Made `Mathlib.CategoryTheory.Localization.Predicate` private because only the proof uses it.
The additional private imports are the termwise shift-compatibility API, the proved profinite-point
square coherence API, module extension-by-zero essential-image API, and the existing
ordinary abelian-sheaf open-base-change theorem.

The following former direct proof dependencies are no longer used by this proof route:

- `def-sfb-finite-upper-star-comp`
- `def-sfb-modobj-extend-restrict-adjunction`
- `def-sfb-modobj-linearization-transport-adjunction`
- `def-sfb-modobj-restriction`
- `def-sfb-modobj-restriction-equivalence`
- `def-sfb-modobj-transport`
- `def-sfb-module-lower-star-comp`
- `def-sfb-module-upper-lower-adjunction`
- `def-sfb-projection-formula-comap`
- `def-weil-pbc-composite-adjunction`
- `lem-sf-ring-sheaf-base-change-mates`
- `lem-sfb-eta-comp`
- `lem-sfb-exact-derived-composition`
- `lem-sfb-exact-derived-natural-iso`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `lem-weil-pbc-qcqs-over-affine`
- `lem-weil-pbc-reduced-induced-closed-subscheme`
- `sk-prop-sfb-cartesian-coefficients`

These are removed from `proof_deps` and from the obsolete `tool_uses` approvals where
present. The existing statement dependencies are retained. Definitions of scalar extension,
restriction and module adjunctions still use their existing internal dependencies: no adopted
source declaration is removed, weakened, or replaced by a hole. No module is withdrawn.
No claim is made here that these modules leave the whole targets' import closure.

Change records: `coord/changes/U9-condensed-open-square-proof-imports.md` and
`coord/changes/U9-square-comparison-definition-boundary.md`.


## Where the brief, the DAG or earlier work was wrong

The nine-step scalar-transport plan is longer than necessary. The specified adjunction
and open essential-image criterion construct the normalized module comparison directly.
A complementary closed immersion, qcqs reduction and scalar transport of the arbitrary-ring
mate are unnecessary. Exactness is already available for pullbacks of every commutative
condensed ring, so admissibility and finite type assumptions need no additional proof.
The theorem retains all its original hypotheses.

The generic exact localization API and its fully faithful whiskering functor give both
the comparison and its precise normalization directly. No new node is needed. The proved public construction equation belongs to the existing
operations definition node. The proof uses the existing proved profinite-point square-coherence theorem
instead of rebuilding its coefficient compositor calculation. The assigned node's proof
fields are updated to describe this shorter route;
its statement, statement dependencies and enclosing unit route are retained.
The operations node records the equality-determined construction and its public equation.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
