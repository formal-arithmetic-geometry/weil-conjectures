## What changed

In `Sheaf.Paper.ProjectionFormulaCompactified`, prove
`AlgebraicGeometry.Scheme.ProjectionRestriction.restrictionStrictPerfect_flat`
and `AlgebraicGeometry.Scheme.ProjectionRestriction.restrictionMixedTensor_existsUnique`.
All existing signatures and definitions are unchanged.

The retained finite-power induction includes rank zero. Retracts of finite powers
of the tensor unit are dualizable, hence flat. The site-tensor comparison and the
bounded-above independent-coefficient K-flat theorem give resolving coefficients.

For mixed tensors, choose an epimorphic flat K-flat resolution of the first factor.
Tensoring its augmentation with the K-flat second factor is a quasi-isomorphism,
as proved using the mapping-cone tensor comparison. Compose the inverse of its
derived tensor image, the resolving-model comparison, and the localized ordinary
tensor augmentation. For any other resolution, resolve its pullback with the chosen
epimorphic augmentation. The pullback projection is a quasi-isomorphism: its kernel
is the acyclic kernel of the chosen augmentation, and the homology exact sequence
proves the assertion. Naturality on the two refinement maps and cancellation give
the required square. Applying that square at the chosen augmentation proves
uniqueness. All auxiliary lemmas are private and proved; no object is chosen from
an unproved mere-existence theorem without its determining comparison equations.

Proof imports provide independent-coefficient bounded-flat K-flatness and
resolutions, tensor comparisons, dualizability, flatness of dualizable objects,
tensor mapping cones and pullbacks of short exact sequences. The original
normalization lemma remains marked STATEMENT-DISPUTED with the counterexample below.

## Proved and sorry left

Two of five original holes closed:

- `AlgebraicGeometry.Scheme.ProjectionRestriction.restrictionStrictPerfect_flat`
- `AlgebraicGeometry.Scheme.ProjectionRestriction.restrictionMixedTensor_existsUnique`

No holes added; no split-offs. The complete module compiled without warnings in
18.8 seconds against the current compiled library. This is a proof from existing
declarations, including the independent-coefficient resolution theorem.

Three original holes remain, all attached to
`lemma-weil-pbc-projection-formula-compactified`:

- `AlgebraicGeometry.Scheme.ProjectionRestriction.restrictionProjectionTensor_normalized`
- `AlgebraicGeometry.Scheme.proEtaleProjectionFormula_compactified`
- `AlgebraicGeometry.Scheme.compactifiedProjection_rho_local`

## No longer needed

Removed unused private imports `Sheaf.Paper.ProjectionFormulaTotalization` and
`Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`. The existing derived open
adjunction is constructed directly by localization, not by preDerivedAdjunctionGeneral.
No declared dependency node is pruned: the untouched global proofs still require
the original DAG route, and ProjectionFormulaArrows already reexports the
pre-derived adjunction interface. Public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The older small-site strict-perfect and mixed representative lemmas equate site
object, morphism and coefficient universes, so they cannot be applied directly
at this module's site universes. Existing independent-coefficient K-flatness and
tensor comparison supply the flatness argument without changing any interface.
The first delivery dry run exited with code 137 after waiting for shared fetch
coordination, without Lean or preflight diagnostics. Single-file compilation works and was rechecked in this resumed session (18.8 seconds,
exit code 0). The interrupted resumed dry run no longer had a running process or
a recoverable session result; it was retried with output saved in the sandbox,
using the unmodified launcher tools. No push had been attempted.


STATEMENT-DISPUTED: `restrictionProjectionTensor_normalized` has a missing
unit-preservation condition. Take C to be the empty category and D the category
with one object and only its identity, both with trivial Grothendieck topologies.
Let R be the unique ring sheaf on C and S the constant integer ring on D. The
functor F : C → D is continuous. Its module pushforward lands in the zero category;
its left adjoint is the zero functor. Both functors are additive and exact, and
Mod(S) has K-injective resolutions. Thus these data give an Operation. Its
OrdinaryTensor comparison is the unique isomorphism between zero objects, and
pure_unit is vacuous because it quantifies over C. But the claimed j would be an
isomorphism from the zero module to the integer ring module, which is impossible.
The false part is the unit-isomorphism existence, not the bounded-flat lemma.
No false statement was used in the new proof. Repairing this generic interface
requires an actual unit comparison (or suitable site-map hypotheses such as
finality, with its consequences checked for every consumer), which is left to
the disputed-statement queue. The theorem is marked at its declaration; its
signature is unchanged, and its existing sorry remains.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
