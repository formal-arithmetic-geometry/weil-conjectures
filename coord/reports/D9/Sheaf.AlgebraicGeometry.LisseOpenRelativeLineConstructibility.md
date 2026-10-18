## What changed

The original public theorem and all its binders are unchanged. Its proof now has three
proved private helpers in the same module:
`finiteLisse_prime_devissage`, `constructibleShriek_prime_devissage`, and
`lisse_shriek_of_affine_opens`. Strong induction on a positive additive annihilator replaces
the primary-idempotent decomposition. Kernels of multiplication by a prime and their
quotients stay finite locally constant; their short-exact triangles give the induction.
A finite-affine-cover induction uses relative Mayer--Vietoris, affine intersections and
constructible cohomology as a triangulated object property to glue the affine cases.
All this takes place in the bounded-below categories, without unfolding total-derived
comparison constructions. The new proof imports are private to this module.

The remaining affine prime-torsion geometric input is isolated in the new module
`Sheaf.AlgebraicGeometry.PrimeLisseAffineCurveShriekConstructibility`. Its public statement
assumes an affine smooth relative curve and a prime killing the sheaf. The parent proves
both the reduction from general finite coefficients to this case and gluing from affine
opens. Thus this is a strict part of the original argument, not a renamed original theorem.
The parent node follows the proof actually written; the new node gives the complete
finite-etale trace/constant-filtration proof plan from Tags 0GKY and 0GKX.

## Proved and sorry left

Original holes closed: the body of
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek`.
Its three private helpers are proved, with no private or nested sorry.

Holes added and still open: exactly one,
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_prime_lisse_affine_curve_shriek`,
node `lem-weil-pbc-prime-lisse-affine-curve-shriek-constructibility`. Its proof is exactly
`by sorry` in its own new module. The item module has zero remaining sorry; the two-module
delivery has one. One old hole closed and one new hole added is a decomposition, with net
zero holes closed, not a complete proof of the original mathematical result.

The remaining theorem needs formal transport to the spectrum of the affine coordinate
ring, the finite-etale filtration theorem with exponent one, a trace retraction using
Bezout, proper finite-direct-image and compactified-shriek composition comparisons, and
finite constant-filtration induction. The existing constant-relative-curve theorem then
treats the graded factors. The last descent is through the disjoint-clopen biproduct and
the trace retract. These are detailed in its docstring and node. In particular the geometric
inputs already stated by the DAG may be used even when their proofs remain sorry.

Validation: server compilation of both modules passed. After qualifying the Limits names
locally, the parent compiled in 49.9 seconds and the residual in 4.2 seconds. The sole
long-line warning in that check was corrected before the final dry run. The first dry run
compiled and reached preflight; it required removal of the added file-level open command.
That command is now identical to the original, with qualified names in the helper proofs.
The final dry run passed compilation without warnings and passed preflight (CODEX review
class: the delivery adds a new node and module). The final pre-push dry-run commit was
`43f065b58a`; delivery reruns the checks against the freshly fetched base.

## No longer needed

The CRT/primary-ring idempotent decomposition is not needed. The parent instead uses
kernel/quotient induction on the additive annihilator. Principal opens are not needed:
a finite affine cover and separated affine intersections suffice.

`lem-weil-pbc-etale-lisse-filtration-devissage` and its missing attached module
`Sheaf.Paper.EtaleLisseFiltrationDevissage` are not needed by this route. The parent uses
short-exact triangles directly; the affine residual's plan describes ordinary finite
induction along a filtration, without this abstract extra theorem. No need to import or
recreate the absent module.

The geometric trace, finite pushforward, constant-curve, shriek-composition and disjoint-open
inputs have moved to the affine residual's proof plan. They remain needed downstream and
are not claimed as globally pruned. No globally unreachable module has been established.

Imports removed from the item module (some remain inputs of the residual plan):

- `import Sheaf.AlgebraicGeometry.FiniteEtaleModuleTraceDegree`
- `import WeilConjectures.SixFunctors.Finite.Exact`
- `import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `import WeilConjectures.Compactification.NagataCompactification`
- `import WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`
- `import Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne`
- `import Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition`
- `import Sheaf.AlgebraicGeometry.LisseFiniteEtaleFiltration`
- `import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`
- `import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `import WeilConjectures.AlgebraicGeometry.FiniteEtaleModuleTraceDegree`
- `import WeilConjectures.AlgebraicGeometry.Curve.DisjointOpenExtensionBiproduct`
- `import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`

Obsolete direct-parent tool approvals removed, preserving the order of those retained:

- `lemma-weil-pbc-finite-direct-image-exact`
- `lem-weil-pbc-finite-proper`
- `lem-weil-pbc-finite-etale-module-trace-degree`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-module-direct-image-left-exact`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `thm-nagata-compactification`
- `lem-weil-pbc-affine-morphism-permanence`
- `lem-pbc-t2-disjoint-open-extension-biproduct`

## Where the brief, the DAG or earlier work was wrong

The filtration theorem gives the degree over algebraically closed fields, whereas the
public trace-degree theorem asks for it over separably closed fields. The earlier node
review calls those hypotheses matching. A bridge is needed: finite etale algebras over
separably closed fields split into field factors, and passage to an algebraic closure
preserves their number. This is true, but it is an additional Lean interface step, not
an immediate application. It is explicitly included in the residual's proof plan.

The generic filtration-devissage node has a Lean attachment, but that attached file is
absent from the shared checkout. No duplicate theorem or replacement file is introduced.
The direct short-exact-triangle approach avoids depending on that attachment.

An attempted total-derived comparison proof was expensive to elaborate. The proved parent
reduction uses Plus-level short-exact triangles and homology functors throughout; this
avoids the total-derived unfolding and compiles below the existing limit. No timeout
limit or launcher file was changed, and no proof was split to evade the compile limit.

Edge cases checked mathematically: characteristic one gives the zero-object induction;
annihilator n=p*m has m<n and both smaller sheaves killed as claimed; an empty finite
affine cover is the empty affine open; intersections remain affine by separatedness;
zero sheaves, empty affine sources, negative cohomological degrees and the prescribed
arbitrary compactification remain covered by the statements. No definition, target
statement, existing signature, visibility or consumer was changed.

## New nodes

`lem-weil-pbc-prime-lisse-affine-curve-shriek-constructibility` is the affine prime-torsion
geometric part of Tag 0GKY, using the constant-coefficient theorem of Tag 0GKX. It has its
own module, complete natural-language proof, source, dependency list, three kinds of
Mathlib search plus local library searches, and Lean attachment. It is strictly smaller
than the original obligation in coefficients and source geometry. No change record is
needed because no existing statement or definition changed.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
