## What changed

Proved `WeilConjectures.integral_ctf_isTriangulated` in
`Sheaf.Paper.IntegralCtfTriangulated`, from the existing integral constructibility
triangulation theorem, exactness of integral derived reduction, and the quantitative
shift and extension clauses of `AlgebraicGeometry.Scheme.finite_ctf_isTriangulated`.
The uniform Tor predicate is shown isomorphism-closed, zero-containing, shift-stable,
and extension-closed, then intersected with integral bounded constructibility using
Mathlib's instances. Two proved private helpers transport a Tor interval across
isomorphisms and enlarge its endpoints directly from the definition.

For zero, finite-stage triangulation gives a finite interval for each reduced zero
object. At a test degree i, shifting by b-i+1 makes the upper endpoint i-1; the shifted
zero is isomorphic to the original zero. Hence every tensor test vanishes in every
degree, and [0,0] works at every level. This uses only the public finite-stage API,
without a new tensor construction or any additional hole. For shifts the common
interval is [a-m,b-m]. For extensions it is [min(a,c),max(b,e)].

Added the private proof import `Sheaf.Paper.IntegralDerivedReduction`; removed the
unused private imports listed below. Both public imports, the definition of
`integralCtfProperty`, universes, and hypotheses are preserved. Preserved the theorem signature verbatim, including its existing implicit-use lambda
binder. A theorem-local unused-variable linter option suppresses that binder's
warning; the Limits namespace opening and canonical zero-object instance are local
to the proof body. Updated the existing node's
proof, proof dependencies, and proof origin to describe the argument, and refreshed
the theorem docstring.

Validation: remote single-file compilation via lcompile.py succeeds without warnings.
Read Stacks sites-cohomology.tex, definition-tor-amplitude (08FZ) and
lemma-cone-tor-amplitude (08G2), the current blueprint's finite-Tor definition, the
unit record and current unit source, and the actual signatures of the dependencies.
Searches: LeanFinder returned generic derived t-structure bounds, Loogle found no
named triangulated-property match, and grep found Mathlib's inverse-image closure.
The inverse-image result alone does not express a common interval at all levels.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.integral_ctf_isTriangulated`
(node `lem-weil-integral-ctf-triangulated`).

No sorry remains in the item; no holes were added and no statements were split off.
The proof uses the existing
`WeilConjectures.boundedConstructibleDerivedCompleteIntegral_isTriangulated`, whose
own proof remains a pre-existing sorry in its original module. That is an existing
mathematical dependency, not a new hole or a claim of axiom-free target completion.
The two private Tor helpers are fully proved. No definition or public interface
was changed, and no consumer adaptations are necessary.

## No longer needed

Removed these nine unused direct private imports:

- `Mathlib.CategoryTheory.Triangulated.Subcategory` (already publicly re-exported).
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients` (use the exact
  reduction API; its general construction is already a transitive dependency).
- `Sheaf.Algebra.Homology.DerivedTensor` (already publicly re-exported by Tor amplitude).
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` (no separate cochain model needed).
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` (the original predicate suffices).
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` (use integralDerivedReduction).
- `Sheaf.Paper.SfIntegralConstructible` (the given property uses the legacy predicate).
- `Sheaf.Paper.SfIntegralConstructibleTriangulated` (use the exact legacy closure statement).
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`
  (no fixed-ring sheaf tensor presentation needed).

Removed `def-weil-derived-tensor` as a direct proof dependency of this node: the zero
case follows from finite-stage zero and shift closure, while the Tor predicate and
finite-stage theorem retain their own tensor dependencies. No upstream declaration
or module was withdrawn. Other declared proof dependencies remain; the unit route
is preserved (this node realizes no unit statement or step).

## Where the brief, the DAG or earlier work was wrong

The finite-stage quantitative shift and extension clauses do not require a
constructibility hypothesis, so steps 3 and 5 need no separate construction of such
premises. Step 2's separate zero-tensor calculation is unnecessary: finite-stage
triangulation and its shift bounds already imply vanishing in every degree for zero.
Several current DAG attachments point to later universe-independent interfaces;
the original same-universe declarations used by the assigned statement are still
available and have the exact needed signatures. No mathematical statement was
weakened or disputed, and no new node was necessary.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
