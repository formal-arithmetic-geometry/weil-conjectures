## What changed

Filled the three proof holes in `Sheaf.AlgebraicGeometry.KummerModuleCoefficients`.
Insertion naturality follows by evaluating naturality of the sheafification unit on
the pure tensor and using the defining equation for tensor restrictions. For roots of unity, the
kernel condition implies multiplication by `m` on the sheaf is zero. For twisted
coefficients, the same equality follows sectionwise from the module action and
`ZMod.natCast_self`. In both cases, additivity of sheaf cohomology carries this
equality to cohomology. All signatures, constructions and public imports are
preserved.

## Proved and sorry left

Closed 3 of the original 3 holes, all attached to
`def-pur-kummer-module-coefficients`:

- `AlgebraicGeometry.Scheme.kummerCoefficientInsertion_naturality`.
- `AlgebraicGeometry.Scheme.kummerRootCohomology_annihilated`.
- `AlgebraicGeometry.Scheme.kummerModuleCohomology_annihilated`.

Zero holes remain in the delivered module; zero holes added or split off.
The existing dependencies are reused without introducing new statements.

## No longer needed

None. No imports, nodes or modules are removed. The node had no planned proof
dependencies, and the proofs implement its existing docstring arguments directly.
The current public import of
`WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence` is preserved;
the retained sandbox used its former `Sheaf` path before the upstream migration.

## Where the brief, the DAG or earlier work was wrong

The retained attempt already filled all three proof holes and supplied a report.
The earlier naturality proof had failed to infer the lifted residue-ring module structure on the underlying
roots-of-unity sections. The tensor calculation now explicitly uses the objects
and restriction map of `kummerRootModulePresheaf`, which carry that structure.
The repaired module compiled without warnings through `lcompile.py` (21.8 seconds).
The current node is a definition node with empty proof steps; its three named
proof obligations already describe the elementary naturality and annihilation
arguments in their docstrings. No new node, statement repair or route change is
needed. The proofs work uniformly for `m = 0` and `m = 1`, with arbitrary degree
and arbitrary coefficient module, without invertibility or geometric hypotheses.

Resumed validation on 2026-10-19: the required `deliver3.py --no-push` passed
compilation, the axiom probe and preflight, with review class `AUTO` (dry-run
commit `a4b1811467`). The earlier compile-service failures have cleared.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
