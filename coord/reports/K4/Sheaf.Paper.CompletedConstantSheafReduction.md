## What changed

Proved three infrastructure theorems in Sheaf.Paper.CompletedConstantSheafReduction:
base_exists uses a compatible quotient cone and the limit universal property;
constant_additive uses the underlying additive sheafification functor and its faithful
forgetful functor; systemComparison_naturality constructs a natural transformation
using consecutive quotient maps. Added the proof-only import
Mathlib.CategoryTheory.Sites.Abelian for additive sheafification. All existing signatures,
definitions and visibility are unchanged.

The three proofs compiled together without warnings through lcompile.py. Further tensor
Hom-equivalence experiments were not retained: subsequent server calls repeatedly failed
to obtain a response, interspersed with diagnostics for the experimental code. The final
file restores exactly the previously compiling three-proof version.

## Proved and sorry left

Closed 3 of the original 7 holes, with no holes added:
AlgebraicGeometry.Scheme.CompletedConstantReduction.base_exists;
AlgebraicGeometry.Scheme.CompletedConstantReduction.constant_additive;
AlgebraicGeometry.Scheme.CompletedConstantReduction.systemComparison_naturality.

Four original holes remain unchanged, all attached to
lem-weil-pbc-completed-constant-sheaf-reduction:
AlgebraicGeometry.Scheme.CompletedConstantReduction.reduction_exists;
AlgebraicGeometry.Scheme.CompletedConstantReduction.completed_constant_sheaf_reduction;
AlgebraicGeometry.Scheme.CompletedConstantReduction.finiteReduction_exists;
AlgebraicGeometry.Scheme.CompletedConstantReduction.finite_coefficient_identification.

The reduction existence results still require sheafification of the balanced
projection-multiplication map and uniqueness on constant tensor generators. The main
reduction theorem still requires sectionwise flatness, comparison with module
sheafification, the ordinary quotient identification, and preservation of resolutions.
Finite identification additionally requires the locally constant function comparison
and transport of the canonical tensor reductions. No decomposition is claimed.

## No longer needed

None. The retained imports support the original statements or the four unchanged proof
obligations. No DAG dependency is pruned: these three infrastructure proofs implement
parts of the existing route, and the principal mathematical proof remains unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error identified. Remote compilation became intermittently unavailable:
lcompile.py reported no answer from the compile server on repeated requests. No launcher
script, shared source or compilation limit was changed. No new nodes were introduced.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
