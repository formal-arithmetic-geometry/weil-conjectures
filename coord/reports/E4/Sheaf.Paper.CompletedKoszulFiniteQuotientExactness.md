## What changed

Proved `AlgebraicGeometry.Scheme.completedKoszulFiniteQuotientExactness` with
its original statement and universes. Only the item module and its own DAG
proof record change.

The proof pulls the ideal back to `ULift A`, identifies its quotient rings with
`ULift (A/I^(n+1))`, and sheafifies the resulting coefficient comparisons.
All comparison maps are normalized on constant sections. Their consecutive
transition equations give an isomorphism of the actual quotient diagrams.
Forgetting commutativity preserves their limits, so the limit isomorphism lifts
to the concrete completed commutative ring. Its projection equations show that
it respects the existing `completedAdicScalar` map.

The existing `completed_constant_algebra_flat_quotients` theorem now supplies
exactness of scalar extension. The existing commutative constant module functor
is definitionally the Koszul constant functor; its exactness and additivity
combine with scalar extension to prove the result. All added comparison helpers
are private and completely proved. No shared interface or definition changes.

Replaced the proof import of `SiteDerivedConstantModuleFunctor` by its
commutative-coefficient counterpart. Added proof imports of
`CompletedConstantSheafReduction` (including its proved private finite constant
comparison) and `CompletedConstantAlgebraFlatQuotients`. The existing public
import is preserved. No derived quotient computation is needed for this proof.

Validation: the complete proof compiled cleanly through `lcompile.py` in 18.2
seconds, below the 60-second limit. The delivery command performs the final
compile and declaration probes.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.completedKoszulFiniteQuotientExactness`
(node `new-s3-completed-koszul-finite-quotient-exactness`).

Zero holes added and zero `sorry` left in the delivered module. No split-off
statement or new axiom is introduced. Existing obligations in imported modules
remain with their owners; this report does not claim their transitive closure
is axiom-free.

## No longer needed

Removed the direct proof import
`Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor`; the commutative
presentation supplies the exact functor with the correct coefficient ring.
The old module remains a transitive import of that presentation.

The proof does not use the reconstruction models of
`def-weil-pbc-koszul-reconstruction-models` as a proof dependency, nor the finite
quotient complex comparison, exterior algebra, Koszul cones, or any choice of
finite-projective resolution. The first node remains in the statement
dependencies unchanged. The completed constant sheaf reduction dependency is
retained for its finite coefficient sheafification comparisons. No existing
module or declaration is withdrawn; no whole module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The old proof step described constructing a finite quotient comparison, while
the assigned theorem asserts exactness. The proof now records the actual
argument: normalize the concrete completion against the existing constant
completion, apply the Noetherian flat-completion theorem, and compose exact
functors. This closes the obligation without a further decomposition.

The exact constant realization theorem is used as a generic proved tool from
`def-sfb-site-derived-constant-module-functor`; no step of the proper-base-change
unit route is bypassed. The assigned theorem and all definitions retain their
meaning, including zero rings, the zero and unit ideals, and empty site objects.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
