## What changed

Proved `AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImageMap_isIso` in
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`. Private, fully proved
helpers identify ordinary module sheaves with modules over the associated constant ring
sheaf, intertwine restriction and direct image, and transport the existing ringed-module
resolution theorem. The derived-mate factorization then proves invertibility on K-injective
representatives and hence on all derived objects. The existing K-injective normalization
equation is retained. Generic private invertibility and unit-cancellation lemmas perform
mate transport before specialization, avoiding expensive unfolding of concrete sheaf functors.
Its quasi-isomorphism conjunct reuses the preceding resolution lemma.
Every existing public declaration, definition body and hypothesis is unchanged.

Added proof-only imports of `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` (including its
private generic realization lemma) and `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
Updated the node proof and proof dependencies to record the scalar-model transport.
No new statement with a postponed proof is introduced.
The imported `pbcRestriction_isRightAdjoint` instance is disabled during proof elaboration
and restored at the end, leaving the consumer interface unchanged.
Local proof transparency is recorded in
`coord/changes/T5-fixed-scalar-proof-transparency.md`; no consumer adaptation is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImageMap_isIso`
(node `lem-weil-proetale-direct-image-restriction-of-scalars`).
Added 0 holes. No `sorry` remains in any delivered Lean file.
The already proved `AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImage_kInjective`
now uses the completed invertibility proof. This is a proof, not a decomposition.
Existing dependencies retain their own independent proof status.

## No longer needed

The standalone `lem-weil-pbc-exact-functor-derived-functor` and its module
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor` are not needed by this argument:
restriction is already descended termwise, and the derived-mate factorization supplies the
required comparison with the ordinary right-derived units. Removed this node from
`proof_deps` and its obsolete top-level `tool_uses` entry. The ringed-topos composition
resolution clause remains needed through the existing ringed-module helper.
No existing imports are removed: the public imports retain the module's existing re-export
interface, and the proof-only imports are used. No unit statement or unit proof step is
bypassed. No entire module is withdrawn or claimed to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The prior node's final step still described global invertibility as open. It is now proved
using the existing resolution clause, without assuming scalar restriction preserves
K-injectives. The retained interrupted attempt had a complete candidate argument but its
scalar realization proof forced large implicit conversions through module sheafification.
A generic sheafification-unit lemma and an explicit underlying-presheaf equality avoid
those conversions. Generic mate transport and temporary removal of the unrelated
derived-adjoint instance avoid repeated concrete functor unfolding. The complete candidate
compiled in 51.5 seconds with a typed quotient identity rewrite before delivery validation.
No mathematical statement or definition repair was necessary. There was no prior landed T5 delivery to reuse.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
