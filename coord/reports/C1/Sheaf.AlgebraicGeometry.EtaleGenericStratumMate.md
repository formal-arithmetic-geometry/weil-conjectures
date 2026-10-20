## What changed

Replaced `AlgebraicGeometry.Etale.immersionInternalHomIso`'s hole by the
parametrized-adjunction mate of the canonical immersion projection isomorphism.
The symmetry transports the existing tensor-Hom adjunction to right-ordered tensor;
composition with the specified ordinary and exceptional adjunctions constructs the
natural isomorphism in both variables. Its counit identity gives exactly the stated
evaluation formula. All hypotheses, conclusions, functors and maps are unchanged.
The category abbreviation
is expanded definitionally in concrete signatures to avoid expensive instance conversion;
the change record records the old and new text.

Added proved private categorical helpers and the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Parametrized`. Retained the existing
proof-only import `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
The final item compiled cleanly through lcompile.py in 8.1 seconds. The appended
axiom probe exposed inconsistent asynchronous elaboration cost; elaborating the
concrete theorem synchronously also passes that probe (12.1 seconds). No checking
is disabled and neither the time nor heartbeat limit is raised. Explicit
projection invertibility and inference of the pullback functor from its canonical
adjunction avoid expensive instance conversion. Restoring the category abbreviations
still exceeds 60 seconds, so the recorded definitional expansion remains.
The two original
consumer files, `EtaleGenericEvaluationCoherence` and `EtaleGenericExchangeAlgClosed`,
each exceed 60 seconds both against the shared baseline and against this compiled
module. Neither reports a type error before timing out, and neither is adapted here.
`#print axioms immersionInternalHomIso` lists the standard three axioms and `sorryAx`
from existing declared dependencies (in particular the projection formula); this
module adds no hole or axiom.
An earlier delivery dry run passed (commit d68c417db4, CODEX review class); its
push attempt timed out during recompilation before pushing. The revised proof is
being revalidated and delivered.
Change record: `coord/changes/etale-generic-stratum-mate-category-presentation.md`.

## Proved and sorry left

The proof closes the single original hole,
`AlgebraicGeometry.Etale.immersionInternalHomIso`
(node `lem-sf-etale-generic-stratum-mate`). There are zero textual `sorry`s in the
item module and no new holes or split-off modules. Holes closed: 1; added: 0; left: 0.
The projection formula is used as an existing declared dependency; its own proof
is outside this delivery.

## No longer needed

The proof uses the existing canonical etale derived adjunctions and closed derived
tensor API directly, so it does not reconstruct them from K-injective resolutions.
Removed proof-only imports:

- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

The corresponding explicit reconstruction is unnecessary here:
`lem-sf-ringed-derived-closed-symmetric-monoidal`,
`lem-weil-pbc-kinjective-total-derived`, `lem-weil-pbc-termwise-adjunction-homotopy`,
`lem-weil-pbc-kinjective-hom-derived`, `lem-weil-pbc-right-adjoint-preserves-kinjective`,
and `prop-weil-pbc-kinjective-resolutions-exist`.
The closed-ambient adjoint and inverse-image exactness remain needed through existing
canonical interfaces exported by the public projection module. No module is withdrawn,
and no claim is made that another consumer cannot need a removed dependency.

## Where the brief, the DAG or earlier work was wrong

The retained attempt had not been typechecked successfully. Abbreviation-mediated
conversion and implicit projection-invertibility synthesis unfolded large derived
localization instances. Explicit category expressions, the explicit invertibility
argument and the concrete adjoint-tensor-map interface avoid that expansion.
The retained attempt used the nonexistent
namespace-qualified `Functor.flipFunctor` (the actual name is
`CategoryTheory.flipFunctor`), and treated curried and product functors as definitionally
equal although their morphism actions differ by functoriality of composition. Explicit
objectwise natural isomorphisms correct this. The proof plan's proposed reconstruction
of derived adjunctions duplicates canonical adjunctions already in the library.

Read Stacks sites-cohomology, Lemmas `lemma-adjoint` (07A6),
`lemma-adjoint-lower-shriek-restrict` (08FJ), and `lemma-internal-hom` (08J9),
and the current blueprint's `lem-weil-stratum-ambient-hom` statement and proof.
The construction works without boundedness assumptions; identity immersions, zero objects,
empty strata, and the zero coefficient ring require no extra argument or excluded case.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
