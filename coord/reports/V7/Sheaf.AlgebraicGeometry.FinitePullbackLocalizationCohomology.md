## What changed

Completed AlgebraicGeometry.Scheme.finite_pullback_localization_cohomology with its
original signature and all normalization fields unchanged. Constructed module
restriction as a left adjoint to the specified constant-module direct image, using
its constant-section-normalized ring isomorphism. Uniqueness of left adjoints gives
the module comparison. The adjunction Hom-equivalence counit formula identifies its
inverse with the specified module unit restricted along the distinguished graph.

Three fully proved private helpers establish the constant-section coefficient map
and the scalar compatibility equations for that site adjunction. They are the local
versions of existing private calculations in ProEtaleObjectInverseImageRestriction;
no public interface there is changed. Exactness and additivity transfer from the
published sfIntrinsicPullback along the comparison. The existing
mapDerivedCategoryNatIso_fac proves the comparison on every complex. The canonical
mapDerivedCategoryHomologyFunctorIso supplies cohomology, and naturality applies
directly to arbitrary derived arrows, including roofs.

Updated the item's DAG proof and proof dependencies to this argument. Removed unused
imports as recorded below. Import-interface change record:
coord/changes/V7-finite-localization-imports.md. There are zero current Lean importers
or external textual declaration users, so no consumer adaptation is required.

## Proved and sorry left

Closed one original hole:
AlgebraicGeometry.Scheme.finite_pullback_localization_cohomology
(node lem-pur-finite-pullback-localization-cohomology).

The final module compiled without errors or warnings through lcompile.py in 23.2 s.
The first delivery attempt received no answer from the busy compile server within
210 s and pushed nothing; the unchanged proof is being resubmitted.

No sorry remains in the item's module. No holes or new modules were added. The three
private helpers coefficientDirect_unit, coefficient_restriction_counit and
coefficient_restriction_unit are proved. This is a proof from the published library
interfaces, with no split-off statements.

## No longer needed

Removed public imports Sheaf.Paper.DerivedPullbackTensorHom,
Sheaf.Paper.IntrinsicFiniteTorsionConstructibility,
Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations, and
Sheaf.CategoryTheory.LocalizedModuleExactForSystems. Removed proof imports
Sheaf.CategoryTheory.ExactFunctorDerivedFunctor,
Mathlib.CategoryTheory.Localization.Predicate, and
Mathlib.Algebra.Homology.ShortComplex.PreservesHomology. Kept the needed
ProEtaleObjectInverseImageRestriction and homology imports; imported the coefficient
construction publicly and its finiteness theorem privately.

The proof does not need lem-pur-site-restriction-module-adjunction-exact or its module
LocalizedModuleExactForSystems: transfer exactness from sfIntrinsicPullback instead.
It does not need lem-weil-pbc-exact-functor-derived-functor or ExactFunctorDerivedFunctor:
sfIntrinsicDerivedPullback is definitionally the exact induced functor, so no Kan
uniqueness argument is necessary. It does not use def-weil-derived-pullback-tensor-hom
or DerivedPullbackTensorHom: the finite intrinsic functor is already published by the
ordinary operations module. These three dependencies were removed from proof_deps.
The direct call to lem-weil-proetale-weakly-etale-localization is also unnecessary:
the needed constant-section ring isomorphism is already provided by
proEtaleObjectInverseImageRestriction; its module still imports
ProEtaleWeaklyEtaleLocalization. Removed obsolete tool_uses entries for that direct
call, localized restriction exactness, and exact-derived-functor uniqueness, retaining
the graph comparison approval. Statement dependencies remain unchanged.

The remaining exact-derived-natural-iso, factorization, complex homology and
localization tools are used through their existing canonical implementations in
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor. No declaration
or file in the adopted source tree is changed or removed. Listed modules may still
be needed elsewhere; this is pruning of this item's proof route only.

## Where the brief, the DAG or earlier work was wrong

The original plan required additional exactness transport through the abstract slice
and a separate comparison with the exact derived functor. The concrete intrinsic
pullback already has all three exactness instances, and its derived functor is an
abbreviation for mapDerivedCategory. Thus these extra arguments are unnecessary.
The prior module-level inverse-image theorem supplies a natural module comparison,
but its statement does not expose the required intrinsic-unit graph formula. The
proof constructs the normalized comparison directly using the already specified
adjunction and verifies the formula by transposition.

No mathematical statement, target, definition, chapter route or unit realization was
changed. Empty objects, non-monomorphic site objects, level one, negative degrees and
unbounded complexes impose no extra condition: the proof uses only the site
adjunction, finite coefficients and exact functors.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
