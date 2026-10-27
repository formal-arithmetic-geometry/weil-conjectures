## What changed

Proved `CategoryTheory.FiniteCoverDerivedSections.cofinal_reindexing` with its original
signature. The private, fully proved `quasiIso_colim_map` helper shows preservation of
objectwise quasi-isomorphisms by filtered colimits of abelian-group complexes. It applies
homology, uses the naturality identity `colimit.map_post`, and cancels the invertible
homology-colimit comparison. Mathlib's final-functor instance then inverts the actual
`colimit.pre` factor of `v.sourceMap`. The square is the existing `naturality v`.

Added the private proof import
`WeilConjectures.CategoryTheory.Abelian.HomologyFilteredColimit`. Updated the node's
cofinality step to record this argument. Existing public imports, definitions, theorem
signatures and remaining theorem bodies are unchanged. No shared module was adapted.

Validation: the final minimal-import version compiled remotely in 3.1 seconds with
no errors or warnings. The added proof import passes the import-direction check. The
private helper uses only proved declarations; the cofinal square still depends on the
existing, unfinished `naturality` theorem, as intended by stage 3.

## Proved and sorry left

Closed 1 of 9 existing holes:
`CategoryTheory.FiniteCoverDerivedSections.cofinal_reindexing`.
Added 0 holes; split off 0 statements. This is a partial delivery, not a decomposition.

The following eight existing holes remain, all attached to
`lem-per-finite-cover-derived-sections-continuity`:

- `CategoryTheory.FiniteCoverDerivedSections.exists_coefficient_colimit`
- `CategoryTheory.FiniteCoverDerivedSections.exists_model`
- `CategoryTheory.FiniteCoverDerivedSections.continuity`
- `CategoryTheory.FiniteCoverDerivedSections.naturality`
- `CategoryTheory.FiniteCoverDerivedSections.exists_change_lift`
- `CategoryTheory.FiniteCoverDerivedSections.coefficient_naturality`
- `CategoryTheory.FiniteCoverDerivedSections.common_refinement`
- `CategoryTheory.FiniteCoverDerivedSections.truncation_compatibility`

## No longer needed

Removed these unused private imports from this module:

- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.CategoryTheory.KInjectiveComputes`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.CohomologyColimitSites`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `WeilConjectures.CategoryTheory.ColimitSiteSections`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`
- `WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`

No declaration or module is withdrawn. No DAG dependency is pruned: the remaining
resolution, continuity, naturality and truncation holes still carry their original
proof plans and dependencies. For the proved cofinality clause, only filtered-colimit
exactness, the final-functor colimit theorem and the internal naturality theorem are
used. In particular the cofinality proof needs neither site cohomology continuity
nor the acyclic-resolution comparison.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The cofinality clause can be proved directly in the
category of complexes using the final-functor colimit theorem, rather than passing to
an opposite category. The existing node for exact filtered colimits supplies the
homology argument. The other eight clauses remain open; this packet does not claim
to construct their system resolutions or their compatible homotopies.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
