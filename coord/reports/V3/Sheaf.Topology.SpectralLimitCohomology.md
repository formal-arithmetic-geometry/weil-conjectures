## What changed

`TopCat.Sheaf.spectralLimit_cohomology` constructs the stage-cohomology functor and canonical cocone explicitly. Their fields come from the normalized-map laws. Its comparison is bijective: represent a colimit element at a stage and use eventual vanishing for injectivity; represent a limit class at a stage for surjectivity. The combination uses Mathlib's `Concrete.colimit_exists_rep`, coprojection relations and the criterion that a bijective morphism of abelian groups is an isomorphism.

The canonical definition `TopCat.Sheaf.spectralLimitCohomologyMap` moved verbatim to `Sheaf.Topology.SpectralLimitCohomologyMap`, publicly re-exported by the original module. This avoids cycles between the three subargument modules and their parent. Its expression and the original theorem's full signature were checked unchanged. The original downstream modules `Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit`, `Sheaf.AlgebraicGeometry.TopDegreeOpenRestrictionSurjective` and `Sheaf.AlgebraicGeometry.TopCoherentCohomologyFinite` compiled unchanged against the relocation overlay.

The canonical-map evaluation formula is proved in `Sheaf.Topology.SpectralLimitCohomologyDegreeZero`. The sectionwise identity, composition and cocone argument is also proved, as `TopCat.Sheaf.spectralLimit_section_laws`: arbitrary abelian groups equipped with injective evaluations inherit these laws from the specified section formulas. The maps are parameters of the proposition `CohomologyMapLaws`, whose three fields record the equations. This interface keeps the sectionwise argument independent of concrete Ext constructions. Local irreducibility attributes in the evaluation proofs control elaboration and change no exported definition.

The three remaining subargument modules carry the source's compatible-injective, exact-quotient, finite compact-open Čech and dimension-shifting route. Class generation omits transition cohomology families: its conclusion uses only projection pullbacks. Change record: `coord/changes/spectral-limit-cohomology-map-relocation.md`.

## Proved and sorry left

Closed the original hole of `TopCat.Sheaf.spectralLimit_cohomology`, node `lem-weil-pbc-spectral-limit-cohomology`, with no local or anonymous holes. Added three named holes, one public theorem per module:

- `TopCat.Sheaf.spectralLimit_cohomology_laws`, node `lem-weil-pbc-spectral-limit-cohomology-laws`: identity, composition and cocone equations for the specified normalized maps in every degree. The degree-zero evaluation formula and the abstract sectionwise transfer argument are proved. Their instantiation at concrete cohomology groups, adjunction comparisons and normalized-pullback uniqueness/composition remain in this obligation. It needs no spectral or inverse-limit assumption.
- `TopCat.Sheaf.spectralLimit_cohomology_class_lift`, node `lem-weil-pbc-spectral-limit-cohomology-class-lift`: every limit class is a canonical image of a stage class. It needs compatible injective products, exact quotient systems, positive acyclicity of their limit from descended finite Čech covers and induction on degree. This is the generation half only.
- `TopCat.Sheaf.spectralLimit_cohomology_eventual_zero`, node `lem-weil-pbc-spectral-limit-cohomology-eventual-zero`: a stage class with zero limit image becomes zero at a later stage. It needs the same replacement, lower-degree generation and the elementwise long-exact-sequence argument in its docstring. This is the relation half only.

Also proved, with no added holes: `TopCat.Sheaf.spectralLimitCohomologyMap_eval₀` and `TopCat.Sheaf.spectralLimit_section_laws`. The evaluation formula uses terminal-open normalization in degree zero for every coefficient sheaf, as supplied by the original `IsPullback` hypotheses. The sectionwise transfer lemma assumes injective evaluations and their specified section formulas; it does not assume a cohomology comparison isomorphism.

Local declaration counts: one original hole closed, three holes added, three delivery holes left. This is a decomposition, not a complete proof of cohomological continuity. The proof combining the three conclusions is complete Lean. Neither definition contains a hole or chooses unspecified data from an unproved existence theorem.

## No longer needed

The main proof no longer directly imports these planned modules; their relevant declarations remain proof dependencies of the new class subarguments:

- `WeilConjectures.Topology.Sheaves.Cech`
- `WeilConjectures.Topology.Sheaves.PushforwardCohomology`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `WeilConjectures.CategoryTheory.SiteCechVanishingCriterion`
- `Sheaf.Topology.SpectralDirectedLimit`
- `Sheaf.Topology.SpectralLimitDescendOpens`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.Topology.SpectralLimitSheafSections`

The obsolete alias imports `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`, `Sheaf.CategoryTheory.SiteCechVanishingCriterion` and `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor` were removed. The direct import `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor` is also removed: the laws node uses the normalized-pullback uniqueness and composition declarations, whose proofs implement the needed dimension shifting. Thus `lem-weil-pbc-right-derived-universal-delta-functor` is no longer a direct dependency of this argument. It remains reachable elsewhere.

A trial import `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` was unnecessary and removed. The transposed-arrow evaluation corollary `TopCat.Sheaf.spectralLimitCohomologyMap_eval₀_adj` is unnecessary as a separate declaration: the laws plan uses Mathlib’s adjunction unit equation directly. The abstract sectionwise module needs neither the canonical-map definition nor the evaluation-formula module, and imports only its Mathlib sheaf and group support. Redundant direct imports of `Mathlib.Topology.Sheaves.Functors` and `WeilConjectures.CategoryTheory.SiteCohomologyPullbackData` were removed from the laws module; its public dependencies already provide them.

No whole source-proof branch is claimed pruned: compact-open and injective arguments remain in the class nodes. None of the unit's realized statements or proof steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original target signature and canonical-map expression are unchanged. The existing declarations supply the separate ingredients but do not directly construct the entire compatible-injective replacement over the varying spaces. That construction, acyclicity argument and induction are recorded explicitly in the two class nodes and their docstrings.

Searches found fixed-space continuity and concrete colimit representative lemmas, but no direct varying-space comparison. The finite-cover colimit-site injective-system declaration requires another site presentation; this delivery retains the full-open-site argument. The laws obligation records the concrete cohomology instantiation and positive-degree transport glue still needed after the proved evaluation and sectionwise arguments.

Edge cases checked before stating the subarguments: empty spaces and zero sheaves, degree zero, singleton indices, constant identity systems, and directed preorders with equivalent distinct indices. Nonemptiness supplies an index even for the zero class. None requires an extra hypothesis on the original theorem.

## New nodes

`def-weil-pbc-spectral-limit-cohomology-map` records the relocated, unchanged canonical map. Its old attachment is removed from the parent theorem node.

`def-weil-pbc-spectral-limit-cohomology-laws` records the proposition with identity, composition and cocone fields. It shares the specified maps as parameters and asserts no colimit property.

`lem-weil-pbc-spectral-limit-cohomology-degree-zero` records the proved evaluation formula, using evaluation naturality and the adjunction hom-equivalence.

`lem-weil-pbc-spectral-limit-cohomology-zero-laws` records the proved transfer of sectionwise laws through injective evaluations of arbitrary abelian groups. The proof explicitly transports equal inverse-image opens and cancels the colimit presentation isomorphisms.

`lem-weil-pbc-spectral-limit-cohomology-laws` isolates the remaining canonical-map equations in all degrees, using the preceding proved APIs and normalized-pullback uniqueness/composition. It contains neither a comparison isomorphism nor either class criterion.

`lem-weil-pbc-spectral-limit-cohomology-class-lift` isolates generation, with no eventual-equality assertion. Its complete construction, acyclicity argument and induction are recorded in its node and docstring.

`lem-weil-pbc-spectral-limit-cohomology-eventual-zero` isolates eventual detection of zero, with no surjectivity assertion. It uses lower-degree generation and quotient-system induction.

All seven new nodes record real three-kind Mathlib searches, the imported-blueprint ancestor and via chain, matching Lean signatures, sources and proof steps. The parent node now describes the actual construction and colimit-representative argument. Change record: `coord/changes/spectral-limit-cohomology-map-relocation.md`.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
